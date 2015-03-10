{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}

-- | This module implements the execution of SQL query bundles and the
-- construction of nested values from the resulting vector bundle.
module Database.DSH.Backend.Sql
  ( SqlBackend
  , sqlBackend
  ) where

import           Text.Printf

import qualified Database.HDBC                            as H
import           Database.HDBC.PostgreSQL

import           Control.Applicative
import           Control.Monad
import           Control.Monad.State
import           Data.Decimal
import qualified Data.Map                                 as M
import           Data.Maybe
import qualified Data.Text                                as Txt
import qualified Data.Text.Encoding                       as Txt

import qualified Database.Algebra.Dag                     as D
import qualified Database.Algebra.Dag.Build               as B
import           Database.Algebra.Dag.Common
import           Database.Algebra.SQL.Compatibility
import           Database.Algebra.SQL.Materialization.CTE
import           Database.Algebra.SQL.Util
import qualified Database.Algebra.Table.Lang              as TA

import           Database.DSH.Backend
import           Database.DSH.Backend.Sql.Opt.OptimizeTA
import           Database.DSH.Backend.Sql.VectorAlgebra   ()
import           Database.DSH.Common.Impossible
import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Vector
import           Database.DSH.VL

--------------------------------------------------------------------------------

newtype SqlBackend = SqlBackend Connection

-- | Construct a PostgreSQL backend based on an HDBC PostgreSQL
-- connection.
sqlBackend :: Connection -> SqlBackend
sqlBackend = SqlBackend

--------------------------------------------------------------------------------

-- | In a query shape, render each root node for the algebraic plan
-- into a separate SQL query.

-- FIXME use materialization "prelude"
-- FIXME use Functor instance
generateSqlQueries :: QueryPlan TA.TableAlgebra NDVec -> Shape (BackendCode SqlBackend)
generateSqlQueries taPlan = renderSql $ queryShape taPlan
  where
    roots = D.rootNodes $ queryDag taPlan
    (_sqlShared, sqlQueries) = renderOutputDSHWith PostgreSQL materialize (queryDag taPlan)
    nodeToQuery  = zip roots sqlQueries
    lookupNode n = maybe $impossible SqlCode $ lookup n nodeToQuery

    renderSql = fmap (\(ADVec r _) -> lookupNode r)

--------------------------------------------------------------------------------

-- | Insert SerializeRel operators in TA.TableAlgebra plans to define
-- descr and order columns as well as the required payload columns.
-- FIXME: once we are a bit more flexible wrt surrogates, determine the
-- surrogate (i.e. descr) columns from information in NDVec.
insertSerialize :: VecBuild TA.TableAlgebra NDVec (Shape NDVec)
                -> VecBuild TA.TableAlgebra NDVec (Shape NDVec)
insertSerialize g = g >>= traverseShape

  where
    traverseShape :: Shape NDVec -> VecBuild TA.TableAlgebra NDVec (Shape NDVec)
    traverseShape (VShape dvec lyt) = do
        mLyt' <- traverseLayout lyt
        case mLyt' of
            Just lyt' -> do
                dvec' <- insertOp dvec noDescr needAbsPos
                return $ VShape dvec' lyt'
            Nothing   -> do
                dvec' <- insertOp dvec noDescr needRelPos
                return $ VShape dvec' lyt

    traverseShape (SShape dvec lyt)     = do
        mLyt' <- traverseLayout lyt
        case mLyt' of
            Just lyt' -> do
                dvec' <- insertOp dvec noDescr needAbsPos
                return $ SShape dvec' lyt'
            Nothing   -> do
                dvec' <- insertOp dvec noDescr noPos
                return $ SShape dvec' lyt

    traverseLayout :: (Layout NDVec) -> VecBuild TA.TableAlgebra NDVec (Maybe (Layout NDVec))
    traverseLayout LCol          = return Nothing
    traverseLayout (LTuple lyts) = do
        mLyts <- mapM traverseLayout lyts
        if all isNothing mLyts
            then return Nothing
            else return $ Just $ LTuple $ zipWith (\l ml -> maybe l id ml) lyts mLyts
    traverseLayout (LNest dvec lyt) = do
        mLyt' <- traverseLayout lyt
        case mLyt' of
            Just lyt' -> do
                dvec' <- insertOp dvec needDescr needAbsPos
                return $ Just $ LNest dvec' lyt'
            Nothing   -> do
                dvec' <- insertOp dvec needDescr needRelPos
                return $ Just $ LNest dvec' lyt


    -- | Insert a Serialize node for the given vector
    insertOp :: NDVec -> Maybe TA.DescrCol -> TA.SerializeOrder -> VecBuild TA.TableAlgebra NDVec NDVec
    insertOp (ADVec q cols) descr pos = do
        let cs = map (TA.PayloadCol . ("item" ++) . show) cols
            op = TA.Serialize (descr, pos, cs)

        qp   <- lift $ B.insert $ UnOp op q
        return $ ADVec qp cols

    needDescr = Just (TA.DescrCol "descr")
    noDescr   = Nothing

    needAbsPos = TA.AbsPos "pos"
    needRelPos = TA.RelPos ["pos"]
    noPos      = TA.NoPos

implementVectorOps :: QueryPlan VL VLDVec -> QueryPlan TA.TableAlgebra NDVec
implementVectorOps vlPlan = mkQueryPlan dag shape tagMap
  where
    taPlan               = vl2Algebra (D.nodeMap $ queryDag vlPlan) (queryShape vlPlan)
    serializedPlan       = insertSerialize taPlan
    (dag, shape, tagMap) = runVecBuild serializedPlan

--------------------------------------------------------------------------------

instance Backend SqlBackend where
    data BackendRow SqlBackend  = SqlRow (M.Map String H.SqlValue)
    data BackendCode SqlBackend = SqlCode String
    data BackendPlan SqlBackend = QP (QueryPlan TA.TableAlgebra NDVec)

    execFlatQuery (SqlBackend conn) (SqlCode q) = do
        stmt  <- H.prepare conn q
        void $ H.execute stmt []
        map SqlRow <$> H.fetchAllRowsMap' stmt

    generateCode :: BackendPlan SqlBackend -> Shape (BackendCode SqlBackend)
    generateCode (QP plan) = generateSqlQueries plan

    generatePlan :: QueryPlan VL VLDVec -> BackendPlan SqlBackend
    generatePlan = QP . implementVectorOps

    dumpPlan :: String -> BackendPlan SqlBackend -> IO ()
    dumpPlan prefix (QP plan) = do
        exportPlan (prefix ++ "_ta") plan
        exportPlan (prefix ++ "_opt_ta") $ optimizeTA plan

    transactionally (SqlBackend conn) ma =
        H.withTransaction conn (\c -> ma (SqlBackend c))

--------------------------------------------------------------------------------

instance Row (BackendRow SqlBackend) where
    data Scalar (BackendRow SqlBackend) = SqlScalar H.SqlValue

    col c (SqlRow r) =
        case M.lookup c r of
            Just v  -> SqlScalar v
            Nothing -> error $ printf "col lookup %s failed in %s" c (show r)

    descrVal (SqlScalar (H.SqlInt32 i))   = fromIntegral i
    descrVal (SqlScalar (H.SqlInteger i)) = fromIntegral i
    descrVal _                            = $impossible

    unitVal (SqlScalar H.SqlNull)        = unitE
    unitVal (SqlScalar (H.SqlInteger _)) = unitE
    unitVal _                            = $impossible

    integerVal (SqlScalar (H.SqlInteger i)) = integerE i
    integerVal (SqlScalar (H.SqlInt32 i))   = integerE $ fromIntegral i
    integerVal (SqlScalar (H.SqlInt64 i))   = integerE $ fromIntegral i
    integerVal (SqlScalar (H.SqlWord32 i))  = integerE $ fromIntegral i
    integerVal (SqlScalar (H.SqlWord64 i))  = integerE $ fromIntegral i
    integerVal _                            = $impossible

    doubleVal (SqlScalar (H.SqlDouble d))   = doubleE d
    doubleVal (SqlScalar (H.SqlRational d)) = doubleE $ fromRational d
    doubleVal (SqlScalar (H.SqlInteger d))  = doubleE $ fromIntegral d
    doubleVal (SqlScalar (H.SqlInt32 d))    = doubleE $ fromIntegral d
    doubleVal (SqlScalar (H.SqlInt64 d))    = doubleE $ fromIntegral d
    doubleVal (SqlScalar (H.SqlWord32 d))   = doubleE $ fromIntegral d
    doubleVal (SqlScalar (H.SqlWord64 d))   = doubleE $ fromIntegral d
    doubleVal _                             = $impossible

    boolVal (SqlScalar (H.SqlBool b))    = boolE b
    boolVal (SqlScalar (H.SqlInteger i)) = boolE (i /= 0)
    boolVal (SqlScalar (H.SqlInt32 i))   = boolE (i /= 0)
    boolVal (SqlScalar (H.SqlInt64 i))   = boolE (i /= 0)
    boolVal (SqlScalar (H.SqlWord32 i))  = boolE (i /= 0)
    boolVal (SqlScalar (H.SqlWord64 i))  = boolE (i /= 0)
    boolVal _                            = $impossible

    charVal (SqlScalar (H.SqlChar c))       = charE c
    charVal (SqlScalar (H.SqlString (c:_))) = charE c
    charVal (SqlScalar (H.SqlByteString c)) = charE (head $ Txt.unpack $ Txt.decodeUtf8 c)
    charVal _                               = $impossible

    textVal (SqlScalar (H.SqlString t))     = textE (Txt.pack t)
    textVal (SqlScalar (H.SqlByteString s)) = textE (Txt.decodeUtf8 s)
    textVal _                               = $impossible

    -- FIXME this is an incredibly crude method to convert HDBC's
    -- rationals to decimals. Implement this reasonably or - even
    -- better - replace HDBC completely. Rationals do not make sense
    -- here.
    decimalVal (SqlScalar (H.SqlRational d)) = decimalE $ realFracToDecimal 5 d
    decimalVal _                             = $impossible

    dayVal (SqlScalar (H.SqlLocalDate d)) = dayE d
    dayVal _                              = $impossible

