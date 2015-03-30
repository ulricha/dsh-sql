{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE ParallelListComp  #-}

-- | This module implements the execution of SQL query bundles and the
-- construction of nested values from the resulting vector bundle.
module Database.DSH.Backend.Sql
  ( SqlBackend
  , sqlBackend
  ) where

import           Text.Printf

import qualified Database.HDBC                            as H
import           Database.HDBC.PostgreSQL

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
import           Database.DSH.Backend.Sql.Vector
import           Database.DSH.Backend.Sql.VectorAlgebra
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
generateSqlQueries :: QueryPlan TA.TableAlgebra TADVec -> Shape (BackendCode SqlBackend)
generateSqlQueries taPlan = renderSql $ queryShape taPlan
  where
    roots = D.rootNodes $ queryDag taPlan
    (_sqlShared, sqlQueries) = renderOutputDSHWith PostgreSQL materialize (queryDag taPlan)
    nodeToQuery  = zip roots sqlQueries
    lookupNode n = maybe $impossible SqlCode $ lookup n nodeToQuery

    renderSql = fmap (\(TADVec r _ _ _ _) -> lookupNode r)

--------------------------------------------------------------------------------

type TAVecBuild a = VecBuild TA.TableAlgebra (DVec TA.TableAlgebra) (PVec TA.TableAlgebra) (RVec TA.TableAlgebra) a 

-- | Insert SerializeRel operators in TA.TableAlgebra plans to define
-- descr and order columns as well as the required payload columns.
-- FIXME: once we are a bit more flexible wrt surrogates, determine the
-- surrogate (i.e. descr) columns from information in NDVec.
insertSerialize :: TAVecBuild (Shape (DVec TA.TableAlgebra))
                -> TAVecBuild (Shape (DVec TA.TableAlgebra))
insertSerialize g = g >>= traverseShape

  where
    traverseShape :: Shape TADVec -> TAVecBuild (Shape TADVec)
    traverseShape (VShape dvec lyt) = do
        mLyt' <- traverseLayout lyt
        case mLyt' of
            Just lyt' -> do
                dvec' <- insertOp dvec noRef needKey needOrd
                return $ VShape dvec' lyt'
            Nothing   -> do
                dvec' <- insertOp dvec noRef noKey needOrd
                return $ VShape dvec' lyt

    traverseShape (SShape dvec lyt)     = do
        mLyt' <- traverseLayout lyt
        case mLyt' of
            Just lyt' -> do
                dvec' <- insertOp dvec noRef needKey noOrd
                return $ SShape dvec' lyt'
            Nothing   -> do
                dvec' <- insertOp dvec noRef noKey noOrd
                return $ SShape dvec' lyt

    traverseLayout :: (Layout TADVec) -> TAVecBuild (Maybe (Layout TADVec))
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
                dvec' <- insertOp dvec needRef needKey needOrd
                return $ Just $ LNest dvec' lyt'
            Nothing   -> do
                dvec' <- insertOp dvec needRef noKey needOrd
                return $ Just $ LNest dvec' lyt

    -- | Insert a Serialize node for the given vector
    insertOp :: TADVec
             -> (VecRef -> [TA.RefCol])
             -> (VecKey -> [TA.KeyCol])
             -> (VecOrder -> [TA.OrdCol])
             -> TAVecBuild TADVec
    insertOp (TADVec q o k r i) mkRef mkKey mkOrd = do
        let op = TA.Serialize (mkRef r, mkKey k, mkOrd o, itemCols i)

        qp   <- lift $ B.insert $ UnOp op q
        return $ TADVec qp o k r i

    needRef :: VecRef -> [TA.RefCol]
    needRef (VecRef 0) = []
    needRef (VecRef i) = [ TA.RefCol $ rc c | c <- [1..i] ]

    noRef :: VecRef -> [TA.RefCol]
    noRef = const []

    needOrd :: VecOrder -> [TA.OrdCol]
    needOrd (VecOrder ds) = [ TA.OrdCol (oc i, d) | i <- [1..] | d <- ds ]

    noOrd :: VecOrder -> [TA.OrdCol]
    noOrd = const []

    needKey :: VecKey -> [TA.KeyCol]
    needKey (VecKey i) = [ TA.KeyCol $ kc c | c <- [1..i] ]

    noKey :: VecKey -> [TA.KeyCol]
    noKey = const []

    itemCols :: VecItems -> [TA.PayloadCol]
    itemCols (VecItems 0) = []
    itemCols (VecItems i) = [ TA.PayloadCol $ ic c | c <- [1..i] ]

implementVectorOps :: QueryPlan VL VLDVec -> QueryPlan TA.TableAlgebra TADVec
implementVectorOps vlPlan = mkQueryPlan dag shape tagMap
  where
    taPlan               = vl2Algebra (D.nodeMap $ queryDag vlPlan) (queryShape vlPlan)
    serializedPlan       = insertSerialize taPlan
    (dag, shape, tagMap) = runVecBuild serializedPlan

--------------------------------------------------------------------------------

instance Backend SqlBackend where
    data BackendRow SqlBackend  = SqlRow (M.Map String H.SqlValue)
    data BackendCode SqlBackend = SqlCode String
    data BackendPlan SqlBackend = QP (QueryPlan TA.TableAlgebra TADVec)

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

