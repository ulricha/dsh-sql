{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE ParallelListComp  #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}

-- | This module implements the execution of SQL query bundles and the
-- construction of nested values from the resulting vector bundle.
module Database.DSH.Backend.Sql
  ( -- * The relational SQL backend
    SqlBackend
  , sqlBackend
  , unwrapCode
    -- * Show and tell: display relational plans.
  , showRelationalQ
  , showRelationalOptQ
  , showSqlQ
  , showTabularQ
  ) where

import           System.Process
import           System.Random
import           Text.Printf

import qualified Database.HDBC                            as H
import           Database.HDBC.ODBC

import           Control.Monad
import           Control.Monad.State
import qualified Data.ByteString.Char8                    as BS
import qualified Data.ByteString.Lex.Fractional           as BD
import qualified Data.ByteString.Lex.Integral             as BI
import           Data.Decimal
import qualified Data.Map                                 as M
import           Data.Maybe
import qualified Data.Text                                as T
import qualified Data.Text.Encoding                       as TE
import qualified Data.Vector                              as V

import qualified Database.Algebra.Dag                     as D
import qualified Database.Algebra.Dag.Build               as B
import           Database.Algebra.Dag.Common
import           Database.Algebra.SQL.Compatibility
import           Database.Algebra.SQL.Materialization.CTE
import           Database.Algebra.SQL.Util
import qualified Database.Algebra.Table.Lang              as TA

import qualified Database.DSH                             as DSH
import           Database.DSH.Backend
import           Database.DSH.Backend.Sql.Opt.OptimizeTA
import           Database.DSH.Backend.Sql.Vector
import           Database.DSH.Backend.Sql.VectorAlgebra
import           Database.DSH.Common.Impossible
import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Vector
import qualified Database.DSH.Compiler                    as C
import           Database.DSH.VL

--------------------------------------------------------------------------------

newtype SqlBackend = SqlBackend Connection

-- | Construct a PostgreSQL backend based on an HDBC PostgreSQL
-- connection.
sqlBackend :: Connection -> SqlBackend
sqlBackend = SqlBackend

newtype SqlCode = SqlCode { unSql :: String }

data SqlVector = SqlVector SqlCode VecOrder VecKey VecRef VecItems

unwrapCode :: BackendCode SqlBackend -> String
unwrapCode (BC (SqlVector (SqlCode q) _ _ _ _)) = q

instance RelationalVector SqlVector where
    rvKeyCols (SqlVector _ _ k _ _) = map kc $ [1..unKey k]
    rvRefCols (SqlVector _ _ _ r _) = map rc $ [1..unRef r]
    rvItemCols (SqlVector _ _ _ _ i) = V.generate (unItems i) (ic . (+ 1))

--------------------------------------------------------------------------------

-- | In a query shape, render each root node for the algebraic plan
-- into a separate SQL query.

-- FIXME use materialization "prelude"
-- FIXME use Functor instance
generateSqlQueries :: QueryPlan TA.TableAlgebra TADVec -> Shape (BackendCode SqlBackend)
generateSqlQueries taPlan = renderSql $ queryShape taPlan
  where
    roots :: [AlgNode]
    roots = D.rootNodes $ queryDag taPlan

    (_sqlShared, sqlQueries) = renderOutputDSHWith PostgreSQL materialize (queryDag taPlan)

    nodeToQuery :: [(AlgNode, SqlCode)]
    nodeToQuery  = zip roots (map SqlCode sqlQueries)

    lookupNode :: AlgNode -> SqlCode
    lookupNode n = maybe $impossible id $ lookup n nodeToQuery

    renderSql = fmap (\(TADVec q o k r i) -> BC $ SqlVector (lookupNode q) o k r i)

--------------------------------------------------------------------------------

type TAVecBuild a = VecBuild TA.TableAlgebra
                             (DVec TA.TableAlgebra)
                             (RVec TA.TableAlgebra)
                             (KVec TA.TableAlgebra)
                             (FVec TA.TableAlgebra)
                             (SVec TA.TableAlgebra)
                             a

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
        let op = TA.Serialize (mkRef r, mkKey k, mkOrd o, needItems i)

        qp   <- lift $ B.insert $ UnOp op q
        return $ TADVec qp o k r i

    needRef :: VecRef -> [TA.RefCol]
    needRef (VecRef 0) = []
    needRef (VecRef i) = [ TA.RefCol (rc c) (TA.ColE $ rc c) | c <- [1..i] ]

    noRef :: VecRef -> [TA.RefCol]
    noRef = const []

    needOrd :: VecOrder -> [TA.OrdCol]
    needOrd (VecOrder ds) = [ TA.OrdCol (oc i, d) (TA.ColE $ oc i)
                            | i <- [1..] | d <- ds
                            ]

    noOrd :: VecOrder -> [TA.OrdCol]
    noOrd = const []

    needKey :: VecKey -> [TA.KeyCol]
    needKey (VecKey i) = [ TA.KeyCol (kc c) (TA.ColE $ kc c) | c <- [1..i] ]

    noKey :: VecKey -> [TA.KeyCol]
    noKey = const []

    needItems :: VecItems -> [TA.PayloadCol]
    needItems (VecItems 0) = []
    needItems (VecItems i) = [ TA.PayloadCol (ic c) (TA.ColE $ ic c) | c <- [1..i] ]

implementVectorOps :: QueryPlan VL VLDVec -> QueryPlan TA.TableAlgebra TADVec
implementVectorOps vlPlan = mkQueryPlan dag shape tagMap
  where
    taPlan               = vl2Algebra (D.nodeMap $ queryDag vlPlan)
                                      (queryShape vlPlan)
    serializedPlan       = insertSerialize taPlan
    (dag, shape, tagMap) = runVecBuild serializedPlan

--------------------------------------------------------------------------------

instance RelationalVector (BackendCode SqlBackend) where
    rvKeyCols (BC v) = rvKeyCols v
    rvItemCols (BC v) = rvItemCols v
    rvRefCols (BC v) = rvRefCols v

instance Backend SqlBackend where
    data BackendRow SqlBackend  = SqlRow (M.Map String H.SqlValue)
    data BackendCode SqlBackend = BC SqlVector
    data BackendPlan SqlBackend = QP (QueryPlan TA.TableAlgebra TADVec)

    execFlatQuery (SqlBackend conn) (BC (SqlVector q _ _ _ _)) = do
        stmt  <- H.prepare conn (unSql q)
        void $ H.execute stmt []
        map SqlRow <$> H.fetchAllRowsMap' stmt

    generateCode :: BackendPlan SqlBackend -> Shape (BackendCode SqlBackend)
    generateCode (QP plan) = generateSqlQueries $ optimizeTA plan

    generatePlan :: QueryPlan VL VLDVec -> BackendPlan SqlBackend
    generatePlan = QP . implementVectorOps

    dumpPlan :: String -> Bool -> BackendPlan SqlBackend -> IO String
    dumpPlan prefix False (QP plan) = do
        let fileName = prefix ++ "_ta"
        exportPlan fileName plan
        return fileName
    dumpPlan prefix True (QP plan) = do
        let fileName = prefix ++ "_opt_ta"
        exportPlan fileName $ optimizeTA plan
        return fileName

    transactionally (SqlBackend conn) ma =
        H.withTransaction conn (\c -> ma (SqlBackend c))

--------------------------------------------------------------------------------

instance Row (BackendRow SqlBackend) where
    data Scalar (BackendRow SqlBackend) = SqlScalar H.SqlValue

    col c (SqlRow r) =
        case M.lookup c r of
            Just v  -> SqlScalar v
            Nothing -> error $ printf "col lookup %s failed in %s" c (show r)

    keyVal :: Scalar (BackendRow SqlBackend) -> KeyVal
    keyVal (SqlScalar v) = case v of
        H.SqlInt32 i -> KInteger $ fromIntegral i
        H.SqlInt64 i -> KInteger $ fromIntegral i
        H.SqlWord32 i -> KInteger $ fromIntegral i
        H.SqlWord64 i -> KInteger $ fromIntegral i
        H.SqlInteger i -> KInteger $ fromIntegral i
        H.SqlString s -> KByteString $ BS.pack s
        H.SqlByteString s -> KByteString s
        H.SqlLocalDate d -> KDay d

        _ -> $impossible


    descrVal (SqlScalar (H.SqlInt32 i))   = fromIntegral i
    descrVal (SqlScalar (H.SqlInteger i)) = fromIntegral i
    descrVal _                            = $impossible

    unitVal (SqlScalar H.SqlNull)        = unitE
    unitVal (SqlScalar (H.SqlInteger _)) = unitE
    unitVal (SqlScalar (H.SqlInt64 _))   = unitE
    unitVal (SqlScalar v)                = error $ printf "unitVal: %s" (show v)

    integerVal (SqlScalar (H.SqlInteger i)) = integerE i
    integerVal (SqlScalar (H.SqlInt32 i))   = integerE $ fromIntegral i
    integerVal (SqlScalar (H.SqlInt64 i))   = integerE $ fromIntegral i
    integerVal (SqlScalar (H.SqlWord32 i))  = integerE $ fromIntegral i
    integerVal (SqlScalar (H.SqlWord64 i))  = integerE $ fromIntegral i
    integerVal _                            = $impossible

    doubleVal (SqlScalar (H.SqlDouble d))     = doubleE d
    doubleVal (SqlScalar (H.SqlRational d))   = doubleE $ fromRational d
    doubleVal (SqlScalar (H.SqlInteger d))    = doubleE $ fromIntegral d
    doubleVal (SqlScalar (H.SqlInt32 d))      = doubleE $ fromIntegral d
    doubleVal (SqlScalar (H.SqlInt64 d))      = doubleE $ fromIntegral d
    doubleVal (SqlScalar (H.SqlWord32 d))     = doubleE $ fromIntegral d
    doubleVal (SqlScalar (H.SqlWord64 d))     = doubleE $ fromIntegral d
    doubleVal (SqlScalar (H.SqlByteString c)) = doubleE $ maybe $impossible fst (BD.readDecimal c)
    doubleVal (SqlScalar v)                   = error $ printf "doubleVal: %s" (show v)

    boolVal (SqlScalar (H.SqlBool b))    = boolE b
    boolVal (SqlScalar (H.SqlInteger i)) = boolE (i /= 0)
    boolVal (SqlScalar (H.SqlInt32 i))   = boolE (i /= 0)
    boolVal (SqlScalar (H.SqlInt64 i))   = boolE (i /= 0)
    boolVal (SqlScalar (H.SqlWord32 i))  = boolE (i /= 0)
    boolVal (SqlScalar (H.SqlWord64 i))  = boolE (i /= 0)
    boolVal (SqlScalar (H.SqlByteString s)) = boolE $ (maybe $impossible fst (BI.readDecimal s) /= (0 :: Integer))
    boolVal (SqlScalar v)                = error $ printf "boolVal: %s" (show v)

    charVal (SqlScalar (H.SqlChar c))       = charE c
    charVal (SqlScalar (H.SqlString (c:_))) = charE c
    charVal (SqlScalar (H.SqlByteString c)) = charE (head $ T.unpack $ TE.decodeUtf8 c)
    charVal _                               = $impossible

    textVal (SqlScalar (H.SqlString t))     = textE (T.pack t)
    textVal (SqlScalar (H.SqlByteString s)) = textE (TE.decodeUtf8 s)
    textVal _                               = $impossible

    -- FIXME this is an incredibly crude method to convert HDBC's
    -- rationals to decimals. Implement this reasonably or - even
    -- better - replace HDBC completely. Rationals do not make sense
    -- here.
    decimalVal (SqlScalar (H.SqlRational d))   = decimalE $ realFracToDecimal 5 d
    decimalVal (SqlScalar (H.SqlByteString c)) = decimalE $ read $ BS.unpack c
    decimalVal (SqlScalar v)                   = error $ printf "decimalVal: %s" (show v)

    dayVal (SqlScalar (H.SqlLocalDate d)) = dayE d
    dayVal _                              = $impossible

--------------------------------------------------------------------------------

fileId :: IO String
fileId = sequence $ replicate 8 $ (randomRIO ('a', 'z'))

-- | Show the unoptimized relational table algebra plan
showRelationalQ :: forall a.DSH.QA a => DSH.Q a -> IO ()
showRelationalQ q = do
    let vl = C.vectorPlanQ q
    let bp = generatePlan vl :: BackendPlan SqlBackend
    h <- fileId
    fileName <- dumpPlan ("q_ta_" ++ h) False bp
    void $ runCommand $ printf ".cabal-sandbox/bin/tadot -i %s.plan | dot -Tpdf -o %s.pdf" fileName fileName
    void $ runCommand $ printf "evince %s.pdf 2> /dev/null" fileName

-- | Show the optimized relational table algebra plan
showRelationalOptQ :: forall a.DSH.QA a => DSH.Q a -> IO ()
showRelationalOptQ q = do
    let vl = C.vectorPlanQ q
    let bp = generatePlan vl :: BackendPlan SqlBackend
    h <- fileId
    fileName <- dumpPlan ("q_ta_" ++ h) True bp
    void $ runCommand $ printf ".cabal-sandbox/bin/tadot -i %s.plan | dot -Tpdf -o %s.pdf" fileName fileName
    void $ runCommand $ printf "evince %s.pdf 2> /dev/null" fileName

-- | Show all SQL queries produced for the given query
showSqlQ :: forall a.DSH.QA a => DSH.Q a -> IO ()
showSqlQ q = do
    putStrLn sepLine
    forM_ (map unwrapCode $ C.codeQ undefined q) $ \sql -> do
         putStrLn sql
         putStrLn sepLine

  where
    sepLine = replicate 80 '-'

-- | Show raw tabular results via 'psql', executed on the specified
-- database..
showTabularQ :: forall a. DSH.QA a => String -> DSH.Q a -> IO ()
showTabularQ db q = do
    forM_ (map unwrapCode $ C.codeQ undefined q) $ \sql -> do
        putStrLn ""
        h <- fileId
        let queryFile = printf "q_%s.sql" h
        writeFile queryFile sql
        hdl <- runCommand $ printf "psql %s < %s" db queryFile
        void $ waitForProcess hdl
        putStrLn sepLine

  where
    sepLine = replicate 80 '-'

