{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeFamilies      #-}

-- | This module provides the execution of DSH queries as SQL query bundles and the
-- construction of nested values from the resulting vector bundle.
module Database.DSH.Backend.Sql
  ( -- * Show and tell: display relational plans.
    showUnorderedQ
  , showUnorderedOptQ
  , showRelationalQ
  , showRelationalOptQ
  -- , showTabularQ
    -- * Various SQL code generators
  , module Database.DSH.Backend.Sql.CodeGen
    -- * A PostgreSQL ODBC backend
  , module Database.DSH.Backend.Sql.Pg
    -- * SQL backend vectors
  , module Database.DSH.Backend.Sql.Vector
  ) where

import           Control.Monad
import qualified System.Info                              as Sys
import           System.Process
import           System.Random
import           Text.Printf

import qualified Database.DSH                             as DSH
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.QueryPlan
import           Database.DSH.Compiler
import           Database.DSH.SL

import           Database.Algebra.Dag
import qualified Database.Algebra.Table.Lang              as TA
import qualified Database.Algebra.Table.Typing            as TY

import           Database.DSH.Backend.Sql.CodeGen
import qualified Database.DSH.Backend.Sql.MultisetAlgebra as MA
import qualified Database.DSH.Backend.Sql.Opt             as TAOpt
import           Database.DSH.Backend.Sql.Pg
import           Database.DSH.Backend.Sql.Unordered
import           Database.DSH.Backend.Sql.Vector

{-# ANN module "HLint: ignore Reduce duplication" #-}

--------------------------------------------------------------------------------

fileId :: IO String
fileId = replicateM 8 (randomRIO ('a', 'z'))

pdfCmd :: String -> String
pdfCmd f =
    case Sys.os of
        "linux"  -> "evince " ++ f
        "darwin" -> "open " ++ f
        sys      -> error $ "pdfCmd: unsupported os " ++ sys

typeCheckMA :: String -> AlgebraDag MA.MA -> IO ()
typeCheckMA flavor dag =
    case MA.inferMATypes dag of
        Left msg -> putStrLn $ printf "Type inference failed for %s MA plan\n%s" flavor msg
        Right _  -> putStrLn $ printf "Type inference successful for %s MA plan" flavor

typeCheckTA :: String -> AlgebraDag TA.TableAlgebra -> IO ()
typeCheckTA flavor dag =
    case TY.inferTATypes dag of
        Left msg -> putStrLn $ printf "Type inference failed for %s TA plan\n%s" flavor msg
        Right _  -> putStrLn $ printf "Type inference successful for %s TA plan" flavor

showMAPlan :: QueryPlan MA.MA MADVec -> IO ()
showMAPlan maPlan = do
    prefix <- ("q_ma_" ++) <$> fileId
    exportPlan prefix maPlan
    void $ runCommand $ printf "stack exec madot -- -i %s.plan | dot -Tpdf -o %s.pdf && %s" prefix prefix (pdfCmd $ prefix ++ ".pdf")

showTAPlan :: QueryPlan TA.TableAlgebra TADVec -> IO ()
showTAPlan taPlan = do
    prefix <- ("q_ta_" ++) <$> fileId
    exportPlan prefix taPlan
    void $ runCommand $ printf "stack exec tadot -- -i %s.plan | dot -Tpdf -o %s.pdf && %s" prefix prefix (pdfCmd $ prefix ++ ".pdf")

-- | Show the unoptimized multiset algebra plan
showUnorderedQ :: VectorLang v => CLOptimizer -> MAPlanGen (v TExpr TExpr) -> DSH.Q a -> IO ()
showUnorderedQ clOpt maGen q = do
    let vectorPlan = vectorPlanQ clOpt q
        maPlan     = maGen vectorPlan
    typeCheckMA "unoptimized" (queryDag maPlan)
    showMAPlan maPlan
    putStrLn $ pp $ queryShape maPlan

-- | Show the optimized multiset algebra plan
showUnorderedOptQ :: VectorLang v => CLOptimizer -> MAPlanGen (v TExpr TExpr) -> DSH.Q a -> IO ()
showUnorderedOptQ clOpt maGen q = do
    let vectorPlan = vectorPlanQ clOpt q
    let maPlan = maGen vectorPlan
    typeCheckMA "unoptimized" (queryDag maPlan)
    let maPlanOpt     = MA.optimizeMA maPlan
    typeCheckMA "optimized" (queryDag maPlanOpt)
    showMAPlan maPlanOpt
    putStrLn $ pp $ queryShape maPlanOpt

-- | Show the unoptimized table algebra plan
showRelationalQ :: VectorLang v => CLOptimizer -> MAPlanGen (v TExpr TExpr) -> DSH.Q a -> IO ()
showRelationalQ clOpt maGen q = do
    let vectorPlan = vectorPlanQ clOpt q
    let maPlan = maGen vectorPlan
    typeCheckMA "unoptimized" (queryDag maPlan)
    let maPlanOpt     = MA.optimizeMA maPlan
    typeCheckMA "optimized" (queryDag maPlanOpt)
    let taPlan = MA.flattenMAPlan maPlanOpt
    typeCheckTA "unoptimized" (queryDag taPlan)
    showTAPlan taPlan
    putStrLn $ pp $ queryShape taPlan

-- | Show the unoptimized table algebra plan
showRelationalOptQ :: VectorLang v => CLOptimizer -> MAPlanGen (v TExpr TExpr) -> DSH.Q a -> IO ()
showRelationalOptQ clOpt maGen q = do
    let vectorPlan = vectorPlanQ clOpt q
    let maPlan = maGen vectorPlan
    typeCheckMA "unoptimized" (queryDag maPlan)
    let maPlanOpt     = MA.optimizeMA maPlan
    typeCheckMA "optimized" (queryDag maPlanOpt)
    let taPlan = MA.flattenMAPlan maPlanOpt
    typeCheckTA "unoptimized" (queryDag taPlan)
    let taPlanOpt = TAOpt.optimizeTA TAOpt.defaultPipeline taPlan
    typeCheckTA "optimized" (queryDag taPlanOpt)
    showTAPlan taPlanOpt
    putStrLn $ pp $ queryShape taPlanOpt

-- -- | Show raw tabular results via 'psql', executed on the specified
-- -- database..
-- showTabularQ :: VectorLang v
--              => CLOptimizer
--              -> (QueryPlan v DVec -> Shape (SqlVector PgCode))
--              -> String
--              -> DSH.Q a
--              -> IO ()
-- showTabularQ clOpt pgCodeGen dbName q =
--     forM_ (codeQ clOpt pgCodeGen q) $ \sql -> do
--         putStrLn ""
--         h <- fileId
--         let queryFile = printf "q_%s.sql" h
--         writeFile queryFile $ unPg $ vecCode sql
--         hdl <- runCommand $ printf "psql %s < %s" dbName queryFile
--         void $ waitForProcess hdl
--         putStrLn sepLine

--   where
--     sepLine = replicate 80 '-'

