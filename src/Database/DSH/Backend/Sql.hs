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
  --   showRelationalQ
  -- , showRelationalOptQ
  -- , showTabularQ
  --   -- * Various SQL code generators
  -- , module Database.DSH.Backend.Sql.CodeGen
  --   -- * A PostgreSQL ODBC backend
  -- , module Database.DSH.Backend.Sql.Pg
  --   -- * SQL backend vectors
  -- , module Database.DSH.Backend.Sql.Vector
  ) where

import           Control.Monad
import qualified Data.IntMap                                     as IM
import           System.Process
import           System.Random
import           Text.Printf

import qualified Database.DSH                                    as DSH
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.QueryPlan
import           Database.DSH.Compiler
import           Database.DSH.SL

-- import           Database.DSH.Backend.Sql.Opt.OptimizeTA
-- import           Database.DSH.Backend.Sql.Pg
-- import           Database.DSH.Backend.Sql.Relational
-- import           Database.DSH.Backend.Sql.Vector
-- import           Database.DSH.Backend.Sql.CodeGen

import           Database.DSH.Backend.Sql.MultisetAlgebra.Opt
import           Database.DSH.Backend.Sql.MultisetAlgebra.Typing
import           Database.DSH.Backend.Sql.Unordered

{-# ANN module "HLint: ignore Reduce duplication" #-}

--------------------------------------------------------------------------------

fileId :: IO String
fileId = replicateM 8 (randomRIO ('a', 'z'))

-- | Show the unoptimized multiset algebra plan
showUnorderedQ :: VectorLang v => CLOptimizer -> MAPlanGen (v TExpr TExpr) -> DSH.Q a -> IO ()
showUnorderedQ clOpt maGen q = do
    let vectorPlan = vectorPlanQ clOpt q
        maPlan     = maGen vectorPlan
    prefix <- ("q_ma_" ++) <$> fileId
    case inferMATypes (queryDag maPlan) of
        Left e    -> putStrLn e
        Right tys -> putStrLn $ pp $ IM.toList tys
    exportPlan prefix maPlan
    void $ runCommand $ printf "stack exec madot -- -i %s.plan | dot -Tpdf -o %s.pdf && open %s.pdf" prefix prefix prefix

-- | Show the optimized multiset algebra plan
showUnorderedOptQ :: VectorLang v => CLOptimizer -> MAPlanGen (v TExpr TExpr) -> DSH.Q a -> IO ()
showUnorderedOptQ clOpt maGen q = do
    let vectorPlan = vectorPlanQ clOpt q
    let maPlan = maGen vectorPlan
    case inferMATypes (queryDag maPlan) of
        Left e    -> putStrLn $ "Type inference failed for unoptimized plan\n" ++ e
        Right tys -> putStrLn $ pp $ IM.toList tys
    let maPlanOpt     = optimizeMA maPlan
    case inferMATypes (queryDag maPlanOpt) of
        Left e    -> putStrLn $ "Type inference failed for optimized plan\n" ++ e
        Right tys -> putStrLn $ pp $ IM.toList tys
    prefix <- ("q_ma_" ++) <$> fileId
    exportPlan prefix maPlan
    void $ runCommand $ printf "stack exec madot -- -i %s.plan | dot -Tpdf -o %s.pdf && open %s.pdf" prefix prefix prefix

-- -- | Show the unoptimized relational table algebra plan
-- showRelationalQ :: VectorLang v => CLOptimizer -> RelPlanGen v -> DSH.Q a -> IO ()
-- showRelationalQ clOpt relGen q = do
--     let vectorPlan = vectorPlanQ clOpt q
--         relPlan    = relGen vectorPlan
--     prefix <- ("q_ta_" ++) <$> fileId
--     exportPlan prefix relPlan
--     void $ runCommand $ printf "stack exec tadot -- -i %s.plan | dot -Tpdf -o %s.pdf && open %s.pdf" prefix prefix prefix

-- -- | Show the optimized relational table algebra plan
-- showRelationalOptQ :: VectorLang v => CLOptimizer -> RelPlanGen v -> DSH.Q a -> IO ()
-- showRelationalOptQ clOpt relGen q = do
--     let vectorPlan = vectorPlanQ clOpt q
--         relPlan    = optimizeTA defaultPipeline $ relGen vectorPlan
--     prefix <- ("q_ta_opt_" ++) <$> fileId
--     exportPlan prefix relPlan
--     void $ runCommand $ printf "stack exec tadot -- -i %s.plan | dot -Tpdf -o %s.pdf && open %s.pdf" prefix prefix prefix

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

