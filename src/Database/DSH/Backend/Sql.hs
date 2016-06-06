{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeFamilies      #-}

-- | This module provides the execution of DSH queries as SQL query bundles and the
-- construction of nested values from the resulting vector bundle.
module Database.DSH.Backend.Sql
  ( -- * Show and tell: display relational plans.
    showRelationalQ
  , showRelationalOptQ
  , showTabularQ
    -- * Various SQL code generators
  , module Database.DSH.Backend.Sql.CodeGen
    -- * A PostgreSQL ODBC backend
  , module Database.DSH.Backend.Sql.Pg
    -- * SQL backend vectors
  , module Database.DSH.Backend.Sql.Vector
  ) where

import           Control.Monad
import           System.Process
import           System.Random
import           Text.Printf

import qualified Database.DSH                            as DSH
import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Vector
import           Database.DSH.Compiler

import           Database.DSH.Backend.Sql.Opt.OptimizeTA
import           Database.DSH.Backend.Sql.Pg
import           Database.DSH.Backend.Sql.Relational
import           Database.DSH.Backend.Sql.Vector
import           Database.DSH.Backend.Sql.CodeGen

{-# ANN module "HLint: ignore Reduce duplication" #-}

--------------------------------------------------------------------------------

fileId :: IO String
fileId = replicateM 8 (randomRIO ('a', 'z'))

-- | Show the unoptimized relational table algebra plan
showRelationalQ :: (DSH.QA a, VectorLang v) => RelPlanGen v -> DSH.Q a -> IO ()
showRelationalQ relGen q = do
    let vectorPlan = vectorPlanQ q
        relPlan    = relGen vectorPlan
    prefix <- ("q_ta_" ++) <$> fileId
    exportPlan prefix relPlan
    void $ runCommand $ printf "stack exec tadot -- -i %s.plan | dot -Tpdf -o %s.pdf && open %s.pdf" prefix prefix prefix

-- | Show the optimized relational table algebra plan
showRelationalOptQ :: (DSH.QA a, VectorLang v) => RelPlanGen v -> DSH.Q a -> IO ()
showRelationalOptQ relGen q = do
    let vectorPlan = vectorPlanQ q
        relPlan    = optimizeTA $ relGen vectorPlan
    prefix <- ("q_ta_opt_" ++) <$> fileId
    exportPlan prefix relPlan
    void $ runCommand $ printf "stack exec tadot -- -i %s.plan | dot -Tpdf -o %s.pdf && open %s.pdf" prefix prefix prefix

-- | Show raw tabular results via 'psql', executed on the specified
-- database..
showTabularQ :: (DSH.QA a, VectorLang v)
             => (QueryPlan v DVec -> Shape (SqlVector PgCode))
             -> String
             -> DSH.Q a
             -> IO ()
showTabularQ pgCodeGen dbName q =
    forM_ (codeQ pgCodeGen q) $ \sql -> do
        putStrLn ""
        h <- fileId
        let queryFile = printf "q_%s.sql" h
        writeFile queryFile $ unPg $ vecCode sql
        hdl <- runCommand $ printf "psql %s < %s" dbName queryFile
        void $ waitForProcess hdl
        putStrLn sepLine

  where
    sepLine = replicate 80 '-'

