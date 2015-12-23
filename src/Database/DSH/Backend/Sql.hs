{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeFamilies      #-}

-- | This module provides the execution of DSH queries as SQL query bundles and the
-- construction of nested values from the resulting vector bundle.
module Database.DSH.Backend.Sql
  ( -- * The relational SQL backend
    SqlBackend
  , sqlBackend
    -- * Show and tell: display relational plans.
  , showRelationalQ
  , showRelationalOptQ
  , showSqlQ
  , showTabularQ
  ) where

import           System.Process
import           System.Random
import           Text.Printf

import           Control.Monad

import qualified Database.DSH                             as DSH
import           Database.DSH.Backend
import           Database.DSH.Backend.Sql.CodeGen
import qualified Database.DSH.Compiler                    as C

--------------------------------------------------------------------------------

fileId :: IO String
fileId = replicateM 8 (randomRIO ('a', 'z'))

-- | Show the unoptimized relational table algebra plan
showRelationalQ :: forall a.DSH.QA a => DSH.Q a -> IO ()
showRelationalQ q = do
    let vl = C.vectorPlanQ q
    let bp = generatePlan vl :: BackendPlan SqlBackend
    h <- fileId
    fileName <- dumpPlan ("q_ta_" ++ h) False bp
    void $ runCommand $ printf "stack exec tadot -- -i %s.plan | dot -Tpdf -o %s.pdf && open %s.pdf" fileName fileName fileName

-- | Show the optimized relational table algebra plan
showRelationalOptQ :: forall a.DSH.QA a => DSH.Q a -> IO ()
showRelationalOptQ q = do
    let vl = C.vectorPlanQ q
    let bp = generatePlan vl :: BackendPlan SqlBackend
    h <- fileId
    fileName <- dumpPlan ("q_ta_" ++ h) True bp
    void $ runCommand $ printf "stack exec tadot -- -i %s.plan | dot -Tpdf -o %s.pdf && open %s.pdf" fileName fileName fileName

-- | Show all SQL queries produced for the given query
showSqlQ :: forall a.DSH.QA a => DSH.Q a -> IO ()
showSqlQ q = do
    putStrLn sepLine
    forM_ (map (unSql . unwrapSql) $ C.codeQ undefined q) $ \sql -> do
         putStrLn sql
         putStrLn sepLine

  where
    sepLine = replicate 80 '-'

-- | Show raw tabular results via 'psql', executed on the specified
-- database..
showTabularQ :: forall a. DSH.QA a => String -> DSH.Q a -> IO ()
showTabularQ db q =
    forM_ (map (unSql . unwrapSql) $ C.codeQ undefined q) $ \sql -> do
        putStrLn ""
        h <- fileId
        let queryFile = printf "q_%s.sql" h
        writeFile queryFile sql
        hdl <- runCommand $ printf "psql %s < %s" db queryFile
        void $ waitForProcess hdl
        putStrLn sepLine

  where
    sepLine = replicate 80 '-'

