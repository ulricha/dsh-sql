{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeSynonymInstances  #-}

-- | Benchmark TPC-H queries executed using DSH against native SQL queries
-- executed using HDBC.
module Main where

import           Control.Monad
import           System.Environment
import           System.Exit

import           Control.DeepSeq          (NFData)
import qualified Criterion                as B
import qualified Criterion.Main           as M
import qualified Database.HDBC.ODBC       as O

import qualified Database.DSH             as Q
import qualified Database.DSH.Backend.Sql as S
import qualified Database.DSH.Compiler    as C

import           Queries.TPCH.NonStandard
import           Queries.TPCH.Standard

-- provide sql text in environment.
-- prepare query on every go.
-- Produce list result with the same type as DSH query.

--------------------------------------------------------------------------------
-- Execute benchmarks

-- | Benchmark the complete execution of a DSH query
benchmarkDSH :: (Q.QA a, NFData a)
             => String
             -> O.Connection
             -> Q.Q a
             -> B.Benchmark
benchmarkDSH benchName c q = B.bench benchName $ B.nfIO (C.runQ S.naturalPgCodeGen (S.pgConn c) q)

--------------------------------------------------------------------------------
-- Benchmark definition

benchmarks :: O.Connection -> [B.Benchmark]
benchmarks c =
    [ B.bgroup "tpch"
        [ benchmarkDSH "q1" c q1Default
        , benchmarkDSH "q2" c q2Default
        , benchmarkDSH "q3" c q3Default
        , benchmarkDSH "q4" c q4Default
        , benchmarkDSH "q5" c q5Default
        , benchmarkDSH "q6" c q6Default
        , benchmarkDSH "q7" c q7Default
        , benchmarkDSH "q8" c q8Default
        , benchmarkDSH "q9" c q9Default
        , benchmarkDSH "q10" c q10Default
        , benchmarkDSH "q11" c q11Default
        , benchmarkDSH "q12" c q12Default
        , benchmarkDSH "q13" c q13Default
        , benchmarkDSH "q14" c q14Default
        , benchmarkDSH "q15" c q15Default
        , benchmarkDSH "q16" c q16Default
        , benchmarkDSH "q17" c q17Default
        , benchmarkDSH "q18" c q18Default
        -- , benchmarkDSH "q19" c q19Default
        , benchmarkDSH "q20" c q20Default
        -- , benchmarkDSH "q21" c q21Default
        , benchmarkDSH "q22" c q22Default
        ]
    , B.bgroup "nested"
        [ benchmarkDSH "custfromorders" c (custFromOrders "GERMANY")
        , benchmarkDSH "custrevenues" c (custRevenues "GERMANY")
        , benchmarkDSH "expectedrevenuefor" c (expectedRevenueFor "GERMANY")
        , benchmarkDSH "shippingdelayinterval" c shippingDelayInterval
        , benchmarkDSH "toporderspercust" c (topOrdersPerCust' 10 "GERMANY")
        , benchmarkDSH "regionstopcustomers" c (regionsTopCustomers "EUROPE" 10)
        , benchmarkDSH "unshippeditemspercustomer" c (unshippedItemsPerCustomer "GERMANY")
        , benchmarkDSH "cheapersuppliersinregion" c (cheaperSuppliersInRegion "EUROPE")
        , benchmarkDSH "cheapersuppliersinregionavg" c (cheaperSuppliersInRegionAvg "EUROPE")
        , benchmarkDSH "cheapersuppliersinregionavg2" c (cheaperSuppliersInRegionAvg2 "EUROPE")
        ]
    ]

main :: IO ()
main = do
    args <- getArgs
    when ("--help" `elem` args) $ do
        putStrLn "bench-tpch [criterion args] <dbname>"
        withArgs ["--help"] $ M.defaultMain []
        exitFailure

    let critArgs = init args
    let db = last args
    c <- O.connectODBC $ "DSN=" ++ db
    withArgs critArgs $ M.defaultMain $ benchmarks c
