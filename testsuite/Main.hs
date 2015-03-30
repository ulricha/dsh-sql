module Main where

import System.Environment

import Database.HDBC.ODBC

import Database.DSH.Tests
import Database.DSH.Backend.Sql

getConn :: String -> IO Connection
getConn connString = connectODBC connString

main :: IO ()
main = do
    argv <- getArgs
    case argv of
        [connString] -> do
            c <- sqlBackend <$> getConn connString
            runTests c defaultTests
        _            ->
            error "usage: sqltests <connection string>"
