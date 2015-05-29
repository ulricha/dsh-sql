module Main where

import System.Environment
import Text.Printf

import Database.HDBC.ODBC

import Database.DSH.Tests
import Database.DSH.Backend.Sql

getConn :: String -> IO SqlBackend
getConn connString = sqlBackend <$> connectODBC connString

main :: IO ()
main = do
    argv <- getArgs
    case argv of
        [db] -> do
            c <- getConn (printf "DSN=%s" db)
            runTests c defaultTests
        _            ->
            error "usage: sqltests <odbc dbname>"
