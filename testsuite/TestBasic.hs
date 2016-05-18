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
        _:_ -> do
            c <- getConn (printf "DSN=%s" $ last argv)
            runTests (init argv) $ defaultTests c
        _            ->
            error "usage: sqltests [test-framework arguments] <odbc dbname>"
