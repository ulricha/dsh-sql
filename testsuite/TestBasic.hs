module Main where

import           System.Environment
import           Text.Printf

import           Database.HDBC.ODBC

import           Database.DSH.Backend
import           Database.DSH.Backend.Sql
import           Database.DSH.Tests

getConn :: String -> IO (BackendConn PgVector)
getConn connString = pgConn <$> connectODBC connString

main :: IO ()
main = do
    argv <- getArgs
    case argv of
        _:_ -> do
            c <- getConn (printf "DSN=%s" $ last argv)
            runTests (init argv) $ defaultTests naturalPgCodeGen c
        _            ->
            error "usage: sqltests [test-framework arguments] <odbc dbname>"
