-- | A DSH example program. It executes three simple DSH queries from package
-- 'dsh-example-queries' on a PostgreSQL TPC-H database. The command line
-- parameter has to be the DSN for an ODBC connection.
module Main where

import           System.Environment
import           Text.Printf

import           Database.HDBC
import           Database.HDBC.ODBC

import           Database.DSH             (Q, QA)
import           Database.DSH.Backend
import           Database.DSH.Backend.Sql
import           Database.DSH.Compiler

import           Queries.SIGMOD

getConn :: String -> IO Connection
getConn dsn = connectODBC (printf "DSN=%s" dsn)

-- | Compile a DSH query to a bundle of PostgreSQL SQL queries, execute them and
-- print the resulting Haskell value.
execQ :: (QA a, Show a) => BackendConn PgVector -> Q a -> IO ()
execQ c q = runQ naturalPgCodeGen c q >>= print

main :: IO ()
main = do
    argv <- getArgs
    case argv of
        [dsn] -> do
            c <- getConn dsn
            let dshConn = pgConn c
            execQ dshConn exists1
            execQ dshConn allRegionsNations
            execQ dshConn shippingDelay
            disconnect c
        _     ->
            error "usage: runpg <odbc dbname>"
