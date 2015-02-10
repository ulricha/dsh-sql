module Main where

import Control.Applicative

import Database.HDBC.PostgreSQL

import Database.DSH.Tests
import Database.DSH.Backend.Sql

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'au' password = 'foobar' host = 'localhost' dbname = 'test'"

main :: IO ()
main = do
    c <- sqlBackend <$> getConn
    runTests c defaultTests
