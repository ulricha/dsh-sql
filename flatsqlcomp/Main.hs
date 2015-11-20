-- | Read a comprehension expression from stdin or a file and print the SQL
-- shape structure to stdout.
module Main where

import           System.Environment
import           System.IO

import           Data.Aeson
import qualified Data.ByteString.Lazy     as BL

import           Database.DSH.CL.Parser
import           Database.DSH.Common.QueryPlan
import           Database.DSH.Backend.Sql.CodeGen

readInput :: [String] -> IO String
readInput ["-i", inFile] = withFile inFile ReadMode hGetContents
readInput _              = getContents

writeQueries :: Shape SqlCode -> IO ()
writeQueries shape = BL.hPut stdout (encode shape)

main :: IO ()
main = do
    input <- getArgs >>= readInput
    case parseCL input of
        Left msg -> error msg
        Right cl -> writeQueries (comprehensionCodeGen cl)
