-- | Read a comprehension expression from stdin or a file and print the SQL
-- shape structure to stdout.
module Main where

import           System.Console.GetOpt
import           System.Environment
import           System.Exit
import           System.IO

import           Data.Aeson
import qualified Data.ByteString.Lazy             as BL

import           Database.DSH.Backend.Sql.CodeGen
import           Database.DSH.CL.Parser
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.QueryPlan

data Options = Options { optInput :: IO String
                       , optPrint :: Bool
                       }

startOptions :: Options
startOptions = Options { optInput  = getContents
                       , optPrint  = False
                       }

options :: [OptDescr (Options -> IO Options)]
options =
    [ Option "i" ["input"]
          (ReqArg (\arg opt -> return opt { optInput = readFile arg })
           "FILE")
            "Input file"
    , Option "p" ["print"]
          (NoArg (\opt -> return opt { optPrint = True }))
           "Just pretty-print the input (no compilation)"
    , Option "h" ["help"]
          (NoArg
           (\_ -> do
                prg <- getProgName
                hPutStrLn stderr (usageInfo prg options)
                exitSuccess))
           "Show help"
    ]

printQueries :: Shape SqlVector -> IO ()
printQueries shape = BL.hPut stdout (encode shape)

main :: IO ()
main = do
    args  <- getArgs

    let (actions, _, _) = getOpt RequireOrder options args
    opts  <- foldl (>>=) (return startOptions) actions
    input <- optInput opts
    case parseCL input of
        Left msg -> error msg
        Right cl ->
            if optPrint opts
                then putStrLn (pp cl) >> exitSuccess
                else printQueries (comprehensionCodeGen cl)

