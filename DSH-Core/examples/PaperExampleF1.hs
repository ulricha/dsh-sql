{-# LANGUAGE QuasiQuotes #-}

module PaperExampleF1 where

import Prelude ()
import Database.DSH
import Database.DSH.Interpreter

import Database.HDBC.PostgreSQL

conn :: Connection
conn = undefined

type Facility = String
type Cat      = String
type Feature  = String
type Meaning  = String

facilities :: Q [(Facility, Cat)]
facilities = toQ [ ("SQL", "QLA"),
               ("ODBC", "API"),
               ("LINQ", "LIN"),
               ("Links", "LIN"),
               ("Rails", "ORM"),
               ("Ferry", "LIB"),
               ("Kleisli", "QLA"),
               ("ADO.NET", "ORM"),
               ("HaskellDB", "LIB")]
               
features :: Q [(Facility, Feature)]
features = toQ [("Kleisli","nest")
          ,("Kleisli","comp")
          ,("Kleisli","type")
          ,("Links","comp")
          ,("Links","type")
          ,("Links","SQL")
          ,("LINQ","nest")
          ,("LINQ","comp")
          ,("LINQ","type")
          ,("HaskellDB","comp")
          ,("HaskellDB","type")
          ,("HaskellDB","SQL")
          ,("SQL","aval")
          ,("SQL","type")
          ,("SQL","SQL")
          ,("Rails","nest")
          ,("Rails","maps")
          ,("ADO.NET","maps")
          ,("ADO.NET","comp")
          ,("ADO.NET","type")
          ,("Ferry","list")
          ,("Ferry","nest")
          ,("Ferry","comp")
          ,("Ferry","aval")
          ,("Ferry","type")
          ,("Ferry","SQL")] 
          
meanings :: Q [(Feature, Meaning)]
meanings = toQ [("maps","admits user-defined object mappings"),
            ("list","respects list order"),
            ("nest","supports data nesting"),
            ("comp","has compositional syntax and semantics"),
            ("aval","avoids query avalanches"),
            ("type","is statically type-checked"),
            ("SQL","guarantees translation to SQL")]

hasFeatures :: Q String -> Q [String] 
hasFeatures f = [$qc| feat | (fac,feat) <- features, fac == f |]

means :: Q String -> Q String
means f = head [$qc| mean | (feat,mean) <- meanings, feat == f |]

query :: IO [(String , [String ])] 
query = fromQ conn [$qc| tuple (the cat, nub $ concat $ map (map means . hasFeatures) fac)
        | (fac, cat) <- facilities, then group by cat |]
        
main :: IO ()
main = query >>= print