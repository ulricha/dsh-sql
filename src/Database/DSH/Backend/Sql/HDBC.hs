{-# LANGUAGE BangPatterns    #-}
{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Backend.Sql.HDBC
    ( hdbcKey
    , hdbcDescr
    , hdbcInteger
    , hdbcDouble
    , hdbcBool
    , hdbcChar
    , hdbcText
    , hdbcDecimal
    , hdbcDay
    ) where

import qualified Data.ByteString.Char8          as BSC
import qualified Data.ByteString.Lex.Fractional as BD
import qualified Data.ByteString.Lex.Integral   as BI
import           Data.Decimal
import qualified Data.Text                      as T
import           Data.Time.Calendar
import qualified Database.HDBC                  as H
import           Text.Printf
import qualified Data.Text.Encoding                       as TE

import           Database.DSH.Backend
import           Database.DSH.Common.Impossible

hdbcKey :: H.SqlValue -> KeyVal
hdbcKey !v = case v of
    H.SqlInt32 !i      -> KInt (fromIntegral i)
    H.SqlInt64 !i      -> KInt (fromIntegral i)
    H.SqlWord32 !i     -> KInt (fromIntegral i)
    H.SqlWord64 !i     -> KInt (fromIntegral i)
    H.SqlInteger !i    -> KInt (fromIntegral i)
    H.SqlString !s     -> KByteString (BSC.pack s)
    H.SqlByteString !s -> KByteString s
    H.SqlLocalDate !d  -> KDay d
    o                  -> error $ printf "hdbcKey: %s" (show o)

hdbcDescr :: H.SqlValue -> Int
hdbcDescr (H.SqlInt32 !i)   = fromIntegral i
hdbcDescr (H.SqlInteger !i) = fromIntegral i
hdbcDescr v                 = error $ printf "hdbcDescr: %s" (show v)


hdbcInteger :: H.SqlValue -> Integer
hdbcInteger (H.SqlInteger !i)    = i
hdbcInteger (H.SqlInt32 !i)      = fromIntegral i
hdbcInteger (H.SqlInt64 !i)      = fromIntegral i
hdbcInteger (H.SqlWord32 !i)     = fromIntegral i
hdbcInteger (H.SqlWord64 !i)     = fromIntegral i
hdbcInteger (H.SqlDouble !d)     = truncate d
hdbcInteger (H.SqlByteString !s) = case BI.readSigned BI.readDecimal s of
                                       Just (i, s') | BSC.null s' -> i
                                       _                        ->
                                           error $ printf "hdbcInteger: %s" (show s)
hdbcInteger v                    = error $ printf "hdbcInteger: %s" (show v)

hdbcDouble :: H.SqlValue -> Double
hdbcDouble (H.SqlDouble !d)     = d
hdbcDouble (H.SqlRational !d)   = fromRational d
hdbcDouble (H.SqlInteger !d)    = fromIntegral d
hdbcDouble (H.SqlInt32 !d)      = fromIntegral d
hdbcDouble (H.SqlInt64 !d)      = fromIntegral d
hdbcDouble (H.SqlWord32 !d)     = fromIntegral d
hdbcDouble (H.SqlWord64 !d)     = fromIntegral d
hdbcDouble (H.SqlByteString !c) = case BD.readSigned BD.readDecimal c of
                                     Just (!v, _) -> v
                                     Nothing      -> $impossible
hdbcDouble v                    = error $ printf "hdbcDouble: %s" (show v)

hdbcBool :: H.SqlValue -> Bool
hdbcBool (H.SqlBool !b)       = b
hdbcBool (H.SqlInteger !i)    = i /= 0
hdbcBool (H.SqlInt32 !i)      = i /= 0
hdbcBool (H.SqlInt64 !i)      = i /= 0
hdbcBool (H.SqlWord32 !i)     = i /= 0
hdbcBool (H.SqlWord64 !i)     = i /= 0
hdbcBool (H.SqlByteString !s) = case BI.readDecimal s of
                                    Just (!d, _) -> d /= (0 :: Int)
                                    Nothing      -> $impossible
hdbcBool v                   = error $ printf "hdbcBool: %s" (show v)

hdbcChar :: H.SqlValue -> Char
hdbcChar (H.SqlChar !c)       = c
hdbcChar (H.SqlString (c:_))  = c
hdbcChar (H.SqlByteString !s) = case T.uncons (TE.decodeUtf8 s) of
                                     Just (!c, _) -> c
                                     Nothing      -> $impossible
hdbcChar v                    = error $ printf "hdbcChar: %s" (show v)

hdbcText :: H.SqlValue -> T.Text
hdbcText (H.SqlString !t)     = T.pack t
hdbcText (H.SqlByteString !s) = TE.decodeUtf8 s
hdbcText v                    = error $ printf "hdbcText: %s" (show v)

hdbcDecimal :: H.SqlValue -> Decimal
hdbcDecimal (H.SqlRational !d)   = fromRational d
hdbcDecimal (H.SqlByteString !c) =
    case BD.readSigned BD.readDecimal c of
        Just (!d, _) -> d
        Nothing      -> error $ show c
hdbcDecimal v                    = error $ printf "hdbcDecimal: %s" (show v)

hdbcDay :: H.SqlValue -> Day
hdbcDay (H.SqlLocalDate d) = d
hdbcDay v                  = error $ printf "hdbcDay: %s" (show v)
