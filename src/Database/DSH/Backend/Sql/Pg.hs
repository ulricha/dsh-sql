{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE ParallelListComp  #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}

-- | Definition of the SQL backend for DSH: SQL code generation and execution of
-- SQL queries.
module Database.DSH.Backend.Sql.Pg
    ( PgVector
    , PgCode(..)
    , pgConn
    ) where

import           Text.Printf

import qualified Database.HDBC                            as H
import qualified Database.HDBC.ODBC                       as O

import           Control.Monad
import           Data.Aeson
import qualified Data.ByteString.Char8                    as BSC
import qualified Data.ByteString.Lex.Fractional           as BD
import qualified Data.ByteString.Lex.Integral             as BI
import qualified Data.Map                                 as M
import           Data.Maybe
import qualified Data.Text                                as T
import qualified Data.Text.Encoding                       as TE

import qualified Database.Algebra.Dag                     as D
import           Database.Algebra.Dag.Common
import           Database.Algebra.SQL.Compatibility
import           Database.Algebra.SQL.Materialization.CTE
import           Database.Algebra.SQL.Util
import qualified Database.Algebra.Table.Lang              as TA

import           Database.DSH.Common.Impossible
import           Database.DSH.Common.QueryPlan

import           Database.DSH.Backend
import           Database.DSH.Backend.Sql.Common
import           Database.DSH.Backend.Sql.Vector

--------------------------------------------------------------------------------

newtype PgCode = PgCode { unPg :: String }

instance SqlCode PgCode where
    genSqlCode = generatePgQueries

instance ToJSON PgCode where
    toJSON (PgCode sql) = toJSON sql

type PgVector = SqlVector PgCode

-- | Construct a PostgreSQL backend connection from an ODBC connection.
pgConn :: O.Connection -> BackendConn PgVector
pgConn = PgConn

--------------------------------------------------------------------------------

-- | In a query shape, render each root node for the algebraic plan into a
-- separate PostgreSQL SQL query.
generatePgQueries :: QueryPlan TA.TableAlgebra TADVec -> Shape (PgVector)
generatePgQueries taPlan = renderSql $ queryShape taPlan
  where
    roots :: [AlgNode]
    roots = D.rootNodes $ queryDag taPlan

    (_sqlShared, sqlQueries) = renderOutputDSHWith PostgreSQL materialize (queryDag taPlan)

    nodeToQuery :: [(AlgNode, PgCode)]
    nodeToQuery  = zip roots (map PgCode sqlQueries)

    lookupNode :: AlgNode -> PgCode
    lookupNode n = fromMaybe $impossible $ lookup n nodeToQuery

    -- We do not need order columns to reconstruct results: order information is
    -- encoded in the SQL queries' ORDER BY clause. We rely on the physical
    -- order of the result table.
    renderSql = fmap (\(TADVec q _ k r i) -> SqlVector (lookupNode q) k r i)

--------------------------------------------------------------------------------
-- Definition of the PostgreSQL backend

instance Backend PgVector where
    data BackendRow PgVector  = PgRow (M.Map String H.SqlValue)
    data BackendConn PgVector = PgConn O.Connection

    execFlatQuery (PgConn conn) vec = do
        stmt <- H.prepare conn (unPg $ vecCode vec)
        void $ H.execute stmt []
        map PgRow <$> H.fetchAllRowsMap stmt

    transactionally (PgConn conn) ma =
        H.withTransaction conn (ma . PgConn)

--------------------------------------------------------------------------------
-- Encoding of vector rows in SQL result rows.

instance Row (BackendRow PgVector) where
    data Scalar (BackendRow PgVector) = SqlScalar !H.SqlValue

    col !c (PgRow !r) =
        case M.lookup c r of
            Just !v -> SqlScalar v
            Nothing -> error $ printf "col lookup %s failed in %s" c (show r)

    keyVal :: Scalar (BackendRow PgVector) -> KeyVal
    keyVal (SqlScalar !v) = case v of
        H.SqlInt32 !i      -> KInt (fromIntegral i)
        H.SqlInt64 !i      -> KInt (fromIntegral i)
        H.SqlWord32 !i     -> KInt (fromIntegral i)
        H.SqlWord64 !i     -> KInt (fromIntegral i)
        H.SqlInteger !i    -> KInt (fromIntegral i)
        H.SqlString !s     -> KByteString (BSC.pack s)
        H.SqlByteString !s -> KByteString s
        H.SqlLocalDate !d  -> KDay d
        o                  -> error $ printf "keyVal: %s" (show o)


    descrVal (SqlScalar (H.SqlInt32 !i))   = fromIntegral i
    descrVal (SqlScalar (H.SqlInteger !i)) = fromIntegral i
    descrVal (SqlScalar v)                 = error $ printf "descrVal: %s" (show v)

    integerVal (SqlScalar (H.SqlInteger !i))    = i
    integerVal (SqlScalar (H.SqlInt32 !i))      = fromIntegral i
    integerVal (SqlScalar (H.SqlInt64 !i))      = fromIntegral i
    integerVal (SqlScalar (H.SqlWord32 !i))     = fromIntegral i
    integerVal (SqlScalar (H.SqlWord64 !i))     = fromIntegral i
    integerVal (SqlScalar (H.SqlDouble !d))     = truncate d
    integerVal (SqlScalar (H.SqlByteString !s)) = case BI.readSigned BI.readDecimal s of
                                                      Just (i, s') | BSC.null s' -> i
                                                      _                        ->
                                                          error $ printf "integerVal: %s" (show s)
    integerVal (SqlScalar v)                    = error $ printf "integerVal: %s" (show v)

    doubleVal (SqlScalar (H.SqlDouble !d))     = d
    doubleVal (SqlScalar (H.SqlRational !d))   = fromRational d
    doubleVal (SqlScalar (H.SqlInteger !d))    = fromIntegral d
    doubleVal (SqlScalar (H.SqlInt32 !d))      = fromIntegral d
    doubleVal (SqlScalar (H.SqlInt64 !d))      = fromIntegral d
    doubleVal (SqlScalar (H.SqlWord32 !d))     = fromIntegral d
    doubleVal (SqlScalar (H.SqlWord64 !d))     = fromIntegral d
    doubleVal (SqlScalar (H.SqlByteString !c)) = case BD.readSigned BD.readDecimal c of
                                                     Just (!v, _) -> v
                                                     Nothing      -> $impossible
    doubleVal (SqlScalar v)                    = error $ printf "doubleVal: %s" (show v)

    boolVal (SqlScalar (H.SqlBool !b))       = b
    boolVal (SqlScalar (H.SqlInteger !i))    = i /= 0
    boolVal (SqlScalar (H.SqlInt32 !i))      = i /= 0
    boolVal (SqlScalar (H.SqlInt64 !i))      = i /= 0
    boolVal (SqlScalar (H.SqlWord32 !i))     = i /= 0
    boolVal (SqlScalar (H.SqlWord64 !i))     = i /= 0
    boolVal (SqlScalar (H.SqlByteString !s)) = case BI.readDecimal s of
                                                  Just (!d, _) -> d /= (0 :: Int)
                                                  Nothing      -> $impossible
    boolVal (SqlScalar v)                   = error $ printf "boolVal: %s" (show v)

    charVal (SqlScalar (H.SqlChar !c))       = c
    charVal (SqlScalar (H.SqlString (c:_)))  = c
    charVal (SqlScalar (H.SqlByteString !s)) = case T.uncons (TE.decodeUtf8 s) of
                                                   Just (!c, _) -> c
                                                   Nothing      -> $impossible
    charVal (SqlScalar v)                    = error $ printf "charVal: %s" (show v)

    textVal (SqlScalar (H.SqlString !t))     = T.pack t
    textVal (SqlScalar (H.SqlByteString !s)) = TE.decodeUtf8 s
    textVal (SqlScalar v)                    = error $ printf "textVal: %s" (show v)

    decimalVal (SqlScalar (H.SqlRational !d))   = fromRational d
    decimalVal (SqlScalar (H.SqlByteString !c)) =
        case BD.readSigned BD.readDecimal c of
            Just (!d, _) -> d
            Nothing      -> error $ show c
    decimalVal (SqlScalar v)                    = error $ printf "decimalVal: %s" (show v)

    dayVal (SqlScalar (H.SqlLocalDate d)) = d
    dayVal (SqlScalar v)                  = error $ printf "dayVal: %s" (show v)
