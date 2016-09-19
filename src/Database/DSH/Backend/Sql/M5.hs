{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE ParallelListComp  #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}

-- | Definition of the MonetDB5/SQL backend for DSH: SQL code generation and
-- execution of SQL queries.
module Database.DSH.Backend.Sql.M5 where

import           Data.Aeson

import           Database.Algebra.SQL.Dialect
import           Database.Algebra.SQL.Materialization.CTE
import           Database.Algebra.SQL.Util

import           Database.DSH.Backend.Sql.Common

--------------------------------------------------------------------------------

-- | SQL code generated for MonetDB5/SQL
newtype M5Code = M5Code { unM5 :: String }

instance Show M5Code where
    show = unM5

instance SqlCode M5Code where
    genSqlCode dag = (M5Code <$> prelude, M5Code <$> queries)
      where
        (prelude, queries) = renderOutputDSHWith MonetDB materialize dag

instance ToJSON M5Code where
    toJSON (M5Code sql) = toJSON sql

-- | A data vector described by MonetDB5 SQL
type M5Vector = SqlVector M5Code

--------------------------------------------------------------------------------
