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

import qualified Database.Algebra.Table.Lang     as TA

import           Database.DSH.Common.QueryPlan

import           Database.DSH.Backend.Sql.Common
import           Database.DSH.Backend.Sql.Vector

--------------------------------------------------------------------------------

-- | SQL code generated for MonetDB5/SQL
newtype M5Code = M5Code { unM5 :: String }

instance Show M5Code where
    show = unM5

instance SqlCode M5Code where
    genSqlCode = generateM5Queries

instance ToJSON M5Code where
    toJSON (M5Code sql) = toJSON sql

-- | A data vector described by MonetDB5 SQL
type M5Vector = SqlVector M5Code

--------------------------------------------------------------------------------

-- | Generate MonetDB5 SQL code for a relational query plan.
generateM5Queries :: QueryPlan TA.TableAlgebra TADVec -> Shape M5Vector
generateM5Queries = _
