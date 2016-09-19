{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE ParallelListComp  #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}

-- | SQL code generators.
module Database.DSH.Backend.Sql.CodeGen
    ( -- * PostgreSQL code generators
      virtualPgCodeGen
    , naturalPgCodeGen
    , syntheticPgCodeGen
      -- * MonetDB5/SQL code generators
    , naturalM5CodeGen
    ) where

import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Vector
import           Database.DSH.SL
import           Database.DSH.VSL

import           Database.DSH.Backend.Sql.Common
import qualified Database.DSH.Backend.Sql.M5         as M5
import qualified Database.DSH.Backend.Sql.Pg         as Pg
import qualified Database.DSH.Backend.Sql.Relational as R

--------------------------------------------------------------------------------
-- PostgreSQL code generators

-- | Generate code for PostgreSQL using virtual/delayed vectors.
virtualPgCodeGen :: QueryPlan VSL DVec -> Shape Pg.PgVector
virtualPgCodeGen = generateSqlShape . R.optimizeTA . R.virtualVectors

-- | Generate code for PostgreSQL using natural/composite keys and lazy order.
naturalPgCodeGen :: QueryPlan SL DVec -> Shape Pg.PgVector
naturalPgCodeGen = generateSqlShape . R.optimizeTA . R.naturalKeyVectors

syntheticPgCodeGen :: QueryPlan SL DVec -> Shape Pg.PgVector
syntheticPgCodeGen = undefined

--------------------------------------------------------------------------------
-- MonetDB5 SQL code generators

-- | Generate code for MonetDB5/SQL using natural/composite keys and lazy order.
naturalM5CodeGen :: QueryPlan SL DVec -> Shape M5.M5Vector
naturalM5CodeGen = generateSqlShape . R.optimizeTA . R.naturalKeyVectors
