{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE ParallelListComp  #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}

-- | SQL code generators.
module Database.DSH.Backend.Sql.CodeGen
    ( virtualPgCodeGen
    , naturalPgCodeGen
    , syntheticPgCodeGen
    ) where

import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Vector
import           Database.DSH.SL
import           Database.DSH.VSL

import qualified Database.DSH.Backend.Sql.Pg         as Pg
import qualified Database.DSH.Backend.Sql.Relational as R

-- | Generate code for PostgreSQL using virtual/delayed vectors.
virtualPgCodeGen :: QueryPlan VSL DVec -> Shape Pg.PgVector
virtualPgCodeGen = Pg.generatePgQueries . R.virtualVectors

-- | Generate code for PostgreSQL using natural/composite keys and lazy order.
naturalPgCodeGen :: QueryPlan SL DVec -> Shape Pg.PgVector
naturalPgCodeGen = Pg.generatePgQueries . R.naturalKeyVectors

syntheticPgCodeGen :: QueryPlan SL DVec -> Shape Pg.PgVector
syntheticPgCodeGen = undefined
