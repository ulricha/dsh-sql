{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE ParallelListComp  #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}

-- | Definition of the SQL backend for DSH: SQL code generation and execution of
-- SQL queries.
module Database.DSH.Backend.Sql.CodeGen
    ( virtualPgCodeGen
    , naturalPgCodeGen
    , syntheticPgCodeGen
    ) where

import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Vector
import           Database.DSH.VSL
import           Database.DSH.SL

import           Database.DSH.Backend.Sql.Pg
import           Database.DSH.Backend.Sql.Vector

virtualPgCodeGen :: QueryPlan VSL DVec -> Shape PgVector
virtualPgCodeGen = undefined

naturalPgCodeGen :: QueryPlan SL DVec -> Shape PgVector
naturalPgCodeGen = undefined

syntheticPgCodeGen :: QueryPlan SL DVec -> Shape PgVector
syntheticPgCodeGen = undefined
