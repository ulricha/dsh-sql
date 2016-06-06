module Database.DSH.Backend.Sql.Common
    ( SqlVector(..)
    , SqlCode(..)
    ) where

import qualified Data.Vector                     as V

import qualified Database.Algebra.Table.Lang              as TA

import           Database.DSH.Common.Vector
import           Database.DSH.Common.QueryPlan

import           Database.DSH.Backend.Sql.Vector

class SqlCode c where
    genSqlCode :: QueryPlan TA.TableAlgebra TADVec -> Shape (SqlVector c)
