module Database.DSH.Backend.Sql.Unordered
    (
    ) where

import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Vector
import qualified Database.DSH.SL                               as SL
import qualified Database.DSH.VSL                              as VSL

import           Database.DSH.Backend.Sql.MultisetAlgebra.Lang
import           Database.DSH.Backend.Sql.Vector

type MAPlanGen v = QueryPlan v DVec -> QueryPlan MA MADVec
