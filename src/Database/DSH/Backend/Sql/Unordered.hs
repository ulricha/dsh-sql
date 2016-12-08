module Database.DSH.Backend.Sql.Unordered
    ( naturalIndexVectors
    ) where

import qualified Database.Algebra.Dag                          as D
import qualified Database.Algebra.Dag.Build                    as B

import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Vector
import qualified Database.DSH.SL                               as SL

import           Database.DSH.Backend.Sql.MultisetAlgebra.Lang
import           Database.DSH.Backend.Sql.Unordered.Natural    ()
import           Database.DSH.Backend.Sql.Vector

type MAPlanGen v = QueryPlan v DVec -> QueryPlan MA MADVec

-- | Lower a SL vector operator plan to multiset algebra based on composite
-- natural keys.
naturalIndexVectors :: MAPlanGen SL.TSL
naturalIndexVectors vlPlan = mkQueryPlan dag shape tagMap
  where
    maPlan               = SL.vl2Algebra (D.nodeMap $ queryDag vlPlan)
                                         (queryShape vlPlan)
    (dag, shape, tagMap) = B.runBuild maPlan
