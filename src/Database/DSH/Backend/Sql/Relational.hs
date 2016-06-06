-- | Implement vector operator plans with relational algebra operators.
module Database.DSH.Backend.Sql.Relational
    ( RelPlanGen
    , naturalKeyVectors
    , syntheticKeyVectors
    , virtualVectors
    , module Database.DSH.Backend.Sql.Opt.OptimizeTA
    ) where

import qualified Database.Algebra.Dag                          as D
import qualified Database.Algebra.Dag.Build                    as B
import qualified Database.Algebra.Table.Lang                   as TA

import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Vector
import qualified Database.DSH.SL                               as SL
import qualified Database.DSH.VSL                              as VSL

import           Database.DSH.Backend.Sql.Opt.OptimizeTA       (optimizeTA)
import           Database.DSH.Backend.Sql.Relational.Natural   ()
import           Database.DSH.Backend.Sql.Relational.Synthetic ()
import           Database.DSH.Backend.Sql.Relational.Virtual   ()
import           Database.DSH.Backend.Sql.Serialize
import           Database.DSH.Backend.Sql.Vector

type RelPlanGen v = QueryPlan v DVec -> QueryPlan TA.TableAlgebra TADVec

-- | Lower a SL vector operator plan to relational algebra based on composite
-- natural keys.
naturalKeyVectors :: RelPlanGen SL.SL
naturalKeyVectors vlPlan = mkQueryPlan dag shape tagMap
  where
    taPlan               = SL.vl2Algebra (D.nodeMap $ queryDag vlPlan)
                                      (queryShape vlPlan)
    serializedPlan       = insertSerialize taPlan
    (dag, shape, tagMap) = B.runBuild serializedPlan

syntheticKeyVectors :: RelPlanGen SL.SL
syntheticKeyVectors = undefined

-- | Lower a VSL vector operator plan with virtual segments to relational
-- algebra based on composite natural keys.
virtualVectors :: RelPlanGen VSL.VSL
virtualVectors vlPlan = mkQueryPlan dag shape tagMap
  where
    taPlan               = VSL.vl2Algebra (D.nodeMap $ queryDag vlPlan)
                                          (queryShape vlPlan)
    serializedPlan       = insertSerialize taPlan
    (dag, shape, tagMap) = B.runBuild serializedPlan
