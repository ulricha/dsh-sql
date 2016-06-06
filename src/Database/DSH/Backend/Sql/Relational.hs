-- | Implement vector operator plans with relational algebra operators.
module Database.DSH.Backend.Sql.Relational
    ( RelPlanGen
    , naturalKeyVectors
    , syntheticKeyVectors
    , virtualVectors
    ) where

import qualified Database.Algebra.Dag                          as D
import qualified Database.Algebra.Table.Lang                   as TA

import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Vector
import           Database.DSH.SL
import           Database.DSH.VSL

import           Database.DSH.Backend.Sql.Relational.Natural   ()
import           Database.DSH.Backend.Sql.Relational.Synthetic ()
import           Database.DSH.Backend.Sql.Relational.Virtual   ()
import           Database.DSH.Backend.Sql.Serialize
import           Database.DSH.Backend.Sql.Vector

type RelPlanGen v = QueryPlan v DVec -> QueryPlan TA.TableAlgebra TADVec

relationalPlan :: QueryPlan v DVec -> QueryPlan TA.TableAlgebra TADVec
relationalPlan vlPlan = mkQueryPlan dag shape tagMap
  where
    taPlan               = vl2Algebra (D.nodeMap $ queryDag vlPlan)
                                      (queryShape vlPlan)
    serializedPlan       = insertSerialize taPlan
    (dag, shape, tagMap) = runVecBuild serializedPlan

-- | Lower a SL vector operator plan to relational algebra based on composite
-- natural keys.
naturalKeyVectors :: RelPlanGen SL
naturalKeyVectors vlPlan = relationalPlan vlPlan

syntheticKeyVectors :: RelPlanGen SL
syntheticKeyVectors = undefined

-- | Lower a VSL vector operator plan with virtual segments to relational
-- algebra based on composite natural keys.
virtualVectors :: RelPlanGen VSL
virtualVectors = undefined
