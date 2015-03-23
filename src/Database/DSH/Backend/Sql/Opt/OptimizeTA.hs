module Database.DSH.Backend.Sql.Opt.OptimizeTA where

import qualified Data.IntMap as M

import qualified Database.Algebra.Dag                              as Dag
import           Database.Algebra.Table.Lang

import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Vector

import           Database.DSH.Common.Opt
import           Database.DSH.Backend.Sql.Opt.Rewrite.Basic

type RewriteClass = Rewrite TableAlgebra (Shape NDVec) Bool

defaultPipeline :: [RewriteClass]
defaultPipeline = [cleanup]

runPipeline :: Dag.AlgebraDag TableAlgebra
            -> (Shape NDVec)
            -> [RewriteClass]
            -> Bool
            -> (Dag.AlgebraDag TableAlgebra, Log, Shape NDVec)
runPipeline d sh pipeline debug = (d', rewriteLog, sh')
  where (d', sh', _, rewriteLog) = runRewrite (sequence_ pipeline) d sh debug

optimizeTA :: QueryPlan TableAlgebra NDVec -> QueryPlan TableAlgebra NDVec
optimizeTA plan =
#ifdef DEBUGGRAPH
  let (d, _rewriteLog, shape) = runPipeline (queryDag plan) (queryShape plan) defaultPipeline True
#else
  let (d, _rewriteLog, shape) = runPipeline (queryDag plan) (queryShape plan) defaultPipeline False
#endif
  in QueryPlan { queryDag = d, queryShape = shape, queryTags = M.empty }
