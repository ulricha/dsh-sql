module Database.DSH.Backend.Sql.MultisetAlgebra.Opt
    ( optimizeMA
    , defaultPipeline
    ) where

import qualified Data.IntMap as M

import qualified Database.Algebra.Dag                              as Dag

import           Database.DSH.Common.Opt
import           Database.DSH.Common.QueryPlan

import           Database.DSH.Backend.Sql.MultisetAlgebra.Lang
import           Database.DSH.Backend.Sql.MultisetAlgebra.Opt.Rewrite
import           Database.DSH.Backend.Sql.Vector

--------------------------------------------------------------------------------

type MARewrite p = Rewrite MA (Shape MADVec) p

--------------------------------------------------------------------------------

noProps :: Monad m => m (M.IntMap a)
noProps = return M.empty

pullProjections :: MARewrite Bool
pullProjections = iteratively $ applyToAll noProps maRules

defaultPipeline :: [MARewrite Bool]
defaultPipeline = [pullProjections]

--------------------------------------------------------------------------------

-- | Apply a rewrite pipeline to a multiset plan
runPipeline :: Dag.AlgebraDag MA
            -> Shape MADVec
            -> [MARewrite Bool]
            -> Bool
            -> (Dag.AlgebraDag MA, Log, Shape MADVec)
runPipeline d sh pipeline debug = (d', rewriteLog, sh')
  where
    (d', sh', _, rewriteLog) = runRewrite (sequence_ pipeline) d sh debug

optimizeMA :: QueryPlan MA MADVec -> QueryPlan MA MADVec
optimizeMA plan =
#ifdef DEBUGGRAPH
  let (d, _rewriteLog, shape) = runPipeline (queryDag plan) (queryShape plan) defaultPipeline True
#else
  let (d, _rewriteLog, shape) = runPipeline (queryDag plan) (queryShape plan) defaultPipeline False
#endif
  in QueryPlan { queryDag = d, queryShape = shape, queryTags = M.empty }
