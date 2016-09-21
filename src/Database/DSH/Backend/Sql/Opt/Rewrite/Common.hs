module Database.DSH.Backend.Sql.Opt.Rewrite.Common where

import qualified Data.IntMap                                   as M

import           Database.Algebra.Dag.Common
import           Database.Algebra.Table.Lang

import           Database.DSH.Backend.Sql.Vector
import           Database.DSH.Common.QueryPlan
import qualified Database.DSH.Common.Opt as R

import           Database.DSH.Backend.Sql.Opt.Properties.BottomUp
import           Database.DSH.Backend.Sql.Opt.Properties.TopDown
import           Database.DSH.Backend.Sql.Opt.Properties.Types

  -- Type abbreviations for convenience
type TARewrite p = R.Rewrite TableAlgebra (Shape TADVec) p
type TARule p = R.Rule TableAlgebra p (Shape TADVec)
type TARuleSet p = R.RuleSet TableAlgebra  p (Shape TADVec)
type TAMatch p = R.Match TableAlgebra p (Shape TADVec)

inferBottomUp :: TARewrite (NodeMap BottomUpProps)
inferBottomUp = do
    to <- R.topsort
    R.infer $ inferBottomUpProperties to

inferAll :: TARewrite (NodeMap AllProps)
inferAll = do
  to        <- R.topsort
  buPropMap <- R.infer $ inferBottomUpProperties to
  R.infer (inferAllProperties buPropMap to)

noProps :: Monad m => m (M.IntMap a)
noProps = return M.empty
