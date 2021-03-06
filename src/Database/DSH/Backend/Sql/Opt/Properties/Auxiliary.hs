-- | Some auxiliary functions for property inference.
module Database.DSH.Backend.Sql.Opt.Properties.Auxiliary where

import qualified Data.List                   as L
import qualified Data.Map                    as M
import qualified Data.Set.Monad              as S

import           Database.Algebra.Table.Lang

(∪) :: Ord a => S.Set a -> S.Set a -> S.Set a
(∪) = S.union

(∩) :: Ord a => S.Set a -> S.Set a -> S.Set a
(∩) = S.intersection

(∖) :: Ord a => S.Set a -> S.Set a -> S.Set a
(∖) = S.difference

(∈) :: Ord a => a -> S.Set a -> Bool
(∈) = S.member

(⊆) :: Ord a => S.Set a -> S.Set a -> Bool
(⊆) = S.isSubsetOf

-- | Singleton set abbreviation
ss :: Ord a => a -> S.Set a
ss = S.singleton

-- | List set abbreviation
ls :: Ord a => [a] -> S.Set a
ls = S.fromList

unionss :: Ord a => S.Set (S.Set a) -> S.Set a
unionss = S.foldr (∪) S.empty

exprCols :: Expr -> S.Set Attr
exprCols (BinAppE _ e1 e2)        = exprCols e1 ∪ exprCols e2
exprCols (TernaryAppE _ e1 e2 e3) = exprCols e1 ∪ exprCols e2 ∪ exprCols e3
exprCols (UnAppE _ e)             = exprCols e
exprCols (ColE c)                 = S.singleton c
exprCols (ConstE _)               = S.empty

aggrInput :: AggrType -> S.Set Attr
aggrInput (Avg e)           = exprCols e
aggrInput (Max e)           = exprCols e
aggrInput (Min e)           = exprCols e
aggrInput (Sum e)           = exprCols e
aggrInput (All e)           = exprCols e
aggrInput (Any e)           = exprCols e
aggrInput (Count e)         = exprCols e
aggrInput (CountDistinct e) = exprCols e
aggrInput CountStar         = S.empty

winFunInput :: WinFun -> S.Set Attr
winFunInput (WinAvg e)        = exprCols e
winFunInput (WinMax e)        = exprCols e
winFunInput (WinMin e)        = exprCols e
winFunInput (WinSum e)        = exprCols e
winFunInput (WinAll e)        = exprCols e
winFunInput (WinAny e)        = exprCols e
winFunInput (WinFirstValue e) = exprCols e
winFunInput (WinLastValue e)  = exprCols e
winFunInput WinCount          = S.empty

mapCol :: Proj -> Maybe (Attr, Attr)
mapCol (a, ColE b)                   = Just (a, b)
mapCol (a, UnAppE (Cast _) (ColE b)) = Just (a, b)
mapCol _                             = Nothing

-- | Build a map from a projection list that maps each attribute to
-- its new names after projection. Only attributes that are simply
-- renamed are considered.
mapColMulti :: [Proj] -> M.Map Attr (S.Set Attr)
mapColMulti = L.foldl' insertMap M.empty
  where
    insertMap m (a, ColE b)                   = M.insertWith S.union b (ss a) m
    insertMap m (a, UnAppE (Cast _) (ColE b)) = M.insertWith S.union b (ss a) m
    insertMap m _                             = m

mColE :: Expr -> Maybe Attr
mColE (ColE c) = Just c
mColE _        = Nothing
