{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Backend.Sql.Vector where

import qualified Data.List.NonEmpty          as N
import           Data.Aeson.TH

import           Database.Algebra.Dag.Common
import qualified Database.Algebra.Table.Lang as TA
import           Database.DSH.Common.Vector

newtype OrdCol  = OrdCol (TA.Attr, TA.SortDir)
newtype KeyCol  = KeyCol TA.Attr
newtype ItemCol = ItemCol TA.Attr

type VecOrder = N.NonEmpty OrdCol
type VecKey   = N.NonEmpty KeyCol
type VecRef   = Maybe (N.NonEmpty KeyCol)
type VecItems = [ItemCol]

data TAVec = TAVec AlgNode VecOrder VecKey VecRef VecItems

instance DagVector TAVec where
    vectorNodes (TAVec n _ _ _ _) = [n]

    updateVector n1 n2 (TAVec q o k r i)
        | q == n1   = TAVec n2 o k r i
        | otherwise = TAVec q o k r i

$(deriveJSON defaultOptions ''OrdCol)
$(deriveJSON defaultOptions ''KeyCol)
$(deriveJSON defaultOptions ''ItemCol)
$(deriveJSON defaultOptions ''TAVec)

--------------------------------------------------------------------------------
