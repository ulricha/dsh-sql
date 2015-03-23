{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Backend.Sql.Vector where

import qualified Data.List.NonEmpty          as N
import           Data.Aeson.TH


import           Database.Algebra.Dag.Common
import qualified Database.Algebra.Table.Lang as TA
import           Database.DSH.Common.Vector

-- | The ordering columns of a data vector
newtype VecOrder    = VecOrder (N.NonEmpty TA.SortDir)

-- | The natural key of a data vector
newtype VecKey      = VecKey Int

-- | Outer key reference columns
newtype VecRef      = VecRef (Maybe Int)

-- | Payload columns of a data vector
newtype VecItems    = VecItems (Maybe Int)

-- | Source columns of a transformation vector
newtype VecTransSrc = VecTransSrc Int

-- | Destination columns of a transformation vector
newtype VecTransDst = VecTransDst Int

data TADVec = TADVec AlgNode VecOrder VecKey VecRef VecItems

data TARVec = TARVec AlgNode VecTransSrc VecTransDst

data TAPVec = TAPVec AlgNode VecTransSrc VecTransDst

instance DagVector TADVec where
    vectorNodes (TADVec n _ _ _ _) = [n]

    updateVector n1 n2 (TADVec q o k r i)
        | q == n1   = TADVec n2 o k r i
        | otherwise = TADVec q o k r i

$(deriveJSON defaultOptions ''VecOrder)
$(deriveJSON defaultOptions ''VecKey)
$(deriveJSON defaultOptions ''VecRef)
$(deriveJSON defaultOptions ''VecItems)
$(deriveJSON defaultOptions ''VecTransSrc)
$(deriveJSON defaultOptions ''VecTransDst)
$(deriveJSON defaultOptions ''TADVec)
$(deriveJSON defaultOptions ''TARVec)
$(deriveJSON defaultOptions ''TAPVec)

--------------------------------------------------------------------------------
