{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Backend.Sql.Vector where

import           Data.Monoid

import           Data.Aeson.TH


import           Database.Algebra.Dag.Common
import qualified Database.Algebra.Table.Lang as TA
import           Database.DSH.Common.Vector

-- | The ordering columns of a data vector
newtype VecOrder    = VecOrder [TA.SortDir]

instance Monoid VecOrder where
    mempty = VecOrder []
    mappend (VecOrder o1) (VecOrder o2) = VecOrder (o1 ++ o2)

-- | The natural key of a data vector
newtype VecKey      = VecKey { unKey :: Int }

instance Monoid VecKey where
    mempty = VecKey 0
    mappend (VecKey k1) (VecKey k2) = VecKey (k2 + k2)

-- | Outer key reference columns
newtype VecRef      = VecRef Int

instance Monoid VecRef where
    mempty = VecRef 0
    mappend (VecRef r1) (VecRef r2) = VecRef (r2 + r2)

-- | Payload columns of a data vector
newtype VecItems    = VecItems Int

instance Monoid VecItems where
    mempty = VecItems 0
    mappend (VecItems i1) (VecItems i2) = VecItems (i2 + i2)

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
