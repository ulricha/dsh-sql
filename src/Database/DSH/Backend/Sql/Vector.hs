{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Backend.Sql.Vector where

import           Data.Aeson.TH
import           Data.Aeson

import           Database.Algebra.Dag.Common
import qualified Database.Algebra.Table.Lang as TA
import           Database.DSH.Common.Vector

--------------------------------------------------------------------------------

-- | The ordering columns of a data vector
newtype VecOrder    = VecOrder [TA.SortDir]

unOrd :: VecOrder -> Int
unOrd (VecOrder os) = length os

instance Monoid VecOrder where
    mempty = VecOrder []
    mappend (VecOrder o1) (VecOrder o2) = VecOrder (o1 ++ o2)

--------------------------------------------------------------------------------

-- | The natural key of a data vector
newtype VecKey      = VecKey { unKey :: Int }

instance Monoid VecKey where
    mempty = VecKey 0
    mappend (VecKey k1) (VecKey k2) = VecKey (k1 + k2)

instance ToJSON VecKey where
    toJSON (VecKey ks) = toJSON [ "k" ++ show k | k <- [1..ks] ]

--------------------------------------------------------------------------------

-- | Outer key reference columns
newtype VecRef      = VecRef { unRef :: Int }

-- FIXME use rc constructor
instance ToJSON VecRef where
    toJSON (VecRef rs) = toJSON [ "r" ++ show r | r <- [1..rs] ]

-- | Derive inner references from an outer key.
keyRef :: VecKey -> VecRef
keyRef (VecKey i) = VecRef i

instance Monoid VecRef where
    mempty = VecRef 0
    mappend (VecRef r1) (VecRef r2) = VecRef (r1 + r2)

--------------------------------------------------------------------------------

-- | Payload columns of a data vector
newtype VecItems    = VecItems { unItems :: Int }

instance Monoid VecItems where
    mempty = VecItems 0
    mappend (VecItems i1) (VecItems i2) = VecItems (i1 + i2)

instance ToJSON VecItems where
    toJSON (VecItems is) = toJSON [ "i" ++ show i | i <- [1..is] ]

--------------------------------------------------------------------------------

-- | Source columns of a transformation vector
newtype VecTransSrc = VecTransSrc { unSrc :: Int }

-- | Destination columns of a transformation vector
newtype VecTransDst = VecTransDst { unDst :: Int }

--------------------------------------------------------------------------------

-- | Key columns of a filter vector
newtype VecFilter = VecFilter Int

--------------------------------------------------------------------------------

-- | A data vector that references a table algebra plan
data TADVec = TADVec AlgNode VecOrder VecKey VecRef VecItems

-- | A rekeying vector that references a table algebra plan
data TAKVec = TAKVec AlgNode VecTransSrc VecTransDst

-- | A renaming vector that references a table algebra plan
data TARVec = TARVec AlgNode VecTransSrc VecTransDst

-- | Sorting of segments is a NOOP in the natural key backend.
data TASVec = TASVec

-- | A filtering vector that references a table algebra plan
data TAFVec = TAFVec AlgNode VecFilter

instance DagVector TADVec where
    vectorNodes (TADVec n _ _ _ _) = [n]

    updateVector n1 n2 (TADVec q o k r i)
        | q == n1   = TADVec n2 o k r i
        | otherwise = TADVec q o k r i

--------------------------------------------------------------------------------

$(deriveToJSON defaultOptions ''VecOrder)
$(deriveToJSON defaultOptions ''VecTransSrc)
$(deriveToJSON defaultOptions ''VecTransDst)
$(deriveToJSON defaultOptions ''TADVec)
$(deriveToJSON defaultOptions ''TAKVec)
$(deriveToJSON defaultOptions ''TARVec)

--------------------------------------------------------------------------------
