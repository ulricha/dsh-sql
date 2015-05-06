{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE TemplateHaskell     #-}

module Database.DSH.Backend.Sql.Opt.Properties.Types where

import           Data.List
import qualified Data.Map                       as M
import qualified Data.Set.Monad                 as S
import           Database.Algebra.Table.Lang
import           Database.DSH.Common.Impossible

----------------------------------------------------------------------------
-- Property types

data TopDownProps = TDProps
    { pICols :: S.Set Attr
    }

instance Show TopDownProps where
    show ps = show $ S.toList (pICols ps)

-- FIXME: unite with Database.Algebra.Pathfinder....Data.Algebra.Key
type PKey = S.Set Attr

-- | Signal if an operator produces exactly one or zero tuples, respectively.
type Card1 = Bool
type Empty = Bool

type Orders = [(Attr, [Attr])]

type ConstCol = (Attr, AVal)

newtype FDSet = FDSet { fdsRep :: M.Map (S.Set Attr) (S.Set Attr) }

emptyFDSet :: FDSet
emptyFDSet = FDSet $ M.empty

showSet :: S.Set Attr -> String
showSet s = "{" ++ intercalate "," (S.toList s) ++ "}"

instance Show FDSet where
    show fds = intercalate ", "
               $ map (\(cs, ds) -> showSet cs ++ " -> " ++ showSet ds)
               $ M.toList $ fdsRep fds

data BottomUpProps = BUProps
    { pCols     :: S.Set TypedAttr
    , pKeys     :: S.Set PKey
    , pCard1    :: Card1
    , pEmpty    :: Empty
    , pOrder    :: Orders
    , pConst    :: [ConstCol]
    , pNullable :: S.Set Attr
    , pFunDeps  :: FDSet
    } deriving (Show)

data AllProps = AllProps
    { bu :: BottomUpProps
    , td :: TopDownProps
    } deriving (Show)

----------------------------------------------------------------------------
-- Utility functions on properties

typeOf :: Attr -> S.Set TypedAttr -> ATy
typeOf k s =
    case S.toList $ [ b | (a, b) <- s, k == a ] of
        [b] -> b
        _   -> $impossible
