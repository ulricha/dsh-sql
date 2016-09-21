{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE BangPatterns        #-}

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

mergeTDProps :: TopDownProps -> TopDownProps -> TopDownProps
mergeTDProps (TDProps ics1) (TDProps ics2) = TDProps (S.union ics1 ics2)

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
emptyFDSet = FDSet M.empty

showSet :: Ord a => (a -> String) -> S.Set a -> String
showSet f s = "{" ++ intercalate "," (map f $ S.toList s) ++ "}"

instance Show FDSet where
    show fds = intercalate ", "
               $ map (\(cs, ds) -> showSet id cs ++ " -> " ++ showSet id ds)
               $ M.toList $ fdsRep fds

data BottomUpProps = BUProps
    { pCols     :: S.Set TypedAttr
    , pKeys     :: S.Set PKey
    , pCard1    :: {-# UNPACK #-} !Card1
    , pEmpty    :: {-# UNPACK #-} !Empty
    , pOrder    :: !Orders
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
    case S.toList [ b | (a, b) <- s, k == a ] of
        [b] -> b
        _   -> $impossible
