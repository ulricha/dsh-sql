{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE FlexibleContexts #-}

module Database.DSH.Backend.Sql.Opt.Properties.BottomUp where

import           Control.Monad.Except
import qualified Data.Set.Monad                                   as S
import qualified Data.IntMap                                      as IM
import           Text.Printf

import           Database.Algebra.Dag
import           Database.Algebra.Dag.Common
import           Database.Algebra.Table.Lang
import           Database.Algebra.Table.Typing

import           Database.DSH.Common.Impossible
import           Database.DSH.Common.Opt

import           Database.DSH.Backend.Sql.Opt.Properties.Card1
import           Database.DSH.Backend.Sql.Opt.Properties.Const
import           Database.DSH.Backend.Sql.Opt.Properties.Empty
import           Database.DSH.Backend.Sql.Opt.Properties.FD
import           Database.DSH.Backend.Sql.Opt.Properties.Keys
import           Database.DSH.Backend.Sql.Opt.Properties.Nullable
import           Database.DSH.Backend.Sql.Opt.Properties.Order
import           Database.DSH.Backend.Sql.Opt.Properties.Types

opProps :: MonadError String m => AlgNode -> NodeMap p -> m p
opProps n m =
    case IM.lookup n m of
        Just p  -> pure p
        Nothing -> throwError $ printf "BottomUp.opProps: no properties for node %d" n

inferWorker :: MonadError String m => NodeMap TableAlgebra -> TableAlgebra -> AlgNode -> NodeMap BottomUpProps -> m BottomUpProps
inferWorker om o n pm = inferOp om o pm `catchError` augmentMsg
  where
    augmentMsg msg = throwError $ printf "BottomUp.inferWorker: inference failed at node %d:\n%s" n msg

inferOp :: MonadError String m => NodeMap TableAlgebra -> TableAlgebra -> NodeMap BottomUpProps -> m BottomUpProps
inferOp _ op pm =
    case op of
         TerOp{}        -> $impossible
         BinOp vl c1 c2 -> do
             c1Props <- opProps c1 pm
             c2Props <- opProps c2 pm
             inferBinOp vl c1Props c2Props
         UnOp vl c      -> do
             cProps <- opProps c pm
             inferUnOp vl cProps
         NullaryOp vl   -> inferNullOp vl

inferNullOp :: MonadError String m => NullOp -> m BottomUpProps
inferNullOp op = do
  opCols <- tyNullOp op
  let opKeys     = inferKeysNullOp op
      opEmpty    = inferEmptyNullOp op
      opCard1    = inferCard1NullOp op
      -- We only care for rownum-generated columns. Therefore, For
      -- nullary operators order is empty.
      opOrder    = []
      opConst    = inferConstNullOp op
      opNullable = inferNullableNullOp op
      opFDs      = inferFDNullOp opCols opKeys op
  return BUProps { pCols     = opCols
                 , pKeys     = opKeys
                 , pEmpty    = opEmpty
                 , pCard1    = opCard1
                 , pOrder    = opOrder
                 , pConst    = opConst
                 , pNullable = opNullable
                 , pFunDeps  = opFDs
                 }

inferUnOp :: MonadError String m => UnOp -> BottomUpProps -> m BottomUpProps
inferUnOp op cProps = do
  opCols <- tyUnOp (pCols cProps) op
  let opKeys     = inferKeysUnOp (pKeys cProps) (pCard1 cProps) (S.map fst $ pCols cProps) op
      opEmpty    = inferEmptyUnOp (pEmpty cProps) op
      opCard1    = inferCard1UnOp (pCard1 cProps) (pEmpty cProps) op
      opOrder    = inferOrderUnOp (pOrder cProps) op
      opConst    = inferConstUnOp (pConst cProps) op
      opNullable = inferNullableUnOp (pNullable cProps) op
      opFDs      = inferFDUnOp cProps op
  return BUProps { pCols     = opCols
                 , pKeys     = opKeys
                 , pEmpty    = opEmpty
                 , pCard1    = opCard1
                 , pOrder    = opOrder
                 , pConst    = opConst
                 , pNullable = opNullable
                 , pFunDeps  = opFDs
                 }

inferBinOp :: MonadError String m => BinOp -> BottomUpProps -> BottomUpProps -> m BottomUpProps
inferBinOp op c1Props c2Props = do
  opCols <- tyBinOp (pCols c1Props) (pCols c2Props) op
  let opKeys     = inferKeysBinOp (pKeys c1Props) (pKeys c2Props) (pCard1 c1Props) (pCard1 c2Props) op
      opEmpty    = inferEmptyBinOp (pEmpty c1Props) (pEmpty c2Props) op
      opCard1    = inferCard1BinOp (pCard1 c1Props) (pCard1 c2Props) op
      opOrder    = inferOrderBinOp (pOrder c1Props) (pOrder c2Props) op
      opConst    = inferConstBinOp (pConst c1Props) (pConst c2Props) op
      opNullable = inferNullableBinOp c1Props c2Props op
      opFDs      = inferFDBinOp c1Props c2Props opKeys opCols op
  return BUProps { pCols     = opCols
                 , pKeys     = opKeys
                 , pEmpty    = opEmpty
                 , pCard1    = opCard1
                 , pOrder    = opOrder
                 , pConst    = opConst
                 , pNullable = opNullable
                 , pFunDeps  = opFDs
                 }

inferBottomUpProperties :: AlgebraDag TableAlgebra -> NodeMap BottomUpProps
inferBottomUpProperties dag =
    case inferBottomUpE inferWorker dag of
        Left msg -> error msg
        Right props -> props
