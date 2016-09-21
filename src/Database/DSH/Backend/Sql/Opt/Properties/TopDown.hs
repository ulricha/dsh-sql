{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Backend.Sql.Opt.Properties.TopDown where

import           Control.Monad.State

import qualified Data.IntMap                                   as M
import qualified Data.IntSet                                   as IS
import           Data.List
import           Data.Maybe
import qualified Data.Set.Monad                                as S

import qualified Database.Algebra.Dag                          as D
import           Database.Algebra.Dag.Common
import           Database.Algebra.Table.Lang

import           Database.DSH.Backend.Sql.Opt.Properties.ICols
import           Database.DSH.Backend.Sql.Opt.Properties.Types
-- import           Database.DSH.Backend.Sql.Opt.Properties.Use
import           Database.DSH.Common.Impossible
import           Database.DSH.Common.Opt


seed :: TopDownProps
seed = TDProps { pICols = S.empty }

type InferenceState = NodeMap TopDownProps

lookupProps :: AlgNode -> State InferenceState TopDownProps
lookupProps n = do
    m <- get
    case M.lookup n m of
        Just props -> return props
        Nothing -> error "TopDown.lookupProps"

replaceProps :: AlgNode -> TopDownProps -> State InferenceState ()
replaceProps n p = modify (M.insert n p)

inferUnOp :: TopDownProps -> TopDownProps -> UnOp -> TopDownProps
inferUnOp ownProps cp op =
    TDProps { pICols = inferIColsUnOp (pICols ownProps) (pICols cp) op
            }

inferBinOp :: BottomUpProps
           -> BottomUpProps
           -> TopDownProps
           -> TopDownProps
           -> TopDownProps
           -> BinOp
           -> (TopDownProps, TopDownProps)
inferBinOp childBUProps1 childBUProps2 ownProps cp1 cp2 op =
  let (crc1', crc2') = inferIColsBinOp (pICols ownProps)
                                       (pICols cp1)
                                       (S.map fst $ pCols childBUProps1)
                                       (pICols cp2)
                                       (S.map fst $ pCols childBUProps2)
                                       op
      cp1' = TDProps { pICols = crc1' }
      cp2' = TDProps { pICols = crc2' }
  in (cp1', cp2')

inferChildProperties :: NodeMap BottomUpProps
                     -> D.AlgebraDag TableAlgebra
                     -> AlgNode
                     -> State InferenceState ()
inferChildProperties buPropMap d n = do
    ownProps <- lookupProps n
    case D.operator n d of
        NullaryOp _ -> return ()
        UnOp op c -> do
            cp <- lookupProps c
            let cp' = inferUnOp ownProps cp op
            replaceProps c cp'
        -- Special case: If both children refer to the same node, look up child
        -- properties only once.
        BinOp op c1 c2 | c1 == c2 -> do
            cp <- lookupProps c1
            let buProps = lookupUnsafe buPropMap "TopDown.inferChildProperties" c1
            let (cp1', cp2') = inferBinOp buProps buProps ownProps cp cp op
            replaceProps c1 (mergeTDProps cp1' cp2')
        BinOp op c1 c2 -> do
            cp1 <- lookupProps c1
            cp2 <- lookupProps c2
            let buProps1 = lookupUnsafe buPropMap "TopDown.inferChildProperties" c1
                buProps2 = lookupUnsafe buPropMap "TopDown.inferChildProperties" c2
            let (cp1', cp2') = inferBinOp buProps1 buProps2 ownProps cp1 cp2 op
            replaceProps c1 cp1'
            replaceProps c2 cp2'
        TerOp{} -> $impossible

-- | Infer properties during a top-down traversal.
inferAllProperties :: NodeMap BottomUpProps
                   -> [AlgNode]
                   -> D.AlgebraDag TableAlgebra
                   -> NodeMap AllProps
inferAllProperties buPropMap topOrderedNodes d =
    M.intersectionWith AllProps buPropMap tdPropMap
  where
    tdPropMap = execState action initialMap
    action = mapM_ (inferChildProperties buPropMap d) topOrderedNodes

    initialMap = M.map (const seed) $ D.nodeMap d
