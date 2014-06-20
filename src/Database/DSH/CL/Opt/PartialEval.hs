{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE LambdaCase     #-}
    
-- | Support rewrites (partial evaluation, house cleaning)
module Database.DSH.CL.Opt.PartialEval
  ( partialEvalR
  ) where
  
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Kure

--------------------------------------------------------------------------------
-- Partial evaluation rules

-- | Eliminate tuple construction if the elements are first and second of the
-- same tuple:
-- pair (fst x) (snd x) => x
pairR :: RewriteC CL
pairR = do
    ExprCL (AppE2 _ (Prim2 Pair _) 
                    (AppE1 _ (Prim1 Fst _) v@(Var _ x)) 
                    (AppE1 _ (Prim1 Snd _) (Var _ x'))) <- idR
    guardM $ x == x'
    return $ inject v

fstR :: RewriteC CL
fstR = do
    ExprCL (AppE1 _ (Prim1 Fst _) (AppE2 _ (Prim2 Pair _) e1 _)) <- idR
    return $ inject e1

sndR :: RewriteC CL
sndR = do
    ExprCL (AppE1 _ (Prim1 Snd _) (AppE2 _ (Prim2 Pair _) _ e2)) <- idR
    return $ inject e2
    
partialEvalR :: RewriteC CL
partialEvalR = 
    readerT $ \case
        ExprCL AppE1{} -> fstR <+ sndR
        ExprCL AppE2{} -> pairR
        _                    -> fail "can't apply partial evaluation rules"