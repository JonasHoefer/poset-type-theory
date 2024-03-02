module PosTT.HeadLinearReduction where

import           Control.Applicative

import qualified Data.Map as M

import           PosTT.Common
import           PosTT.Eval
import           PosTT.Quotation ()
import           PosTT.Terms
import           PosTT.Values


headUnfold :: Env -> Tm -> Maybe Int -> (M.Map Name Int, Tm)
headUnfold δ = go M.empty
  where
    ρ  = blockedEnv δ
    -- s  = foldr sExtName terminalStage (blockedNames δ)

    -- TODO: wrong, the stage handling seems more complicated
    unfold :: Tm -> Maybe (Name, Tm)
    unfold t = bindStage terminalStage $ (fmap . fmap) readBack $ singleReduction δ $ eval ρ t

    go :: M.Map Name Int -> Tm -> Maybe Int -> (M.Map Name Int, Tm)
    go u t (Just 0) = (u, t)
    go u t s        = case unfold t of
      Nothing      -> (u, t)
      Just (d, t') -> go (M.alter (\e -> fmap succ e <|> Just 1) d u) t' (pred <$> s)


--------------------------------------------------------------------------------
---- Setup blocked environment

isSplit :: Tm -> Bool
isSplit = \case
  Split _ _ -> True
  BLam _ t  -> isSplit t
  _         -> False

blockedEnv :: Env -> Env
blockedEnv = \case
  EmptyEnv       -> EmptyEnv
  EnvFib ρ x _   -> EnvFib (blockedEnv ρ) x (VVar x)
  EnvDef ρ x s _ | not (isSplit s) -> EnvFib (blockedEnv ρ) x (VVar x)
  EnvCons ρ x e  -> EnvCons (blockedEnv ρ) x e

blockedNames :: Env -> [Name]
blockedNames = \case
  EmptyEnv       -> []
  EnvFib ρ x _   -> x:blockedNames ρ
  EnvDef ρ x s _ | not (isSplit s) -> x:blockedNames ρ
  EnvCons ρ _ _  -> blockedNames ρ


--------------------------------------------------------------------------------
---- Single unfold steps

singleReduction :: AtStage (Env -> Val -> Maybe (Name, Val))
singleReduction δ = \case
  VNeu n     -> Just (singleReductionNeu δ n) -- a neutral always makes progess, when we unfold something
  VCon c [a] -> (fmap . fmap) (VCon c . return) (singleReduction δ a)
  _          -> Nothing

singleReductionNeu :: AtStage (Env -> Neu -> (Name, Val))
singleReductionNeu δ = \case
  NVar x                     -> (x, δ `lookupFib` x)
  NApp k v                   -> (`doApp` v) <$> singleReductionNeu δ k
  NPr1 k                     -> doPr1 <$> singleReductionNeu δ k
  NPr2 k                     -> doPr2 <$> singleReductionNeu δ k
  NPApp k a₀ a₁ r            -> (\v -> doPApp v a₀ a₁ r) <$> singleReductionNeu δ k
  NCoePartial r₀ r₁ c        -> doCoePartial r₀ r₁ <$> singleReductionTrNeuIntClosure δ c
  NHComp r₀ r₁ k u₀ tb       -> (\t -> doHComp r₀ r₁ t u₀ tb) <$> singleReductionNeu δ k
  NExtFun ws k               -> doExtFun ws <$> singleReductionNeu δ k
  NHCompSum r₀ r₁ d lbl k tb -> (\v -> doHCompSum r₀ r₁ d lbl v tb) <$> singleReductionNeu δ k
  NSplit f bs k              -> doSplit f bs <$> singleReductionNeu δ k

singleReductionTrNeuIntClosure :: AtStage (Env -> TrNeuIntClosure -> (Name, TrIntClosure))
singleReductionTrNeuIntClosure δ (TrNeuIntClosure i k) =
  refreshGen i $ \i' -> (\t -> TrIntClosure i' t IdRestr) <$> singleReductionNeu δ k
