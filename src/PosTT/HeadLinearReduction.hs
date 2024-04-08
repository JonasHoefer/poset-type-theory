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
    ρ = blockedEnv δ
    s = foldr sExtName terminalStage (blockedNames δ)

    blockedLookup :: AtStage (Name -> Val)
    blockedLookup x = case lookup x δ of
      Just (EntryFib v)   -> v
      Just (EntryDef t _) -> eval (dropWhile ((/= x) . fst) ρ) t
      _                   -> impossible "Lookup of non-fibrant variable"

    -- The stage reserves too many names.
    -- Formally, singleReduction frees up one name, which we could remove.
    unfold :: Tm -> Maybe (Name, Tm)
    unfold t = bindStage s $ (fmap . fmap) readBack
      $ singleReduction blockedLookup $ eval ρ t

    go :: M.Map Name Int -> Tm -> Maybe Int -> (M.Map Name Int, Tm)
    go u t (Just 0) = (u, t)
    go u t steps    = case unfold t of
      Nothing      -> (u, t)
      Just (d, t') -> go (M.alter (\e -> fmap succ e <|> Just 1) d u) t' (pred <$> steps)


--------------------------------------------------------------------------------
---- Setup blocked environment

isSplitOrSum :: Tm -> Bool
isSplitOrSum = \case
  Split _ _ -> True
  Sum _ _   -> True
  HSplit{}  -> True
  HSum{}    -> True
  BLam _ t  -> isSplitOrSum t
  _         -> False

blockedEnv :: Env -> Env
blockedEnv = \case
  EmptyEnv       -> EmptyEnv
  EnvFib ρ x _   -> EnvFib (blockedEnv ρ) x (VVar x)
  EnvDef ρ x s _ | not (isSplitOrSum s) -> EnvFib (blockedEnv ρ) x (VVar x)
  EnvCons ρ x e  -> EnvCons (blockedEnv ρ) x e

blockedNames :: Env -> [Name]
blockedNames = \case
  EmptyEnv       -> []
  EnvFib ρ x _   -> x:blockedNames ρ
  EnvDef ρ x s _ | not (isSplitOrSum s) -> x:blockedNames ρ
  EnvCons ρ _ _  -> blockedNames ρ


--------------------------------------------------------------------------------
---- Single unfold steps

singleReduction :: AtStage (AtStage (Name -> Val) -> Val -> Maybe (Name, Val))
singleReduction δ = \case
  VNeu n     -> Just (singleReductionNeu δ n) -- a neutral always makes progess, when we unfold something
  VCon c [a] -> (fmap . fmap) (VCon c . return) (singleReduction δ a)
  _          -> Nothing

singleReductionNeu :: AtStage (AtStage (Name -> Val) -> Neu -> (Name, Val))
singleReductionNeu δ = \case
  NVar x                     -> (x, δ x)
  NApp k v                   -> (`doApp` v) <$> singleReductionNeu δ k
  NPr1 k                     -> doPr1 <$> singleReductionNeu δ k
  NPr2 k                     -> doPr2 <$> singleReductionNeu δ k
  NPApp k a₀ a₁ r            -> (\v -> doPApp v a₀ a₁ r) <$> singleReductionNeu δ k
  NCoePartial r₀ r₁ c        -> doCoePartial r₀ r₁ <$> singleReductionTrNeuIntClosure δ c
  NHComp r₀ r₁ k u₀ tb       -> (\t -> doHComp r₀ r₁ t u₀ tb) <$> singleReductionNeu δ k
  NExtFun ws k               -> doExtFun ws <$> singleReductionNeu δ k
  NCoeSum r₀ r₁ i d lbl f k  -> doCoeSum r₀ r₁ i d lbl f <$> singleReductionNeu δ k
  NCoeHSum r₀ r₁ i d lbl f k -> doCoeHSum r₀ r₁ i d lbl f <$> singleReductionNeu δ k
  NHCompSum r₀ r₁ d lbl k tb -> (\v -> doHCompSum r₀ r₁ d lbl v tb) <$> singleReductionNeu δ k
  NSplit f bs k              -> doSplit f bs <$> singleReductionNeu δ k
  NHSplit f d bs k           -> doHSplit f d bs <$> singleReductionNeu δ k
  NNonConstHCompSum{}        -> impossible "Non-constant tubes for HComp in sum type during closed evaluation"

singleReductionTrNeuIntClosure :: AtStage (AtStage (Name -> Val) -> TrNeuIntClosure -> (Name, TrIntClosure))
singleReductionTrNeuIntClosure δ (TrNeuIntClosure i k) =
  refreshGen i $ \i' -> (\t -> TrIntClosure i' t IdRestr) <$> singleReductionNeu δ k
