module PosTT.HeadLinearReduction where

import           Data.Tuple.Extra (first)

import           PosTT.Common
import           PosTT.Eval
import           PosTT.Quotation ()
import           PosTT.Poset
import           PosTT.Terms
import           PosTT.Values


headUnfold :: Env -> Tm -> Maybe Int -> ([Name], Tm)
headUnfold δ = go
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

    go :: Tm -> Maybe Int -> ([Name], Tm)
    go t (Just 0) = ([], t)
    go t steps    = case unfold t of
      Nothing      -> ([], t)
      Just (d, t') -> first (d:) $ go t' (pred <$> steps)


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
  VNeu n             -> Just (singleReductionNeu δ n) -- a neutral always makes progess, when we unfold something
  VCon c [a]         -> (fmap . fmap) (VCon c . return) (singleReduction δ a)
  VHCon c [a] is bs  -> (fmap . fmap) (\a' -> VHCon c [a'] is bs) (singleReduction δ a)
  _                  -> Nothing

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
  -- by cubical cannonicity, at least one of the entries in the tube is neutral
  NNonConstHCompSum r₀ r₁ d lbl c as tb -> doHComp r₀ r₁ (VSum d lbl) (VCon c as) <$> singleReductionSysTrIntClosure δ tb

singleReductionSysTrIntClosure :: AtStage (AtStage (Name -> Val) -> VSys TrIntClosure -> (Name, VSys TrIntClosure))
singleReductionSysTrIntClosure δ (VSys sys) = VSys <$> go sys
  where
    go :: [(VCof, TrIntClosure)] -> (Name, [(VCof, TrIntClosure)])
    go ((φ, c):bs) = case extCof φ (stepCl c) of
      Left (n, c') -> (n, (φ,c'):bs)
      Right c'     -> ((φ,c'):) <$> go bs
    go [] = impossible "No branch was neutral! The system should have been reduced!"

    stepCl :: AtStage (TrIntClosure -> Either (Name, TrIntClosure) TrIntClosure)
    stepCl (force -> c) = case c of
      -- We have to inline some things to extract the name; change to more flexible closre representation?
      TrIntClosure i (VNeu k) _ ->
        let (i', (x, k'')) = refreshGen i $ \i' -> (i',) $ case k @ (iVar i' `for` i) of
              VNeu k'                  -> singleReductionNeu δ k'
              _renamingForcedReduction -> impossible "Renaming a variable to a fresh name forced a reduction!"
        in  Left (x, TrIntClosure i' k'' IdRestr)
      TrIntClosure _ (VCon _ _) _ -> Right c
      _nonConValue -> impossible "A closed term of sum type with blocked variables is neither neutral nor constructor"

singleReductionTrNeuIntClosure :: AtStage (AtStage (Name -> Val) -> TrNeuIntClosure -> (Name, TrIntClosure))
singleReductionTrNeuIntClosure δ (TrNeuIntClosure i k) =
  refreshGen i $ \i' -> (\t -> TrIntClosure i' t IdRestr) <$> singleReductionNeu δ k
