-- | Quotation of Semantic Values back into Terms
module PosTT.Quotation where

import Data.Bifunctor (first)

import PosTT.Eval
import PosTT.Poset
import PosTT.Terms
import PosTT.Values


nf :: AtStage (Env -> Tm -> Tm)
nf ρ = readBack . eval ρ

normalize :: Env -> Tm -> Tm
normalize ρ t = bindStage terminalStage $ nf ρ t


--------------------------------------------------------------------------------
---- Read Back

instance ReadBack Val where
  type Quot Val = Tm

  readBack :: AtStage (Val -> Tm)
  readBack = \case
   VU                   -> U
   VPi a b              -> Pi (readBack a) (readBack b)
   VLam c               -> Lam (readBack c)
   VSigma a b           -> Sigma (readBack a) (readBack b)
   VPair u v            -> Pair (readBack u) (readBack v)
   VPath a a₀ a₁        -> Path (readBack a) (readBack a₀) (readBack a₁)
   VPLam c a₀ a₁        -> PLam (readBack c) (readBack a₀) (readBack a₁)
   VCoePartial r₀ r₁ c  -> Coe (readBack r₀) (readBack r₁) (readBack c)
   VCoe r₀ r₁ c u₀      -> readBack (VCoePartial r₀ r₁ c) `App` readBack u₀
   VHComp r₀ r₁ a u₀ s  -> HComp (readBack r₀) (readBack r₁) (readBack a) (readBack u₀) (readBack s)
   VExt a b             -> Ext (readBack a) (readBack b)
   VExtElm v us         -> ExtElm (readBack v) (readBack us)
   VSum d _             -> readBack d
   VCon c as            -> Con c (map readBack as)
   VSplitPartial f _    -> readBack f
   VHSum d _            -> readBack d
   VHCon c as is sys    -> HCon c (map readBack as) (map readBack is) (readBack sys)
   VHSplitPartial f _ _ -> readBack f
   VNeu k               -> readBack k

instance ReadBack Neu where
  type Quot Neu = Tm

  readBack :: AtStage (Neu -> Tm)
  readBack = \case
    NVar x                              -> Var x
    NApp k v                            -> readBack k `App` readBack v
    NPr1 v                              -> Pr1 (readBack v)
    NPr2 v                              -> Pr2 (readBack v)
    NPApp k a₀ a₁ r                     -> PApp (readBack k) (readBack a₀) (readBack a₁) (readBack r)
    NCoePartial r₀ r₁ c                 -> Coe (readBack r₀) (readBack r₁) (readBack c)
    NCoeSum r₀ r₁ i d lbl g k           -> readBack (VCoePartial r₀ r₁ (TrIntClosure i (VSum d lbl) g)) `App` readBack k
    NHComp r₀ r₁ k u₀ tb                -> HComp (readBack r₀) (readBack r₁) (readBack k) (readBack u₀) (readBack tb)
    NHCompSum r₀ r₁ d _ k tb            -> HComp (readBack r₀) (readBack r₁) (readBack d) (readBack k) (readBack tb)
    NNonConstHCompSum r₀ r₁ d _ c as tb -> HComp (readBack r₀) (readBack r₁) (readBack d) (readBack (VCon c as)) (readBack tb)
    NExtFun ws k                        -> ExtFun (readBack ws) (readBack k)
    NSplit f bs k                       -> readBack (VSplitPartial f bs) `App` readBack k
    NHSplit f a bs k                    -> readBack (VHSplitPartial f a bs) `App` readBack k

instance ReadBack v => ReadBack (VSys v) where
  type Quot (VSys v) = Sys (Quot v)

  readBack :: AtStage (VSys v -> Sys (Quot v))
  readBack sys = readBackSysCof (mapSys sys readBack)

readBackSysCof :: AtStage (VSys a -> Sys a)
readBackSysCof (VSys bs) = Sys (map (first readBack) bs)

instance ReadBack Closure where
  type Quot Closure = Binder Tm

  readBack :: AtStage (Closure -> Binder Tm)
  readBack cl@(Closure y _ _)  = refreshName y $ \x -> Binder x $ readBack $ cl $$ VVar x

instance ReadBack IntClosure where
  type Quot IntClosure = IntBinder Tm

  readBack :: AtStage (IntClosure -> IntBinder Tm)
  readBack cl@(IntClosure i _ _)  = refreshGen i $ \j -> IntBinder j $ readBack $ cl $$ iVar j

instance ReadBack TrIntClosure where
  type Quot TrIntClosure = TrIntBinder Tm

  readBack :: AtStage (TrIntClosure -> TrIntBinder Tm)
  readBack cl@(TrIntClosure i _ _)  = refreshGen i $ \j -> TrIntBinder j $ readBack $ cl $$ iVar j

instance ReadBack TrNeuIntClosure where
  type Quot TrNeuIntClosure = TrIntBinder Tm

  readBack :: AtStage (TrNeuIntClosure -> TrIntBinder Tm)
  readBack cl@(TrNeuIntClosure i _)  = refreshGen i $ \j -> TrIntBinder j $ readBack $ cl $$ iVar j

instance (ReadBack a, ReadBack b, ReadBack c) => ReadBack (a, b, c) where
  type Quot (a, b, c) = (Quot a, Quot b, Quot c)

  readBack :: AtStage ((a, b, c) -> (Quot a, Quot b, Quot c))
  readBack (a, b, c) = (readBack a, readBack b, readBack c)
