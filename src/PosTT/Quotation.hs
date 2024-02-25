-- | Quotation of Semantic Values back into Terms
module PosTT.Quotation where

import PosTT.Eval
import PosTT.Terms
import PosTT.Values


--------------------------------------------------------------------------------
---- Read Back

instance ReadBack Val where
  type Quot Val = Tm

  readBack :: AtStage (Val -> Tm)
  readBack = \case
   VU                  -> U
   VPi a b             -> Pi (readBack a) (readBack b)
   VLam c              -> Lam (readBack c)
   VSigma a b          -> Sigma (readBack a) (readBack b)
   VPair u v           -> Pair (readBack u) (readBack v)
   VPath a a₀ a₁       -> Path (readBack a) (readBack a₀) (readBack a₁)
   VPLam c a₀ a₁       -> PLam (readBack c) (readBack a₀) (readBack a₁)
   VCoePartial r₀ r₁ c -> Coe (readBack r₀) (readBack r₁) (readBack c)
   VCoe r₀ r₁ c u₀     -> readBack (VCoePartial r₀ r₁ c) `App` readBack u₀
   VHComp r₀ r₁ a u₀ s -> HComp (readBack r₀) (readBack r₁) (readBack a) (readBack u₀) (readBack s)
   VExt a b            -> Ext (readBack a) (readBack b)
   VExtElm v us        -> ExtElm (readBack v) (readBack us)
   VSum d _            -> readBack d
   VCon c as           -> Con c (map readBack as)
   VSplitPartial f _   -> readBack f
   VNeu k              -> readBack k

instance ReadBack Neu where
  type Quot Neu = Tm

  readBack :: AtStage (Neu -> Tm)
  readBack = \case
    NVar x              -> Var x
    NApp k v            -> readBack k `App` readBack v
    NPr1 v              -> Pr1 (readBack v)
    NPr2 v              -> Pr2 (readBack v)
    NPApp k a₀ a₁ r     -> PApp (readBack k) (readBack a₀) (readBack a₁) (readBack r)
    NCoePartial r₀ r₁ c -> Coe (readBack r₀) (readBack r₁) (readBack c)
    NHComp r₀ r₁ k u₀ s -> HComp (readBack r₀) (readBack r₁) (readBack k) (readBack u₀) (readBack s)
    NExtFun ws k        -> ExtFun (readBack ws) (readBack k)
    NSplit f bs k       -> readBack (VSplitPartial f bs) `App` readBack k

instance ReadBack v => ReadBack (VSys v) where
  type Quot (VSys v) = Sys (Quot v)

  readBack :: AtStage (VSys v -> Sys (Quot v))
  readBack (VSys bs) = Sys [ (readBack φ, extCof φ (readBack v)) | (φ, v) <- bs ]

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