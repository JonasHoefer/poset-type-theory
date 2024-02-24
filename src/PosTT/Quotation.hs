-- | Quotation of Semantic Values back into Terms
module PosTT.Quotation where

import PosTT.Eval
import PosTT.Terms
import PosTT.Values

--------------------------------------------------------------------------------
---- Read Back

class ReadBack a where
  type Quot a
  readBack :: AtStage (a -> Quot a)

instance ReadBack Val where
  type Quot Val = Tm

  readBack :: AtStage (Val -> Tm)
  readBack = \case
    VU -> U

    VPi a b -> Pi (readBack a) (readBack b)
    VLam cl -> Lam (readBack cl)

    VSigma a b -> Sigma (readBack a) (readBack b)
    VPair u v  -> Pair (readBack u) (readBack v)

    VNeu k -> readBack k

instance (Eval a, ReadBack (ResType (Closure a)), Quot (ResType (Closure a)) ~ a) => ReadBack (Closure a) where
  type Quot (Closure a) = Binder a

  readBack :: AtStage (Closure a -> Binder a)
  readBack cl@(Closure y _ _)  = refreshName y $ \x -> Binder x $ readBack $ cl $$ VVar x

instance ReadBack Neu where
  type Quot Neu = Tm

  readBack :: AtStage (Neu -> Tm)
  readBack = \case
    NVar x -> Var x

    NPr1 k -> Pr1 (readBack k)
    NPr2 k -> Pr2 (readBack k)

