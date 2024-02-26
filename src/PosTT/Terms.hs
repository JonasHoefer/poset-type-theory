{-# LANGUAGE StrictData #-}

module PosTT.Terms where

import Data.String (IsString(..))

import PosTT.Common (Name)
import Algebra.Lattice (SupSemilattice(..), InfSemilattice(..))

--------------------------------------------------------------------------------
---- Terms of Fibrant Types

data Tm where
  U :: Ty
  Var :: Name -> Tm
  Let :: Name -> Tm -> Ty -> Tm -> Tm

  Pi :: Ty -> Binder Ty -> Ty
  Lam :: Binder Tm -> Tm
  App :: Tm -> Tm -> Tm

  Sigma :: Ty -> (Binder Ty) -> Ty
  Pair :: Tm -> Tm -> Tm
  Pr1 :: Tm -> Tm
  Pr2 :: Tm -> Tm

  Path :: Ty -> Tm -> Tm -> Tm
  PLam :: IntBinder Tm -> ~Tm -> ~Tm -> Tm
  PApp :: Tm -> ~Tm -> ~Tm -> I -> Tm

  Coe :: I -> I -> TrIntBinder Ty -> Tm
  HComp :: I -> I -> Ty -> Tm -> Sys (TrIntBinder Tm) -> Tm

  Ext :: Ty -> (Sys (Ty, Tm, Tm)) -> Tm
  ExtElm :: Tm -> ~(Sys Tm) -> Tm
  ExtFun :: ~(Sys Tm) -> Tm -> Tm

  Sum :: Name -> [Label] -> Tm
  Con :: Name -> [Tm] -> Tm
  Split :: Name -> [Branch] -> Tm
type Ty = Tm

instance IsString Tm where fromString = Var . fromString

---- Binder (We explicitly mark how variables are bound above)

data Binder a = Binder Name a

data IntBinder a = IntBinder Gen a

data TrIntBinder a = TrIntBinder Gen a

data SplitBinder = SplitBinder [Name] Tm

pattern BPi :: Ty -> Name -> Ty -> Tm
pattern BPi a x b = Pi a (Binder x b)

pattern BLam :: Name -> Tm -> Tm
pattern BLam x t = Lam (Binder x t)

pattern BSigma :: Ty -> Name -> Ty -> Tm
pattern BSigma a x b = Sigma a (Binder x b)

pattern BPLam :: Gen -> Tm -> Tm -> Tm -> Tm
pattern BPLam x t a₀ a₁ = PLam (IntBinder x t) a₀ a₁

pattern BCoe :: I -> I -> Gen -> Ty -> Tm
pattern BCoe r₀ r₁ i a = Coe r₀ r₁ (TrIntBinder i a)


---- Data Types

newtype Tel = Tel [(Name, Ty)]

pattern TelNil :: Tel
pattern TelNil = Tel []

telCons :: Name -> Ty -> Tel -> Tel
telCons x a (Tel tel) = Tel ((x, a) : tel)

data Label = Label Name Tel

data Branch = Branch Name SplitBinder

pattern BBranch :: Name -> [Name] -> Tm -> Branch
pattern BBranch n xs t = Branch n (SplitBinder xs t)


--------------------------------------------------------------------------------
---- Base Category

newtype Gen = Gen { unGen :: String } deriving (Eq, Ord, IsString)

data I = IVar Gen | Sup I I | Inf I I | I0 | I1

instance IsString I where fromString = IVar . fromString

newtype Cof = Cof [(I, I)]

newtype Sys a = Sys [(Cof, a)]

instance SupSemilattice I where
  (\/) :: I -> I -> I
  (\/) = Sup

  bot :: I
  bot = I0

instance InfSemilattice I where
  (/\) :: I -> I -> I
  (/\) = Inf

  top :: I
  top = I1