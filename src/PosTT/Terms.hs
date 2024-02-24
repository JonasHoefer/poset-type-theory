module PosTT.Terms where

import Data.String (IsString(..))

--------------------------------------------------------------------------------
---- Terms of Fibrant Types

newtype Name = Name { unName :: String } deriving (Eq, IsString)

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
  ExtElm :: Tm -> (Sys Tm) -> Tm
  ExtFun :: Sys Tm -> Tm -> Tm

  Sum :: Name -> [Label] -> Tm
  Con :: Name -> [Tm] -> Tm
  Split :: Name -> [Branch] -> Tm
type Ty = Tm

---- Binder (We explicitly mark how variables are bound above)

data Binder a = Binder Name a

data IntBinder a = IntBinder Gen a

data TrIntBinder a = TrIntBinder Gen a

data SplitBinder = SplitBinder [Name] Tm

---- Data Types

newtype Tel = Tel [(Name, Ty)]

data Label = Label Name Tel

data Branch = Branch Name SplitBinder


--------------------------------------------------------------------------------
---- Base Category

newtype Gen = Gen { unGen :: String } deriving Eq

data I = IVar Gen | Sup I I | Inf I I | I0 | I1

newtype Cof = Cof [(I, I)]

newtype Sys a = Sys [(Cof, a)]
