-- | Representations of Values
module PosTT.Values where

import Algebra.Lattice

import PosTT.Terms

-- We mirror terminology and observations by András Kovács.
-- We have two types of binders in cubical NbE: 
-- 1. Those which just have to be evaluated at some poitn
-- 2. Those which have to be peeked under during the evaluation
-- We call the semantic values associated to a binder a *closure*, and call
-- those closures associated to binders of the second type *transparant*.


--------------------------------------------------------------------------------
---- Fibrant Values

data Val where
  VU :: Val
  VPi :: Val -> Closure Ty -> Val
  VLam :: Closure Tm -> Val

  VSigma :: Val -> Closure Ty -> Val
  VPair :: Val -> Val -> Val

  VPath :: Val -> Val -> Val -> Val
  VPLam :: IntClosure -> Val -> Val -> Val

  VCoePartial :: VI -> VI -> TrIntClosure -> Val

  -- In negative types, we delay coe and hcomp until elimination
  VCoe :: VI -> VI -> TrIntClosure -> Val -> Val
  VHComp :: VI -> VI -> VTy -> Val -> VSys TrIntClosure -> Val

  VExt :: VTy -> VSys (VTy, Val, Val) -> Val
  VExtElm :: Val -> VSys Val -> Val

  VSum :: Val -> [VLabel] -> VTy
  VCon :: Name -> [Val] -> Val
  VSplitPartial :: Val -> [VBranch] -> Val

  VNeu :: Neu -> Val
type VTy = Val

pattern VCoePi :: VI -> VI -> Gen -> Val -> Closure Tm -> Restr -> Val -> Val
pattern VCoePi r₀ r₁ i a b α u = VCoe r₀ r₁ (TrIntClosure i (VPi a b) α)  u

pattern VCoeSigma :: VI -> VI -> Gen -> Val -> Closure Tm -> Restr -> Val -> Val
pattern VCoeSigma r₀ r₁ i a b α u = VCoe r₀ r₁ (TrIntClosure i (VSigma a b) α)  u

pattern VCoePath :: VI -> VI -> Gen -> Val -> Val -> Val -> Restr -> Val -> Val
pattern VCoePath r₀ r₁ i a a₀ a₁ α u = VCoe r₀ r₁ (TrIntClosure i (VPath a a₀ a₁) α)  u


pattern VHCompPi :: VI -> VI -> Val -> Closure Tm -> Val -> VSys TrIntClosure -> Val
pattern VHCompPi r r' a b a0 sys = VHComp r r' (VPi a b) a0 sys

pattern VHCompSigma :: VI -> VI -> Val -> Closure Tm -> Val -> VSys TrIntClosure -> Val
pattern VHCompSigma r r' a b a0 sys = VHComp r r' (VSigma a b) a0 sys

pattern VHCompPath :: VI -> VI -> Val -> Val -> Val -> Val -> VSys TrIntClosure -> Val
pattern VHCompPath r r' a ar ar' a0 sys = VHComp r r' (VPath a ar ar') a0 sys


newtype VSys a = VSys [(VCof, a)]

data Closure a = Closure Name a Env

data Neu where
  NVar :: Name -> Neu
  NApp :: Neu -> Val -> Neu
  NPr1 :: Neu -> Neu
  NPr2 :: Neu -> Neu
  NPApp :: Neu -> Val -> Val -> VI -> Neu
  NCoePartial :: VI -> VI -> TrNeuIntClosure -> Neu
  NHComp :: VI -> VI -> Neu -> Val -> VSys TrIntClosure -> Neu
  -- NHCompSum :: VI -> VI -> VTy -> [VLabel] -> Neu -> VSys IntClosure -> Neu
  NExtFun :: VSys Val -> Neu -> Neu
  NSplit :: Val -> [VBranch] -> Neu -> Neu

pattern VVar :: Name -> Val
pattern VVar x = VNeu (NVar x)

pattern VApp :: Neu -> Val -> Val
pattern VApp k v = VNeu (NApp k v)

pattern VPr1 :: Neu -> Val
pattern VPr1 v = VNeu (NPr1 v)

pattern VPr2 :: Neu -> Val
pattern VPr2 v = VNeu (NPr2 v)

pattern VPApp :: Neu -> Val -> Val -> VI -> Val
pattern VPApp k p0 p1 r = VNeu (NPApp k p0 p1 r)

pattern VNeuCoePartial :: VI -> VI -> TrNeuIntClosure -> Val
pattern VNeuCoePartial r0 r1 cl = VNeu (NCoePartial r0 r1 cl)

pattern VNeuHComp :: VI -> VI -> Neu -> Val -> VSys TrIntClosure -> Val
pattern VNeuHComp r r' a u₀ tb = VNeu (NHComp r r' a u₀ tb)

pattern VExtFun :: VSys Val -> Neu -> Val
pattern VExtFun ws k = VNeu (NExtFun ws k)

pattern VSplit :: Val -> [VBranch] -> Neu -> Val
pattern VSplit f bs k = VNeu (NSplit f bs k)


---- Data Types

data VTel = VTel [(Name, Ty)] Env

type VLabel = (Name, VTel)

type VBranch = (Name, SplitClosure)

data SplitClosure = SplitClosure [Name] Tm Env


--------------------------------------------------------------------------------
---- Values for Base Category (interval and cofibrations)

---- Interval

newtype VI = VI [[Gen]] -- DNF

instance SupSemilattice VI where
  (\/) :: VI -> VI -> VI
  VI r \/ VI s = VI (r ++ s)

  bot :: VI
  bot = VI []

instance InfSemilattice VI where
  (/\) :: VI -> VI -> VI
  VI r /\ VI s = VI [ m ++ n | m <- r, n <- s ]

  top :: VI
  top = VI [[]]

instance Num VI where fromInteger 0 = bot ; fromInteger 1 = top

iVar :: Gen -> VI
iVar i = VI [[i]]


---- Functions out of the interval

-- | A closure binding an interval variable.
data IntClosure = IntClosure Gen Tm Env

-- | A "transpart" closure binding an interval variable.
data TrIntClosure = TrIntClosure Gen Val Restr

-- | Smart constructor for a TrIntClosure.
--
-- Abstracts a fresh variable for the current stage, prefering the given name.
-- The continuation works at the extended stage to produce the captured value.
trIntCl :: AtStage (Gen -> AtStage (Gen -> Val) -> TrIntClosure)
trIntCl i k = refreshGen i $ \i' -> TrIntClosure i' (k i') IdRestr

-- | A "transpart" closure binding an interval variable,
--   whose captured value is guarantied to be neutral. 
data TrNeuIntClosure = TrNeuIntClosure Gen Neu


---- Cofibrations

-- | Representation of a sieve generated by an embedding, 
--   as a list of equations under Birkhoff duality.
newtype VCof = VCof [(VI, VI)]

-- | Sieves represented by VCof are closed under conjunction.
instance InfSemilattice VCof where
  top :: VCof
  top = VCof []

  (/\) :: VCof -> VCof -> VCof
  VCof phi /\ VCof psi = VCof (phi ++ psi)


---- Stages

data Stage = Stage { gens :: [Gen], cof :: VCof, names :: [Name] }

terminalStage :: Stage
terminalStage = Stage [] top []

type AtStage a = (?s :: Stage) => a

bindStage :: Stage -> AtStage a -> a
bindStage s k = let ?s = s in k

extName :: AtStage (Name -> AtStage a -> a)
extName n = bindStage (?s { names = n : names ?s })

extGen :: AtStage (Gen -> AtStage a -> a)
extGen n = bindStage (?s { gens = n : gens ?s })

extCof :: AtStage (VCof -> AtStage a -> a)
extCof phi = bindStage (?s { cof = phi /\ cof ?s })


---- Fresh Names/Generators

freshName :: AtStage (AtStage (Name -> a) -> a)
freshName = refreshName "x"

refreshName :: AtStage (Name -> AtStage (Name -> a) -> a)
refreshName y k = extName x $ k x
  where
    x = Name $ head
          [ x'
          | x' <- unName y : [ 'x':show n | n <- [1..] ]
          , Name x' `notElem` names ?s, Gen x' `notElem` gens ?s
          ]

refreshGen :: AtStage (Gen -> AtStage (Gen -> a) -> a)
refreshGen j k = extGen i $ k i
  where
    i = Gen $ head
          [ i'
          | i' <- unGen j : [ 'i':show n | n <- [1..] ]
          , Name i' `notElem` names ?s, Gen i' `notElem` gens ?s
          ]


---- Restrictions maps

newtype Restr = Restr [(Gen, VI)]

pattern IdRestr :: Restr
pattern IdRestr = Restr []

class Restrictable a where
  type Alt a
  act :: AtStage (Restr -> a -> Alt a)

infixl 7 @
(@) :: Restrictable a => AtStage (a -> Restr -> Alt a)
a @ f = f `act` a


--------------------------------------------------------------------------------
---- Environment

data Entry = EntryFib Val | EntryDef Tm Ty | EntryInt VI

data Env
  = EmptyEnv
  | EnvFib Env Name Val
  | EnvDef Env Name Tm Ty
  | EnvInt Env Gen VI

unConsEnv :: Env -> Maybe Env
unConsEnv = \case
  EnvFib rho _ _   -> Just rho
  EnvDef rho _ _ _ -> Just rho
  EnvInt rho _ _   -> Just rho
  EmptyEnv         -> Nothing

pattern ConsEnv :: Env -> Env
pattern ConsEnv rho <- (unConsEnv -> Just rho)

envFibs :: Env -> [(Name, Val)] -> Env
envFibs = foldr (\(x, v) rho' -> EnvFib rho' x v)

envRestr :: Env -> Restr
envRestr = Restr . go
  where
    go EmptyEnv         = []
    go (EnvInt rho i r) = (i, r) : go rho
    go (ConsEnv rho)    = go rho


--------------------------------------------------------------------------------
---- Convertibility  

-- | Our notion of equality for semantic values is convertibility .
--
-- This class is defined here, because evaluation depends on convertibility of
-- values of pre-type I, but conversion checking for fibrant values depends on
-- evaluation. We break this cycle, by factorring out this class.
class Convertible a where
  (===) :: AtStage (a -> a -> Bool)
