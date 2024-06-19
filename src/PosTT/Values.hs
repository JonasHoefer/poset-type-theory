-- | Representations of Values
module PosTT.Values where

import Algebra.Lattice

import Data.Bifunctor
import Data.List (uncons)
import Data.Either (isRight)

import PosTT.Common
import PosTT.Terms
import PosTT.Errors
import qualified PosTT.Common as M


-- We mirror terminology and observations by András Kovács.
-- We have two types of binders in cubical NbE:
-- 1. Those which just have to be evaluated at some point
-- 2. Those which have to be peeked under during the evaluation
-- We call the semantic values associated to a binder a *closure*, and call
-- those closures associated to binders of the second type *transparent*.


--------------------------------------------------------------------------------
---- Fibrant Values

data Val where
  VU :: Val
  VPi :: Val -> Closure -> Val
  VLam :: Closure -> Val

  VSigma :: Val -> Closure -> Val
  VPair :: Val -> Val -> Val

  VPath :: TrIntClosure -> Val -> Val -> Val
  VPLam :: IntClosure -> Val -> Val -> Val

  VCoePartial :: VI -> VI -> TrIntClosure -> Val

  -- In Π, Σ, Path, we delay coe and hcomp until elimination
  VCoe :: VI -> VI -> TrIntClosure -> Val -> Val
  VHComp :: VI -> VI -> VTy -> Val -> VSys TrIntClosure -> Val

  VExt :: VTy -> VSys (VTy, Val, Val) -> Val
  VExtElm :: Val -> VSys Val -> Val

  VSum :: Val -> [VLabel] -> VTy
  VCon :: Name -> [Val] -> Val
  VSplitPartial :: Val -> [VBranch] -> Val

  VHSum :: Val -> [VHLabel] -> VTy
  VHCon :: Name -> [Val] -> [VI] -> VSys Val -> Val
  VHSplitPartial :: Val -> Closure -> [VBranch] -> Val

  VNeu :: !Neu -> Val
type VTy = Val


pattern VCoePi :: VI -> VI -> Gen -> Val -> Closure -> Restr -> Val -> Val
pattern VCoePi r₀ r₁ i a b α u = VCoe r₀ r₁ (TrIntClosure i (VPi a b) α)  u

pattern VCoeSigma :: VI -> VI -> Gen -> Val -> Closure -> Restr -> Val -> Val
pattern VCoeSigma r₀ r₁ i a b α u = VCoe r₀ r₁ (TrIntClosure i (VSigma a b) α)  u

pattern VCoePath :: VI -> VI -> Gen -> TrIntClosure -> Val -> Val -> Restr -> Val -> Val
pattern VCoePath r₀ r₁ i a a₀ a₁ α u = VCoe r₀ r₁ (TrIntClosure i (VPath a a₀ a₁) α)  u


pattern VHCompPi :: VI -> VI -> Val -> Closure -> Val -> VSys TrIntClosure -> Val
pattern VHCompPi r r' a b a0 sys = VHComp r r' (VPi a b) a0 sys

pattern VHCompSigma :: VI -> VI -> Val -> Closure -> Val -> VSys TrIntClosure -> Val
pattern VHCompSigma r r' a b a0 sys = VHComp r r' (VSigma a b) a0 sys

pattern VHCompPath :: VI -> VI -> TrIntClosure -> Val -> Val -> Val -> VSys TrIntClosure -> Val
pattern VHCompPath r r' a ar ar' a0 sys = VHComp r r' (VPath a ar ar') a0 sys

pattern VHCompHSum :: VI -> VI -> Val -> [VHLabel] -> Val -> VSys TrIntClosure -> Val
pattern VHCompHSum r r' d lbl a0 sys = VHComp r r' (VHSum d lbl) a0 sys


newtype VSys a = VSys { unVSys :: [(VCof, a)] }
  deriving Semigroup via [(VCof, a)]
  deriving Monoid    via [(VCof, a)]

pattern EmptySys :: VSys a
pattern EmptySys = VSys []

data Closure = Closure Name Tm Env

data Neu where
  NVar :: Name -> Neu
  NApp :: Neu -> Val -> Neu
  NPr1 :: Neu -> Neu
  NPr2 :: Neu -> Neu
  NPApp :: Neu -> Val -> Val -> VI -> Neu
  NCoePartial :: VI -> VI -> TrNeuIntClosure -> Neu
  NCoeSum :: VI -> VI -> Gen -> VTy -> [VLabel] -> Restr -> Neu -> Neu
  NCoeHSum :: VI -> VI -> Gen -> VTy -> [VHLabel] -> Restr -> Neu -> Neu
  NHComp :: VI -> VI -> Neu -> Val -> VSys TrIntClosure -> Neu
  NHCompSum :: VI -> VI -> VTy -> [VLabel] -> Neu -> VSys TrIntClosure -> Neu
  NNonConstHCompSum :: VI -> VI -> VTy -> [VLabel] -> Name -> [Val] -> VSys TrIntClosure -> Neu
  NExtFun :: VSys Val -> Neu -> Neu
  NSplit :: Val -> [VBranch] -> Neu -> Neu
  NHSplit :: Val -> Closure -> [VBranch] -> Neu -> Neu

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

pattern VNeuCoeSum :: VI -> VI -> Gen -> VTy -> [VLabel] -> Restr -> Neu -> Val
pattern VNeuCoeSum r₀ r₁ i d lbl f k = VNeu (NCoeSum r₀ r₁ i d lbl f k)

pattern VNeuCoeHSum :: VI -> VI -> Gen -> VTy -> [VHLabel] -> Restr -> Neu -> Val
pattern VNeuCoeHSum r₀ r₁ i d lbl f k = VNeu (NCoeHSum r₀ r₁ i d lbl f k)

pattern VNeuHComp :: VI -> VI -> Neu -> Val -> VSys TrIntClosure -> Val
pattern VNeuHComp r r' a u₀ tb = VNeu (NHComp r r' a u₀ tb)

pattern VNeuHCompSum :: VI -> VI -> VTy -> [VLabel] -> Neu -> VSys TrIntClosure -> Val
pattern VNeuHCompSum r₀ r₁ d lbl k tb = VNeu (NHCompSum r₀ r₁ d lbl k tb)

pattern VNonConstHCompSum :: VI -> VI -> VTy -> [VLabel] -> Name -> [Val] -> VSys TrIntClosure -> Val
pattern VNonConstHCompSum r₀ r₁ d lbl c as tb = VNeu (NNonConstHCompSum r₀ r₁ d lbl c as tb)

pattern VExtFun :: VSys Val -> Neu -> Val
pattern VExtFun ws k = VNeu (NExtFun ws k)

pattern VSplit :: Val -> [VBranch] -> Neu -> Val
pattern VSplit f bs k = VNeu (NSplit f bs k)

pattern VHSplit :: Val -> Closure -> [VBranch] -> Neu -> Val
pattern VHSplit f a bs k = VNeu (NHSplit f a bs k)


---- Data Types

data VTel = VTel [(Name, Ty)] Env

lengthVTel :: VTel -> Int
lengthVTel (VTel as _) = length as

type VLabel = (Name, VTel)


---- Higher Inductive Types

data VHTel = VHTel [(Name, Ty)] [Gen] (Sys Tm) Env

lengthVHTel :: VHTel -> Int
lengthVHTel (VHTel as is _ _) = length as + length is

hTelToTel :: VHTel -> VTel
hTelToTel (VHTel tel _ _ ρ) = VTel tel ρ

type VHLabel = (Name, VHTel)


---- Case Splits

type VBranch = (Name, SplitClosure)

data SplitClosure = SplitClosure [Name] Tm Env


--------------------------------------------------------------------------------
---- Values for Base Category (interval and cofibrations)

---- Interval

newtype VI = VI [[Gen]] -- DNF

iVar :: Gen -> VI
iVar i = VI [[i]]


---- Functions out of the interval

-- | A closure binding an interval variable.
data IntClosure = IntClosure Gen Tm Env

-- | A "transparent" closure binding an interval variable.
data TrIntClosure = TrIntClosure Gen Val Restr

-- | Smart constructor for a TrIntClosure.
--
-- Abstracts a fresh variable for the current stage, preferring the given name.
-- The continuation works at the extended stage to produce the captured value.
trIntCl :: AtStage (Gen -> AtStage (Gen -> Val) -> TrIntClosure)
trIntCl i k = refreshGen i $ \i' -> TrIntClosure i' (k i') IdRestr

trIntCl' :: AtStage (AtStage (Gen -> Val) -> TrIntClosure)
trIntCl' k = freshGen $ \i' -> TrIntClosure i' (k i') IdRestr

-- | A "transparent" closure binding an interval variable,
--   whose captured value is guarantied to be neutral.
data TrNeuIntClosure = TrNeuIntClosure Gen Neu


---- Cofibrations

newtype VCof = VCof [(VI, VI)]

instance InfSemilattice VCof where
  top :: VCof
  top = VCof []

  (/\) :: VCof -> VCof -> VCof
  VCof phi /\ VCof psi = VCof (phi ++ psi)


---- Stages

data Stage = Stage { gens :: !NameStore, cof :: !VCof, names :: !NameStore }

terminalStage :: Stage
terminalStage = Stage M.emptyStore top M.emptyStore

type AtStage a = (?s :: Stage) => a

bindStage :: Stage -> AtStage a -> a
bindStage s k = let ?s = s in k

sExtName :: Name -> Stage -> Stage
sExtName n s = s { names = addNameStore n (names s) }

sExtGen :: Gen -> Stage -> Stage
sExtGen n s = s { gens = addNameStore n (gens s) }

sExtCof :: VCof -> Stage -> Stage
sExtCof φ s = s { cof = φ /\ cof s}

extName :: AtStage (Name -> AtStage a -> a)
extName n = bindStage (sExtName n ?s)

extGen :: AtStage (Gen -> AtStage a -> a)
extGen n = bindStage (sExtGen n ?s)

extCof :: AtStage (VCof -> AtStage a -> a)
extCof φ = bindStage (sExtCof φ ?s)


---- Fresh Names/Generators

freshName :: AtStage (AtStage (Name -> a) -> a)
freshName = refreshName "x"

freshFibVar :: AtStage (AtStage (Val -> a) -> a)
freshFibVar k = freshName (k . VVar)

freshGen :: AtStage (AtStage (Gen -> a) -> a)
freshGen = refreshGen "i"

freshIntVar :: AtStage (AtStage (VI -> a) -> a)
freshIntVar k = freshGen (k . iVar)


refreshName :: AtStage (Name -> AtStage (Name -> a) -> a)
refreshName n k =
  let (s', n') = refreshNameStore n (names ?s)
  in  bindStage (?s {names = s'}) (k n')

refreshGen :: AtStage (Gen -> AtStage (Gen -> a) -> a)
refreshGen n k =
  let (s', n') = refreshNameStore n (gens ?s)
  in  bindStage (?s {gens = s'}) (k n')


---- Restrictions maps

newtype Restr = Restr [(Gen, VI)] deriving (Semigroup, Monoid) via [(Gen, VI)]

pattern IdRestr :: Restr
pattern IdRestr = Restr []

class Restrictable a where
  type Alt a
  type Alt a = a
  act :: AtStage (Restr -> a -> Alt a)

infixl 7 @
(@) :: Restrictable a => AtStage (a -> Restr -> Alt a)
a @ f = f `act` a

re :: Restrictable a => AtStage (a -> Alt a)
re = (@ IdRestr)


--------------------------------------------------------------------------------
---- Environment

type Env = [(Name, EnvEntry)]

data EnvEntry = EntryDef !Tm !Ty | EntryFib !Val | EntryInt !VI | EntryLock

pattern EmptyEnv :: Env
pattern EmptyEnv = []

pattern EnvCons :: Env -> Name -> EnvEntry -> Env
pattern EnvCons rho x e <- (uncons -> Just ((x, e), rho))
  where EnvCons rho x e = (x,e):rho

{-# COMPLETE EmptyEnv, EnvCons #-}

pattern EnvLock :: Env -> Name -> Env
pattern EnvLock rho x = (x, EntryLock):rho

pattern EnvFib :: Env -> Name -> Val -> Env
pattern EnvFib rho x v   = (x, EntryFib v):rho

pattern EnvInt :: Env -> Gen -> VI -> Env
pattern EnvInt rho x i   = (x, EntryInt i):rho

pattern EnvDef :: Env -> Name -> Tm -> Ty -> Env
pattern EnvDef rho x s t = (x, EntryDef s t):rho

envIdents :: Env -> [Name]
envIdents EmptyEnv          = []
envIdents (EnvCons rho n _) = n : envIdents rho

envFibs :: Env -> [(Name, Val)] -> Env
envFibs = foldr (\(x, v) rho' -> EnvFib rho' x v)

envInts :: Env -> [(Name, VI)] -> Env
envInts = foldr (\(x, v) rho' -> EnvInt rho' x v)

envRestr :: Env -> Restr
envRestr = Restr . go
  where
    go EmptyEnv         = []
    go (EnvInt ρ i r)   = (i, r) : go ρ
    go (EnvCons ρ _ _)  = go ρ


--------------------------------------------------------------------------------
---- Convertibility

-- | Our notion of equality for semantic values is convertibility.
--
-- This class is defined here, because evaluation depends on convertibility of
-- values of pre-type I, but conversion checking for fibrant values depends on
-- evaluation. We break this cycle, by factoring out this class.
class Conv a where
  (===) :: AtStage (a -> a -> Bool)
  x === y = isRight (x `conv` y)

  conv :: AtStage (a -> a -> Either ConvError ())


--------------------------------------------------------------------------------
---- Quotation

-- | Semantic values can be read back into terms.
class ReadBack a where
  type Quot a
  readBack :: AtStage (a -> Quot a)

instance ReadBack VI where
  type Quot VI = I

  readBack :: AtStage (VI -> I)
  readBack (VI dnf) = sup [ inf (map IVar cl) | cl <- dnf ]

instance ReadBack VCof where
  type Quot VCof = Cof

  readBack :: AtStage (VCof -> Cof)
  readBack (VCof eqs) = Cof (map (bimap readBack readBack) eqs)
