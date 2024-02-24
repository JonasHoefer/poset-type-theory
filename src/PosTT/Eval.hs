-- | Evaluation of Terms into Semantic Values
module PosTT.Eval where

import Algebra.Lattice

import Data.Tuple.Extra (fst3)

import PosTT.Terms
import PosTT.Values
import PosTT.Poset


--------------------------------------------------------------------------------
---- Utilities 

-- | Looks up firbant value in environment. If it is a definition, then it is
--   evaluated. Thus, the current stage is required.
lookupFib :: AtStage (Env -> Name -> Val)
lookupFib (EnvFib _ y v)       x | y == x = v
lookupFib rho@(EnvDef _ y t _) x | y == x = eval rho t
lookupFib (ConsEnv rho)        x = rho `lookupFib` x

lookupInt :: Env -> Gen -> VI
lookupInt (EnvInt _ y r) x | y == x = r
lookupInt (ConsEnv rho)  x = rho `lookupInt` x

reAppDef :: AtStage (Name -> Env -> Val)
reAppDef d (EnvFib rho x v) 
  | x == d = VVar d
  | x /= d = reAppDef d rho `doApp` v

--------------------------------------------------------------------------------
---- Eval

class Eval a where
  type Sem a
  eval :: AtStage (Env -> a -> Sem a)

instance Eval Tm where
  type Sem Tm = Val

  eval :: AtStage (Env -> Tm -> Val)
  eval rho = \case
    U            -> VU
    Var x        -> rho `lookupFib` x
    Let d t ty s -> extName d $ eval (EnvDef rho d t ty) s

    Pi a b  -> VPi (eval rho a) (eval rho b)
    Lam t   -> VLam (eval rho t)
    App s t -> eval rho s `doApp` eval rho t

    Sigma a b -> VSigma (eval rho a) (eval rho b)
    Pair s t  -> VPair (eval rho s) (eval rho t)
    Pr1 t     -> doPr1 (eval rho t)
    Pr2 t     -> doPr2 (eval rho t)

    Path a s t     -> VPath (eval rho a) (eval rho s) (eval rho t)
    PLam t t0 t1   -> VPLam (eval rho t) (eval rho t0) (eval rho t1)
    PApp t t0 t1 r -> doPApp (eval rho t) (eval rho t0) (eval rho t1) (eval rho r)

    Coe r0 r1 l         -> VCoePartial (eval rho r0) (eval rho r1) (eval rho l)
    HComp r0 r1 a u0 tb -> doHComp' (eval rho r0) (eval rho r1) (eval rho a) (eval rho u0) (eval rho tb)

    Ext a bs    -> vExt (eval rho a) (eval rho bs)
    ExtElm s ts -> vExtElm (eval rho s) (eval rho ts)
    -- ExtFun :: (Sys Tm) -> Tm -> Tm

    Sum d lbl  -> VSum (reAppDef d rho) (eval rho lbl)
    Con c args -> VCon c (eval rho args)
    Split f bs -> VSplitPartial (reAppDef f rho) (eval rho bs)

instance Eval I where
  type Sem I = VI

  eval :: AtStage (Env -> I -> VI)
  eval rho = \case
    Sup r s -> eval rho r \/ eval rho s
    Inf r s -> eval rho r /\ eval rho s
    I0      -> bot
    I1      -> top
    IVar i  -> rho `lookupInt` i

instance Eval Cof where
  type Sem Cof = VCof

  eval :: AtStage (Env -> Cof -> VCof)
  eval rho (Cof eqs) = VCof (map (eval rho) eqs)

instance Eval a => Eval (Sys a) where
  type Sem (Sys a) = Either (Sem a) (VSys (Sem a))

  eval :: AtStage (Env -> Sys a -> Either (Sem a) (VSys (Sem a)))
  eval rho (Sys bs) = simplifySys (VSys bs') 
    where bs' = [ (phi', extCof phi' (eval rho a)) | (phi, a) <- bs, let phi' = eval rho phi ]

instance Eval (Binder Tm) where
  type Sem (Binder Tm) = Closure Tm

  eval :: AtStage (Env -> Binder Tm -> Closure Tm)
  eval rho (Binder x t) = Closure x t rho

instance Eval (IntBinder Tm) where
  type Sem (IntBinder Tm) = IntClosure

  eval :: AtStage (Env -> IntBinder Tm -> IntClosure)
  eval rho (IntBinder i t) = IntClosure i t rho

instance Eval (TrIntBinder Tm) where
  type Sem (TrIntBinder Tm) = TrIntClosure

  -- | We evaluate a transparant binder, by evaluating the *open* terms t under
  --   the binder. (TODO: How can i be already used if the terms have no shadowing?)
  eval :: AtStage (Env -> TrIntBinder Tm -> TrIntClosure)
  eval rho (TrIntBinder i t) = trIntCl i $ \i' -> eval (EnvInt rho i (iVar i')) t

instance Eval SplitBinder where
  type Sem SplitBinder = SplitClosure
  
  eval :: AtStage (Env -> SplitBinder -> SplitClosure)
  eval rho (SplitBinder xs t) = SplitClosure xs t rho

instance Eval Branch where
  type Sem Branch = VBranch

  eval :: AtStage (Env -> Branch -> VBranch)
  eval rho (Branch c t) = (c, eval rho t)

instance Eval Label where
  type Sem Label = VLabel

  eval :: AtStage (Env -> Label -> VLabel)
  eval rho (Label c tel) = (c, eval rho tel)

instance Eval Tel where
  type Sem Tel = VTel

  eval :: AtStage (Env -> Tel -> VTel)
  eval rho (Tel ts) = VTel ts rho

instance Eval a => Eval [a] where
  type Sem [a] = [Sem a]

  eval :: AtStage (Env -> [a] -> [Sem a])
  eval rho = map (eval rho)

instance (Eval a, Eval b) => Eval (a, b) where
  type Sem (a, b) = (Sem a, Sem b)

  eval :: AtStage (Env -> (a, b) -> (Sem a, Sem b))
  eval rho (a, b) = (eval rho a, eval rho b)

instance (Eval a, Eval b, Eval c) => Eval (a, b, c) where
  type Sem (a, b, c) = (Sem a, Sem b, Sem c)

  eval :: AtStage (Env -> (a, b, c) -> (Sem a, Sem b, Sem c))
  eval rho (a, b, c) = (eval rho a, eval rho b, eval rho c) 


--------------------------------------------------------------------------------
---- Semantic Combinators

---- Closure Evaluation

class Apply c where
  type ArgType c
  type ResType c

  ($$) :: AtStage (c -> ArgType c -> ResType c)

instance Eval a => Apply (Closure a) where
  type ArgType (Closure a) = Val
  type ResType (Closure a) = Sem a

  ($$) :: AtStage (Closure a -> Val -> Sem a)
  Closure x t rho $$ v = eval (EnvFib rho x v) t

instance Apply IntClosure where
  type ArgType IntClosure = VI
  type ResType IntClosure = Val

  ($$) :: AtStage (IntClosure -> VI -> Val)
  IntClosure i t rho $$ r = eval (EnvInt rho i r) t

instance Apply SplitClosure where
  type ArgType SplitClosure = [Val]
  type ResType SplitClosure = Val

  ($$) :: AtStage (SplitClosure -> [Val] -> Val)
  SplitClosure xs t rho $$ vs = eval (rho `envFibs` (xs `zip` vs)) t 


---- Basic Combinators

doPr1 :: AtStage (Val -> Val)
doPr1 (VPair s _) = s
doPr1 (VNeu k)    = VPr1 k

doPr2 :: AtStage (Val -> Val)
doPr2 (VPair _ t) = t
doPr2 (VNeu k)    = VPr2 k

doApp :: AtStage (Val -> Val -> Val)
doApp (VLam cl)            v = cl $$ v
doApp (VNeu k)             v = VApp k v
doApp (VSplitPartial f bs) v = doSplit f bs v

doPApp :: AtStage (Val -> Val -> Val -> VI -> Val)
doPApp (VPLam cl _ _) _  _  r = cl $$ r
doPApp (VNeu k)       p0 p1 r
  | r === 0   = p0
  | r === 1   = p1
  | otherwise = VPApp k p0 p1 r

doSplit :: AtStage (Val -> [VBranch] -> Val -> Val)
doSplit f bs (VCon c as) | Just cl <- lookup c bs = cl $$ as
doSplit f bs (VNeu k)    = VSplit f bs k


---- Extension Types

vExt :: AtStage (Val -> Either (VTy, Val, Val) (VSys (VTy, Val, Val)) -> Val)
vExt a = either fst3 (VExt a)

vExtElm :: AtStage (Val -> Either Val (VSys Val) -> Val)
vExtElm v = either id (VExtElm v) 


---- HComp

-- | HComp where the system could be trivial
doHComp' :: AtStage (VI -> VI -> VTy -> Val -> Either TrIntClosure (VSys TrIntClosure) -> Val)
doHComp' = _

doHComp :: AtStage (VI -> VI -> VTy -> Val -> VSys TrIntClosure -> Val)
doHComp = _



--------------------------------------------------------------------------------
---- Restriction Operations

