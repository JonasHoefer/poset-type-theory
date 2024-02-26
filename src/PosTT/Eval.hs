-- | Evaluation of Terms into Semantic Values
module PosTT.Eval where

import Algebra.Lattice

import Data.Tuple.Extra (fst3)

import PosTT.Common
import PosTT.Terms
import PosTT.Values
import PosTT.Poset

import Debug.Trace
import {-# SOURCE #-} PosTT.Pretty -- only for debugging


--------------------------------------------------------------------------------
---- Utilities 

-- | Looks up fibrant value in environment. If it is a definition, then it is
--   evaluated. Thus, the current stage is required.
lookupFib :: AtStage (Env -> Name -> Val)
lookupFib (EnvFib _ y v)       x | y == x = v
lookupFib rho@(EnvDef _ y t _) x | y == x = eval rho t -- recursive definition
lookupFib (ConsEnv rho)        x = rho `lookupFib` x

lookupInt :: Env -> Gen -> VI
lookupInt (EnvInt _ y r) x | y == x = r
lookupInt (ConsEnv rho)  x = rho `lookupInt` x

reAppDef :: AtStage (Name -> Env -> Val)
reAppDef d (EnvDef _   x _ _) | x == d = VVar d
reAppDef d (EnvFib rho x v)   | x /= d = reAppDef d rho `doApp` v


--------------------------------------------------------------------------------
---- Eval

class Eval a where
  type Sem a
  eval :: AtStage (Env -> a -> Sem a)

closedEval :: Eval a => a -> Sem a
closedEval = bindStage terminalStage $ eval EmptyEnv

instance Eval Tm where
  type Sem Tm = Val

  eval :: AtStage (Env -> Tm -> Val)
  eval rho = \case
    U            -> VU
    Var x        -> rho `lookupFib` x
    Let d t ty s -> eval (EnvDef rho d t ty) s -- TODO: do we need this extName? extName d $

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

    Coe r0 r1 l         -> vCoePartial (eval rho r0) (eval rho r1) (eval rho l)
    HComp r0 r1 a u0 tb -> doHComp' (eval rho r0) (eval rho r1) (eval rho a) (eval rho u0) (eval rho tb)

    Ext a bs    -> vExt (eval rho a) (eval rho bs)
    ExtElm s ts -> vExtElm (eval rho s) (eval rho ts)
    ExtFun ws t -> doExtFun' (eval rho ws) (eval rho t)

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
  type Sem (Binder Tm) = Closure

  eval :: AtStage (Env -> Binder Tm -> Closure)
  eval rho (Binder x t) = Closure x t rho

instance Eval (IntBinder Tm) where
  type Sem (IntBinder Tm) = IntClosure

  eval :: AtStage (Env -> IntBinder Tm -> IntClosure)
  eval rho (IntBinder i t) = IntClosure i t rho

instance Eval (TrIntBinder Tm) where
  type Sem (TrIntBinder Tm) = TrIntClosure

  -- | We evaluate a transparant binder, by evaluating the *open* term t under
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
---- Closure Evaluation

class Apply c where
  type ArgType c
  type ResType c

  infixr 0 $$
  ($$) :: AtStage (c -> ArgType c -> ResType c)

instance Apply Closure where
  type ArgType Closure = Val
  type ResType Closure = Val

  ($$) :: AtStage (Closure -> Val -> Val)
  Closure x t rho $$ v = eval (EnvFib rho x v) t

instance Apply IntClosure where
  type ArgType IntClosure = VI
  type ResType IntClosure = Val

  ($$) :: AtStage (IntClosure -> VI -> Val)
  IntClosure i t rho $$ r = eval (EnvInt rho i r) t

instance Apply TrIntClosure where
  type ArgType TrIntClosure = VI
  type ResType TrIntClosure = Val

  ($$) :: AtStage (TrIntClosure -> VI -> Val)
  TrIntClosure i v (Restr alpha) $$ r = v @ Restr ((i, r):alpha)

instance Apply TrNeuIntClosure where
  type ArgType TrNeuIntClosure = VI
  type ResType TrNeuIntClosure = Val

  ($$) :: AtStage (TrNeuIntClosure -> VI -> Val)
  TrNeuIntClosure i k $$ r = k @ (r `for` i)

instance Apply SplitClosure where
  type ArgType SplitClosure = [Val]
  type ResType SplitClosure = Val

  ($$) :: AtStage (SplitClosure -> [Val] -> Val)
  SplitClosure xs t rho $$ vs = eval (rho `envFibs` (xs `zip` vs)) t

-- | Forces the delayed restriction under the binder.
force :: AtStage (TrIntClosure -> TrIntClosure)
force cl@(TrIntClosure i _ _) = trIntCl i $ \j -> cl $$ iVar j


--------------------------------------------------------------------------------
---- Telescope Utilities

headVTel :: AtStage (VTel -> VTy)
headVTel (VTel ((_, a):_) ρ) = eval ρ a

tailVTel :: VTel -> Val -> VTel
tailVTel (VTel ((x, _):tel) ρ) v = VTel tel (EnvFib ρ x v)


--------------------------------------------------------------------------------
---- Prelude Combinators

pFunType :: Val
pFunType = closedEval $
  BLam "A" $ BLam "B" $ BPi "A" "_" "B"

pFib :: Val
pFib = closedEval $
  BLam "A" $ BLam "B" $ BLam "f" $ BLam "y" $
    BSigma "A" "x" (Path "B" "y" ("f" `App` "x"))

pIsContr :: Val
pIsContr = closedEval $
  BLam "A" $ BSigma "A" "x" $ BPi "A" "y" $ Path "A" "x" "y"

pIsEquiv :: Val
pIsEquiv = bindStage terminalStage $ eval (EnvFib (EnvFib EmptyEnv "fib" pFib) "is-contr" pIsContr) $
  BLam "A" $ BLam "B" $ BLam "f" $ BPi "B" "y" $ Var "is-contr" `App` foldl1 App ["fib", "A", "B", "f", "y"]

pId :: Val
pId = closedEval $ BLam "A" $ BLam "x" "x"

pRefl :: Val
pRefl = closedEval $ BLam "A" $ BLam "x" $ BPLam "i" "x" "x" "x"

-- isEquivId (A : U) : isEquiv A A (id A) =
--   \a. ((a, refl A a), \v z. (v.2 z, \z'. v.2 (z /\ z')))
pIsEquivId :: Val
pIsEquivId = bindStage terminalStage $ eval (EnvFib (EnvFib EmptyEnv "id" pId) "refl" pRefl) $
  let c    = Pair "a" rfla
      rfla = foldl1 App ["refl", "A", "a"]
      p0   = PApp (Pr2 "v") (Pr1 "v") "a" "z"
      p1   = PApp (Pr2 "v") (Pr1 "v") "a" ("z" /\ "z'")
  in  BLam "A" $ BLam "a" $ Pair c $ BLam "v" $ BPLam "z" (Pair p0 $ BPLam "z'" p1 (Pr2 "v") rfla) c "v"


---- Abstracted versions

-- | (A B : U) : U
funType :: AtStage (VTy -> VTy -> VTy)
funType a b = foldl1 doApp [pFunType, a, b]

-- | (A : U) : A → A
identity :: AtStage (Val -> Val)
identity a = foldl1 doApp [pId, a]

-- | (A : U) -> isContr A
isContr :: AtStage (VTy -> VTy)
isContr a = foldl1 doApp [pIsContr, a]

-- | (A B : U) (f : A → B) : U
isEquiv :: AtStage (Val -> Val -> Val -> Val)
isEquiv a b f = foldl1 doApp [pIsEquiv, a, b, f]

-- | A : isEquiv (id A)
isEquivId :: AtStage (Val -> Val)
isEquivId a = foldl1 doApp [pIsEquivId, a]

-- | refl (A : U) (a₀ : A) : Path A a₀ a₀
refl :: AtStage (Val -> Val -> Val)
refl a a₀ = foldl1 doApp [pRefl, a, a₀]

-- | fiber (A B : U) (f : A -> B) (y : B) : U
fiber :: AtStage (VTy -> VTy -> Val -> Val -> Val)
fiber a b f y = foldl1 doApp [pFib, a, b, f, y]

-- | idFiber (A : U) (x : A) : fiber A A (id A) x = (x, refl A x)
idFiber :: AtStage (VTy -> Val -> Val)
idFiber a x = VPair x (refl a x)


---- internal combinators

doComp :: AtStage (VI -> VI -> TrIntClosure -> Val -> VSys TrIntClosure -> Val)
doComp r₀ r₁ ℓ u₀ tb = doHComp r₀ r₁ (ℓ $$ r₁) (doCoe r₀ r₁ ℓ u₀)
  $ mapSys tb $ \u -> trIntCl' $ \z -> doCoe (re r₁) (iVar z) (re ℓ) (u $$ iVar z)


--------------------------------------------------------------------------------
---- Basic MLTT Combinators + actions on delayed coe and hcomp

doPr1 :: AtStage (Val -> Val)
doPr1 (VPair s _) = s
doPr1 (VNeu k)    = VPr1 k
doPr1 (VCoeSigma r₀ r₁ i a _ α u₀) = doCoe r₀ r₁ (TrIntClosure i a α) (doPr1 u₀)

doPr2 :: AtStage (Val -> Val)
doPr2 (VPair _ t) = t
doPr2 (VNeu k)    = VPr2 k
doPr2 (VCoeSigma r₀ r₁ z a b α u₀)  = doCoe r₀ r₁
  (trIntCl z $ \z' -> b @ ((iVar z' `for` z) <> α) $$ doCoe r₀ (iVar z') (TrIntClosure z a α) (doPr1 u₀))
  (doPr2 u₀)

doApp :: AtStage (Val -> Val -> Val)
doApp (VLam cl)             v = cl $$ v
doApp (VNeu k)              v = VApp k v
doApp (VSplitPartial f bs)  v = doSplit f bs v
doApp (VCoePartial r0 r1 l) v = doCoePartialApp r0 r1 l v
doApp (VCoePi r₀ r₁ z a b α u₀) a₁ = doCoe r₀ r₁
  (trIntCl z $ \z' -> b @ ((iVar z' `for` z) <> α) $$ doCoe r₁ (iVar z') (TrIntClosure z a α) a₁)
  (u₀ `doApp` doCoe r₁ r₀ (TrIntClosure z a α) a₁)

doPApp :: AtStage (Val -> Val -> Val -> VI -> Val)
doPApp (VPLam cl _ _) _  _  r = cl $$ r
doPApp (VNeu k)       p0 p1 r
  | r === 0   = p0
  | r === 1   = p1
  | otherwise = VPApp k p0 p1 r
doPApp (VCoePath r₀ r₁ i a a₀ a₁ α u₀) _ _ r = -- u₀ : Path a(r₀) a₀(r₀) a₁(r₀)
  doComp r₀ r₁ (TrIntClosure i a α) (doPApp u₀ (a₀ @ (r₀ `for` i)) (a₁ @ (r₁ `for` i)) r) $
    singSys (VCof [(r, 0)]) (TrIntClosure i (extGen i (re a₀)) α)
      <> singSys (VCof [(r, 1)]) (TrIntClosure i (extGen i (re a₁)) α)
doPApp (VHCompPath _ _ _ _ _ _ _) _ _ _ = error "HComp Path"

doSplit :: AtStage (Val -> [VBranch] -> Val -> Val)
doSplit f bs (VCon c as) | Just cl <- lookup c bs = cl $$ as
doSplit f bs (VNeu k)    = VSplit f bs k


--------------------------------------------------------------------------------
---- Extension Types

vExt :: AtStage (Val -> Either (VTy, Val, Val) (VSys (VTy, Val, Val)) -> Val)
vExt a = either fst3 (VExt a)

vExtElm :: AtStage (Val -> Either Val (VSys Val) -> Val)
vExtElm v = either id (VExtElm v)

doExtFun' :: AtStage (Either Val (VSys Val) -> Val -> Val)
doExtFun' ws v = either (`doApp` v) (`doExtFun` v) ws

doExtFun :: AtStage (VSys Val -> Val -> Val)
doExtFun _  (VExtElm v _) = v
doExtFun ws (VNeu k)      = VExtFun ws k


--------------------------------------------------------------------------------
---- Coercion

doCoe :: AtStage (VI -> VI -> TrIntClosure -> Val -> Val)
doCoe r₀ r₁ ℓ u₀ = vCoePartial r₀ r₁ ℓ `doApp` u₀

-- | Smart constructor for VCoePartial
--
-- We maintain the following three invariants:
-- (1) At the current stage r0 != r1 (otherwise coe reduces to the identity)
-- (2) The head constructor of the line of types is known for VCoePartial.
--     Otherwise, the coersion is neutral, and given by VNeuCoePartial.
-- (3) In case of an Ext type, we keep the line fully forced.
--
-- We are very careful (TODO: is this neccessary?): We peak under the closure
-- to see the type. In the cases where we have restriction stable type formers,
-- we can safely construct a VCoePartial value to be evaluated when applied.
-- Otherwise, we force the delayed restriction, and check again.
--
-- TODO: what is with U?
vCoePartial :: AtStage (VI -> VI -> TrIntClosure -> Val)
vCoePartial r0 r1 | r0 === r1 = \l -> pId `doApp` (l $$ r0)
vCoePartial r0 r1 = go False
  where
    go :: Bool -> TrIntClosure -> Val
    go forced l@(TrIntClosure i a _) = case a of
      VSum{}   -> VCoePartial r0 r1 l
      VPi{}    -> VCoePartial r0 r1 l
      VSigma{} -> VCoePartial r0 r1 l
      VPath{}  -> VCoePartial r0 r1 l
      VNeu k   | forced     -> VNeuCoePartial r0 r1 (TrNeuIntClosure i k)
      VExt{}   | forced     -> VCoePartial r0 r1 l -- we keep Ext types forced
      _        | not forced -> go True (force l)

-- | The actual implementation of coe. Should *only* be called by doApp.
doCoePartialApp :: AtStage (VI -> VI -> TrIntClosure -> Val -> Val)
doCoePartialApp r0 r1 = \case -- r0 != r1 by (1) ; by (2) these are all cases
  TrIntClosure z (VExt a bs) IdRestr -> doCoeExt r0 r1 z a bs -- by (3) restr (incl. eqs)
  TrIntClosure z (VSum _ _)  _       -> error "TODO: copy + simplify"
  l@(TrIntClosure _ VPi{}    _)      -> VCoe r0 r1 l
  l@(TrIntClosure _ VSigma{} _)      -> VCoe r0 r1 l
  l@(TrIntClosure _ VPath{}  _)      -> VCoe r0 r1 l
  l@(TrIntClosure _ (VNeu _) _) -> error "doCoe with Neu"

doCoeExt :: AtStage (VI -> VI -> Gen -> VTy -> VSys (VTy, Val, Val) -> Val -> Val)
doCoeExt = error "TODO: copy doCoeExt"


--------------------------------------------------------------------------------
---- HComp

-- | HComp where the system could be trivial
doHComp' :: AtStage (VI -> VI -> VTy -> Val -> Either TrIntClosure (VSys TrIntClosure) -> Val)
doHComp' r₀ r₁ a u0 = either ($$ r₁) (doHComp r₀ r₁ a u0)

doHComp :: AtStage (VI -> VI -> VTy -> Val -> VSys TrIntClosure -> Val)
doHComp r₀ r₁ _ u₀ _ | r₀ === r₁ = u₀
doHComp r₀ r₁ a u₀ tb = case a of
  VNeu k        -> VNeuHComp r₀ r₁ k u₀ tb
  VPi a b       -> VHCompPi r₀ r₁ a b u₀ tb
  VSigma a b    -> VHCompSigma r₀ r₁ a b u₀ tb
  VPath a a₀ a₁ -> VHCompPath r₀ r₁ a a₀ a₁ u₀ tb
  VSum d lbl    -> doHCompSum r₀ r₁ d lbl u₀ tb
  VExt a bs     -> doHCompExt r₀ r₁ a bs u₀ tb
  VU            -> doHCompU r₀ r₁ u₀ tb


---- Cases for positive types

doHCompSum :: AtStage (VI -> VI -> Val -> [VLabel] -> Val -> VSys TrIntClosure -> Val)
doHCompSum r₀ r₁ _ lbl (VCon c as) = error "TODO" -- VCon c 
doHCompSum r₀ r₁ _ lbl (VNeu k)    = error "TODO: copy doHCompSum"

unConSys :: AtStage (Name -> VSys IntClosure -> Maybe (VSys [IntClosure]))
unConSys = error "TODO" -- TODO: we could selectively force here as-well!

doHCompExt :: AtStage (VI -> VI -> VTy -> VSys (VTy, Val, Val) -> Val -> VSys TrIntClosure -> Val)
doHCompExt = error "TODO: copy doHCompExt"

doHCompU :: AtStage (VI -> VI -> Val -> VSys TrIntClosure -> Val)
doHCompU = error "TODO: copy doHCompU"


--------------------------------------------------------------------------------
---- Restriction Operations

instance Restrictable Val where
  act :: AtStage (Restr -> Val -> Val)
  act f = \case
    VU -> VU

    VPi a b -> VPi (a @ f) (b @ f)
    VLam cl -> VLam (cl @ f)

    VSigma a b -> VSigma (a @ f) (b @ f)
    VPair u v  -> VPair (u @ f) (v @ f)

    VPath a a0 a1  -> VPath (a @ f) (a0 @ f) (a1 @ f)
    VPLam cl p0 p1 -> VPLam (cl @ f) (p0 @ f) (p1 @ f)

    VCoePartial r0 r1 l -> vCoePartial (r0 @ f) (r1 @ f) (l @ f)

    VCoe r0 r1 l u0      -> vCoePartial (r0 @ f) (r1 @ f) (l @ f) `doApp` (u0 @ f)
    VHComp r0 r1 a u0 tb -> doHComp' (r0 @ f) (r1 @ f) (a @ f) (u0 @ f) (tb @ f)

    VExt a bs    -> vExt (a @ f) (bs @ f)
    VExtElm v ws -> vExtElm (v @ f) (ws @ f)

    VSum a lbl         -> VSum (a @ f) (lbl @ f)
    VCon c as          -> VCon c (as @ f)
    VSplitPartial v bs -> VSplitPartial (v @ f) (bs @ f)

    VNeu k -> k @ f

instance Restrictable Neu where
  -- a neutral can get "unstuck" when restricted
  type Alt Neu = Val

  act :: AtStage (Restr -> Neu -> Val)
  act f = \case
    NVar x -> VVar x

    NApp k v -> doApp (k @ f) (v @ f)

    NPr1 k -> doPr1 (k @ f)
    NPr2 k -> doPr2 (k @ f)

    NPApp k a₀ a₁ r -> doPApp (k @ f) (a₀ @ f) (a₁ @ f) (r @ f)

    NCoePartial r₀ r₁ cl -> vCoePartial (r₀ @ f) (r₁ @ f) (cl @ f)
    NHComp r₀ r₁ k u₀ tb -> doHComp' (r₀ @ f) (r₁ @ f) (k @ f) (u₀ @ f) (tb @ f)
    -- NHCompSum :: VI -> VI -> VTy -> [VLabel] -> Neu -> VSys IntClosure -> Neu
    NExtFun ws k -> doExtFun' (ws @ f) (k @ f)

    NSplit g bs k -> doSplit (g @ f) (bs @ f) (k @ f)

instance Restrictable a => Restrictable (VSys a) where
  type Alt (VSys a) = Either (Alt a) (VSys (Alt a))

  act :: AtStage (Restr -> VSys a -> Either (Alt a) (VSys (Alt a)))
  act f (VSys bs) = simplifySys $ VSys [ (φ', extCof φ' (a @ f)) | (φ, a) <- bs, let φ' = φ @ f ]

instance Restrictable VLabel where
  act :: AtStage (Restr -> VLabel -> VLabel)
  act f = fmap (@ f)

instance Restrictable VBranch where
  act :: AtStage (Restr -> VBranch -> VBranch)
  act f = fmap (@ f)

instance Restrictable Closure where
  -- | ((λx.t)ρ)f = (λx.t)(ρf)
  act :: AtStage (Restr -> Closure -> Closure)
  act f (Closure x t env) = Closure x t (env @ f)

instance Restrictable IntClosure where
  -- | ((λi.t)ρ)f = (λi.t)(ρf)
  act :: AtStage (Restr -> IntClosure -> IntClosure)
  act f (IntClosure x t env) = IntClosure x t (env @ f)

instance Restrictable SplitClosure where
  act :: AtStage (Restr -> SplitClosure -> SplitClosure)
  act f (SplitClosure xs t env) = SplitClosure xs t (env @ f)

instance Restrictable TrIntClosure where
  act :: AtStage (Restr -> TrIntClosure -> TrIntClosure)
  act f (TrIntClosure i v g) = TrIntClosure i v (f `comp` g) -- NOTE: original is flipped

instance Restrictable TrNeuIntClosure where
  type Alt TrNeuIntClosure = TrIntClosure

  act :: AtStage (Restr -> TrNeuIntClosure -> TrIntClosure)
  act f (TrNeuIntClosure i k) = TrIntClosure i (VNeu k) f

instance Restrictable VTel where
  act :: AtStage (Restr -> VTel -> VTel )
  act f (VTel ts rho) = VTel ts (rho @ f)

instance Restrictable Env where
  act :: AtStage (Restr -> Env -> Env)
  act f = \case
    EmptyEnv          -> EmptyEnv
    EnvFib env x v    -> EnvFib (env @ f) x (v @ f)
    EnvDef env x t ty -> EnvDef (env @ f) x t ty
    EnvInt env i r    -> EnvInt (env @ f) i (r @ f)

instance Restrictable a => Restrictable [a] where
  type Alt [a] = [Alt a]

  act :: AtStage (Restr -> [a] -> [Alt a])
  act f = map (@ f)

instance (Restrictable a, Restrictable b, Restrictable c) => Restrictable (a, b, c) where
  type Alt (a, b, c) = (Alt a, Alt b, Alt c)

  act :: AtStage (Restr -> (a, b, c) -> (Alt a, Alt b, Alt c))
  act f (x, y, z) = (x @ f, y @ f, z @ f)
