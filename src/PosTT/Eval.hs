-- | Evaluation of Terms into Semantic Values
module PosTT.Eval where

import Algebra.Lattice

import Control.Applicative

import Data.Bifunctor
import Data.Either.Extra (fromRight')
import Data.Tuple.Extra (fst3, snd3, thd3)

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
lookupFib (EnvFib _ y v)     x | y == x = v
lookupFib ρ@(EnvDef _ y t _) x | y == x = eval ρ t -- recursive definition
lookupFib (EnvCons ρ _ _)    x = lookupFib ρ x

lookupInt :: Env -> Gen -> VI
lookupInt (EnvInt _ y r)  x | y == x = r
lookupInt (EnvCons ρ _ _) x = ρ `lookupInt` x

reAppDef :: AtStage (Name -> Env -> Val)
reAppDef d (EnvDef _   x _ _) | x == d = VVar d
reAppDef d (EnvFib rho x v)   | x /= d = reAppDef d rho `doApp` v


--------------------------------------------------------------------------------
---- Eval

closedEval :: Tm -> Val
closedEval = bindStage terminalStage $ eval EmptyEnv

eval :: AtStage (Env -> Tm -> Val)
eval rho = \case
  U            -> VU
  Var x        -> rho `lookupFib` x
  Let d t ty s -> eval (EnvDef rho d t ty) s

  Pi a b  -> VPi (eval rho a) (evalBinder rho b)
  Lam t   -> VLam (evalBinder rho t)
  App s t -> eval rho s `doApp` eval rho t

  Sigma a b -> VSigma (eval rho a) (evalBinder rho b)
  Pair s t  -> VPair (eval rho s) (eval rho t)
  Pr1 t     -> doPr1 (eval rho t)
  Pr2 t     -> doPr2 (eval rho t)

  Path a s t     -> VPath (eval rho a) (eval rho s) (eval rho t)
  PLam t t0 t1   -> VPLam (evalIntBinder rho t) (eval rho t0) (eval rho t1)
  PApp t t0 t1 r -> doPApp (eval rho t) (eval rho t0) (eval rho t1) (evalI rho r)

  Coe r0 r1 l         -> doCoePartial (evalI rho r0) (evalI rho r1) (evalTrIntBinder rho l)
  HComp r0 r1 a u0 tb -> doHComp' (evalI rho r0) (evalI rho r1) (eval rho a) (eval rho u0) (evalSys evalTrIntBinder rho tb)

  Ext a bs    -> vExt (eval rho a) (evalSys eval3 rho bs)
  ExtElm s ts -> vExtElm (eval rho s) (evalSys eval rho ts)
  ExtFun ws t -> doExtFun' (evalSys eval rho ws) (eval rho t)

  Sum d lbl  -> VSum (reAppDef d rho) (map (evalLabel rho) lbl)
  Con c args -> VCon c (map (eval rho) args)
  Split f bs -> VSplitPartial (reAppDef f rho) (map (evalBranch rho) bs)

evalI :: Env -> I -> VI
evalI rho = \case
  Sup r s -> evalI rho r \/ evalI rho s
  Inf r s -> evalI rho r /\ evalI rho s
  I0      -> bot
  I1      -> top
  IVar i  -> rho `lookupInt` i

eval3 :: AtStage (Env -> (Tm, Tm, Tm) -> (Val, Val, Val))
eval3 rho (s, t, r) = (eval rho s, eval rho t, eval rho r)

evalCof :: AtStage (Env -> Cof -> VCof)
evalCof rho (Cof eqs) = VCof (map (bimap (evalI rho) (evalI rho)) eqs)

evalSys :: AtStage (AtStage (Env -> a -> b) -> Env -> Sys a -> Either b (VSys b))
evalSys ev rho (Sys bs) = simplifySys (VSys bs')
  where bs' = [ (phi', extCof phi' (ev (re rho) a)) | (phi, a) <- bs, let phi' = evalCof rho phi ]

evalBinder :: AtStage (Env -> Binder Tm -> Closure)
evalBinder rho (Binder x t) = Closure x t rho

evalIntBinder :: AtStage (Env -> IntBinder Tm -> IntClosure)
evalIntBinder rho (IntBinder i t) = IntClosure i t rho

-- | We evaluate a transparent binder, by evaluating the *open* term t under
--   the binder. (TODO: How can i be already used if the terms have no shadowing?)
evalTrIntBinder :: AtStage (Env -> TrIntBinder Tm -> TrIntClosure)
evalTrIntBinder rho (TrIntBinder i t) = trIntCl i $ \i' -> eval (EnvInt rho i (iVar i')) t

evalSplitBinder :: AtStage (Env -> SplitBinder -> SplitClosure)
evalSplitBinder rho (SplitBinder xs t) = SplitClosure xs t rho

evalBranch :: AtStage (Env -> Branch -> VBranch)
evalBranch rho (Branch c t) = (c, evalSplitBinder rho t)

evalLabel :: AtStage (Env -> Label -> VLabel)
evalLabel rho (Label c tel) = (c, evalTel rho tel)

evalTel :: AtStage (Env -> Tel -> VTel)
evalTel rho (Tel ts) = VTel ts rho


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

rebindI :: AtStage (AtStage (Gen -> Val -> Val) -> TrIntClosure -> TrIntClosure)
rebindI k c@(TrIntClosure i _ _) = trIntCl i $ \j -> k j (c $$ iVar j)


--------------------------------------------------------------------------------
---- Telescope Utilities

headVTel :: AtStage (VTel -> VTy)
headVTel (VTel ((_, a):_) ρ) = eval ρ a

tailVTel :: VTel -> Val -> VTel
tailVTel (VTel ((x, _):tel) ρ) v = VTel tel (EnvFib ρ x v)

pattern VTelNil :: VTel
pattern VTelNil <- VTel [] _


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


---- Internal Combinators

-- | A partial element of a contractible type can be extended to a total one
-- wid A (a₀ , h) [ψ ↪ u] = hcomp 0 1 A [ψ ↪ h(u)] a₀
-- where (a₀ , h) : isContr A so a₀ : A and h : const a₀ ∼ id
wid :: AtStage (Val -> Val -> VSys Val -> Val)
wid a isContrA sys = doHComp 0 1 a a₀ $ mapSys sys
    $ \u -> trIntCl' $ \z -> doPApp (re h `doApp` u) (re a₀) u (iVar z)
  where a₀ = doPr1 isContrA ; h = doPr2 isContrA

wid' :: AtStage (Val -> Val -> Either Val (VSys Val) -> Val)
wid' a isContrA = either id (wid a isContrA)

doComp :: AtStage (VI -> VI -> TrIntClosure -> Val -> VSys TrIntClosure -> Val)
doComp r₀ r₁ ℓ u₀ tb = doHComp r₀ r₁ (ℓ $$ r₁) (doCoe r₀ r₁ ℓ u₀)
  $ mapSys tb $ \u -> trIntCl' $ \z -> doCoe (re r₁) (iVar z) (re ℓ) (u $$ iVar z)


--------------------------------------------------------------------------------
---- Basic MLTT Combinators + actions on delayed coe and hcomp

doPr1 :: AtStage (Val -> Val)
doPr1 (VPair s _) = s
doPr1 (VNeu k)    = VPr1 k
doPr1 (VCoeSigma r₀ r₁ i a _ α u₀) = doCoe r₀ r₁ (TrIntClosure i a α) (doPr1 u₀)
doPr1 (VHCompSigma r₀ r₁ a _ u₀ tb) = doHComp r₀ r₁ a (doPr1 u₀)
  (mapSys tb $ rebindI $ \_ u -> doPr1 u)

doPr2 :: AtStage (Val -> Val)
doPr2 (VPair _ t) = t
doPr2 (VNeu k)    = VPr2 k
doPr2 (VCoeSigma r₀ r₁ z a b α u₀)  = doCoe r₀ r₁
  (trIntCl z $ \z' -> b @ ((iVar z' `for` z) <> α) $$ doCoe r₀ (iVar z') (TrIntClosure z a α) (doPr1 u₀))
  (doPr2 u₀)
doPr2 (VHCompSigma r₀ r₁ a b u₀ tb) = doComp r₀ r₁
  (trIntCl' $ \z -> b $$ doHComp r₀ (iVar z) a (doPr1 u₀) (mapSys tb $ rebindI $ \_ u -> doPr1 u))
  (doPr2 u₀)
  (mapSys tb $ rebindI $ \_ u -> doPr2 u)

doApp :: AtStage (Val -> Val -> Val)
doApp (VLam cl)             v = cl $$ v
doApp (VNeu k)              v = VApp k v
doApp (VSplitPartial f bs)  v = doSplit f bs v
doApp (VCoePartial r0 r1 l) v = doCoePartialApp r0 r1 l v
doApp (VCoePi r₀ r₁ z a b α u₀) a₁ = doCoe r₀ r₁
  (trIntCl z $ \z' -> b @ ((iVar z' `for` z) <> α) $$ doCoe r₁ (iVar z') (TrIntClosure z a α) a₁)
  (u₀ `doApp` doCoe r₁ r₀ (TrIntClosure z a α) a₁)
doApp (VHCompPi r₀ r₁ _ b u₀ tb) a = doHComp r₀ r₁ (b $$ a) (u₀ `doApp` a)
  (mapSys tb $ rebindI $ \_ u -> u `doApp` re a)

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
doPApp (VHCompPath r₀ r₁ a a₀ a₁ u₀ tb) _ _ r = doHComp' r₀ r₁ a (doPApp u₀ a₀ a₁ r) $ simplifySys $
  mapSys tb (rebindI $ \_ u -> doPApp u (re a₀) (re a₁) (re r))
    <> singSys (VCof [(r, bot)]) (trIntCl' $ \_ -> re a₀) <> singSys (VCof [(r, top)]) (trIntCl' $ \_ -> re a₁)

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
doCoe r₀ r₁ ℓ u₀ = doCoePartial r₀ r₁ ℓ `doApp` u₀

-- | Smart constructor for VCoePartial
--
-- We maintain the following three invariants:
-- (1) At the current stage r0 != r1 (otherwise coe reduces to the identity)
-- (2) The head constructor of the line of types is known for VCoePartial.
--     Otherwise, the coercion is neutral, and given by VNeuCoePartial.
-- (3) In case of an Ext type, we keep the line fully forced.
--
-- We are very careful: We peak under the closure to see the type.
-- In the cases where we have restriction stable type formers,
-- we can safely construct a VCoePartial value to be evaluated when applied.
-- Otherwise, we force the delayed restriction, and check again.
doCoePartial :: AtStage (VI -> VI -> TrIntClosure -> Val)
doCoePartial r0 r1 | r0 === r1 = \ℓ -> pId `doApp` (ℓ $$ r0) -- could just be id closure
doCoePartial r0 r1 = go False
  where
    go :: Bool -> TrIntClosure -> Val
    go forced l@(TrIntClosure i a _) = case a of
      VU{}     -> identity VU
      VSum{}   -> VCoePartial r0 r1 l
      VPi{}    -> VCoePartial r0 r1 l
      VSigma{} -> VCoePartial r0 r1 l
      VPath{}  -> VCoePartial r0 r1 l
      VNeu k   | forced     -> VNeuCoePartial r0 r1 (TrNeuIntClosure i k)
      VExt{}   | forced     -> VCoePartial r0 r1 l -- we keep Ext types forced (3) -- REMARK: this slows "flip test" significantly
      _        | not forced -> go True (force l)

-- | The actual implementation of coe. Should *only* be called by doApp.
doCoePartialApp :: AtStage (VI -> VI -> TrIntClosure -> Val -> Val)
doCoePartialApp r0 r1 = \case -- r0 != r1 by (1) ; by (2) these are all cases
  TrIntClosure z (VExt a bs) IdRestr -> doCoeExt r0 r1 z a bs -- by (3) restr (incl. eqs)
  TrIntClosure z (VSum d lbl) f      -> doCoeSum r0 r1 z d lbl f
  l@(TrIntClosure _ VPi{}    _)      -> VCoe r0 r1 l
  l@(TrIntClosure _ VSigma{} _)      -> VCoe r0 r1 l
  l@(TrIntClosure _ VPath{}  _)      -> VCoe r0 r1 l
  l@(TrIntClosure _ (VNeu _) _)      -> impossible "doCoe with Neu"

-- | Coercion for extension types. Note that the given type is assumed to be fully restricted.
doCoeExt :: AtStage (VI -> VI -> Gen -> VTy -> VSys (VTy, Val, Val) -> Val -> Val)
doCoeExt r₀ r₁ z a bs u₀ = -- a, bs depend on z!
  let a₀ = doExtFun' (mapSys bs snd3 @ (r₀ `for` z)) u₀
      a' = trIntCl z $ \z' -> doCoe r₀ (iVar z') (TrIntClosure z a IdRestr) a₀
      b'p = mapSys (mapSysCof (forAll z) bs) $ \(b, w, _) -> -- here we could have simplification!
              let b' = trIntCl' $ \z' -> doCoe (re r₀) (iVar z') (TrIntClosure z (extGen z (re b)) IdRestr) (re u₀)
                  p  = doCoe (re r₀) (re r₁)
                         (TrIntClosure z (extGen z (VPath (re a) (re a' $$ iVar z) (re w `doApp` (b' $$ iVar z)))) IdRestr)
                         (refl (a @ (r₀ `for` z)) (re a₀))
              in  (b', p)

      -- system containing the element e of the fiber w a, as well as, w and a to allow calculation of endpoints of e.2
      b₁p₁ = mapSys' (bs @ (r₁ `for` z)) $ \(b, w, w') ->
               let a'r₁ = a' $$ re r₁
               in  ( w
                   , a'r₁
                   , wid' (fiber b (re a) w a'r₁) (w' `doApp` a'r₁) $ simplifySys $ -- the above system is only used here and simplified
                       consSys (mapSys b'p $ \(b', p) -> VPair (b' $$ re r₁) p)
                         (VCof [(re r₀, re r₁)]) (idFiber (re a) (re a₀))
                   )

      -- a₁ is only needed of above system for b₁ is non-trivial
      a₁ = doHComp' 0 1 (a @ (r₁ `for` z)) (a' $$ r₁) $ simplifySys $
             consSys (mapSys (fromRight' b₁p₁) $ \(w, a'r₁, fib) -> trIntCl' $ \z' -> doPApp (doPr2 fib) (w `doApp` doPr1 fib) a'r₁ (iVar z'))
               (VCof [(re r₀, re r₁)]) (trIntCl' $ \_ -> re a₀)
  in  vExtElm a₁ (mapSys' b₁p₁ (doPr1 . thd3))

-- | Coercion in a sum type. Note that the type given by (d, lbl) has to be restricted by f.
doCoeSum :: AtStage (VI -> VI -> Gen -> VTy -> [VLabel] -> Restr -> Val -> Val)
doCoeSum r₀ r₁ i d lbl f (VCon c as) | Just tel <- lookup c lbl = VCon c (doCoeTel r₀ r₁ i tel f as)
doCoeSum _  _  _ _ _   _ (VNeu _)    = error "TODO: neutral for coe in Sum type"

doCoeTel :: AtStage (VI -> VI -> Gen -> VTel -> Restr -> [Val] -> [Val])
doCoeTel _ _ _ VTelNil _ [] = []
doCoeTel _ _ _ _       _ _  = error "TODO: copy"


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

-- Extension Types

doHCompExt :: AtStage (VI -> VI -> VTy -> VSys (VTy, Val, Val) -> Val -> VSys TrIntClosure -> Val)
doHCompExt r₀ r₁ a bs u₀ tb =
  let a₀ = doExtFun (mapSys bs snd3) u₀
      -- we construct the line and the mapped version together: [ ψ ↪ (b', λᵢ.w(b'i)) ]
      b' = mapSys bs $ \(b, w, _) ->
             let b'' = trIntCl' $ \i -> doHComp' (re r₀) (iVar i) b (re u₀) (re tb)
             in  (b'', trIntCl' $ \i -> w `doApp` (b'' $$ iVar i))
      sys = mapSys tb $ rebindI $ \_ -> doExtFun' (re $ mapSys bs snd3) -- [ ψ ↪ λᵢ. extFun [φ ↪ w] (u i) ]
      a₁ = doHComp r₀ r₁ a a₀ (sys `unionSys` mapSys b' snd) -- ... ∪ [ φ ↪ λᵢ.w(b' i) ]
  in  VExtElm a₁ (mapSys b' (($$ re r₁) . fst))


-- Universe

doHCompU :: AtStage (VI -> VI -> Val -> VSys TrIntClosure -> Val)
doHCompU r₀ r₁ a₀ tb =
  let vs = mapSys tb $ \a ->
             let r₀η = re r₀ ; r₁η = re r₁ ; ar₁η = a $$ r₁η
                 ℓ = trIntCl' $ \z -> isEquiv (a $$ iVar z) (a $$ r₀η) (VCoePartial (iVar z) r₀η a)
             in  (ar₁η, VCoePartial r₁η r₀η a, doCoe r₀η r₁η ℓ (isEquivId ar₁η))
  in vExt a₀ $ simplifySys $ consSys vs (VCof [(r₀, r₁)]) (a₀, identity a₀, isEquivId a₀)


-- Sum Types

doHCompSum :: AtStage (VI -> VI -> Val -> [VLabel] -> Val -> VSys TrIntClosure -> Val)
doHCompSum r₀ r₁ _ lbl (VCon c as) tb
  | Just tel <- lookup c lbl, Just tb' <- unConSys c tb = VCon c (doHCompTel r₀ r₁ tel as tb')
doHCompSum r₀ r₁ d lbl (VNeu k)    tb = VNeuHCompSum r₀ r₁ d lbl k tb

unConSys :: AtStage (Name -> VSys TrIntClosure -> Maybe (VSys [TrIntClosure]))
unConSys c tb = go tb <|> go (mapSys tb force) -- TODO: do we want selective forcing here?
  where
    go :: AtStage (VSys TrIntClosure -> Maybe (VSys [TrIntClosure]))
    go tb' = mapSysM tb' $ \case


-- Telescopes

doHCompTel :: AtStage (VI -> VI -> VTel -> [Val] -> VSys [TrIntClosure] -> [Val])
doHCompTel _ _ VTelNil [] _ = []
doHCompTel _ _ _       _  _ = error "TODO: copy doHCompTel"


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

    VCoePartial r0 r1 l -> doCoePartial (r0 @ f) (r1 @ f) (l @ f)

    VCoe r0 r1 l u0      -> doCoePartial (r0 @ f) (r1 @ f) (l @ f) `doApp` (u0 @ f)
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

    NCoePartial r₀ r₁ cl       -> doCoePartial (r₀ @ f) (r₁ @ f) (cl @ f)
    NHComp r₀ r₁ k u₀ tb       -> doHComp' (r₀ @ f) (r₁ @ f) (k @ f) (u₀ @ f) (tb @ f)
    NHCompSum r₀ r₁ d lbl k tb -> doHComp' (r₀ @ f) (r₁ @ f) (VSum (d @ f) (lbl @ f)) (k @ f) (tb @ f)

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

instance Restrictable (Name, EnvEntry) where
  act :: AtStage (Restr -> (Name, EnvEntry) -> Alt (Name, EnvEntry))
  act f = fmap (@ f)

instance Restrictable EnvEntry where
  act :: AtStage (Restr -> EnvEntry -> EnvEntry)
  act f = \case
    EntryFib v    -> EntryFib (v @ f)
    EntryDef t ty -> EntryDef t ty
    EntryInt r    -> EntryInt (r @ f)

instance Restrictable a => Restrictable [a] where
  type Alt [a] = [Alt a]

  act :: AtStage (Restr -> [a] -> [Alt a])
  act f = map (@ f)

instance (Restrictable a, Restrictable b, Restrictable c) => Restrictable (a, b, c) where
  type Alt (a, b, c) = (Alt a, Alt b, Alt c)

  act :: AtStage (Restr -> (a, b, c) -> (Alt a, Alt b, Alt c))
  act f (x, y, z) = (x @ f, y @ f, z @ f)
