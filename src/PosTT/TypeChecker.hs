module PosTT.TypeChecker where

import           Control.Monad.Reader
import           Control.Monad.Except

import           Data.Either (fromRight)
import           Data.List (sortOn)
import           Data.Tuple.Extra (uncurry3, first3, second3)

import           PosTT.Common
import           PosTT.Conversion
import           PosTT.Errors
import           PosTT.Eval
import qualified PosTT.Frontend.PreTerms as P
import           PosTT.Frontend.PreTerms (PTm)
import           PosTT.Poset
import           PosTT.Pretty
import           PosTT.Quotation
import           PosTT.Terms
import           PosTT.Values

import           Debug.Trace


--------------------------------------------------------------------------------
---- Type Checking Monad

-- | Type checking context
data Cxt = Cxt { env :: Env, types :: [(Name, VTy)], intVars :: [Gen], pos :: SrcSpan }

emptyCxt :: Cxt
emptyCxt = Cxt EmptyEnv [] [] Nothing

newtype TypeChecker a = TypeChecker { unTypeChecker :: ReaderT Cxt (Either TypeError) a }
  deriving (Functor, Applicative, Monad, MonadReader Cxt, MonadError TypeError)

instance MonadFail TypeChecker where
  fail :: String -> TypeChecker a
  fail s = asks pos >>= \ss -> throwError (TypeErrorMsg ss s)

runTC :: Cxt -> AtStage (TypeChecker a) -> Either TypeError a
runTC cxt ma = bindStage terminalStage (runReaderT (unTypeChecker ma) cxt)


--------------------------------------------------------------------------------
---- Utility Functions

-- | Extends context Γ with a definition to a context Γ,(x=t:a)
extDef :: Name -> Tm -> Ty -> VTy -> Cxt -> Cxt
extDef x t a va (Cxt ρ ts is pos) = Cxt (EnvDef ρ x t a) ((x, va):ts) is pos

-- | Extends context Γ with a (fibrant) value to a context Γ,(x=v:a)
extFib :: Name -> Val -> VTy -> Cxt -> Cxt
extFib x v a (Cxt ρ ts is pos) = Cxt (EnvFib ρ x v) ((x, a):ts) is pos

-- | Extends context Γ with a value of type I to a context Γ,(i=r:I)
extInt :: Gen -> VI -> Cxt -> Cxt
extInt i r (Cxt ρ ts is pos) = Cxt (EnvInt ρ i r) ts (i:is) pos


---- introduction of free variables

-- | Extends the context Γ with a free variable to a context Γ,(x=x:a)
bindFibVar :: AtStage (Name -> VTy -> AtStage (Val -> TypeChecker a) -> TypeChecker a)
bindFibVar x a k = extName x (local (extFib x (VVar x) a) (k (VVar x)))

bindFibVars :: AtStage ([Name] -> VTel -> AtStage ([Val] -> TypeChecker a) -> TypeChecker a)
bindFibVars []     VTelNil     k = k []
bindFibVars (x:xs) tel         k =
  bindFibVar x (headVTel tel) (\v -> bindFibVars xs (tailVTel tel v) (\vs -> k (v:vs)))
bindFibVars _      _           _ = impossible "bindFibVars: Names and telescope do not match!"

-- | Extends the context Γ with a free variable to a context Γ,(i=i:I)
bindIntVar :: AtStage (Gen -> AtStage (VI -> TypeChecker a) -> TypeChecker a)
bindIntVar i k = extGen i (local (extInt i (iVar i)) (k (iVar i)))

bindIntVars :: AtStage ([Gen] -> AtStage ([VI] -> TypeChecker a) -> TypeChecker a)
bindIntVars []     k = k []
bindIntVars (i:is) k = bindIntVar i $ \i' -> bindIntVars is (k . (i':))

bindFibIntVars :: AtStage ([Name] -> VHTel -> AtStage ([Val] -> [VI] -> VSys Val -> TypeChecker a) -> TypeChecker a)
bindFibIntVars []     (VHTelNil (Right sys)) k = k [] [] sys
bindFibIntVars (n:ns) (VHTelConsFib a tel)   k =
  bindFibVar n a $ \v -> bindFibIntVars ns (tel v) $ \vs -> k (v:vs)
bindFibIntVars (n:ns) (VHTelConsInt tel)     k =
  bindIntVar n $ \i -> bindFibIntVars ns (tel i) $ \vs is -> k vs (i:is)
bindFibIntVars _      _                      _ = impossible "bindFibIntVars: Names and telescope do not match!"


---- lookup types in context

checkIntVar :: Name -> TypeChecker I
checkIntVar i = asks (elem i . intVars) >>= \case
  True  -> return (IVar i)
  False -> fail $ show i ++ " is not an interval variable!"

checkFibVar :: Name -> TypeChecker VTy
checkFibVar x = asks (lookup x . types) >>= \case
  Just t  -> return t
  Nothing -> fail $ show x ++ " is not a fibrant variable!"


---- Evaluation and Quotation using context

-- | Given one of the "evaluation functions" from PosTT.Eval
--   we can run it using the environment form the type checker.
evalTC :: AtStage (AtStage (Env -> a -> b) -> a -> TypeChecker b)
evalTC ev t = asks ((`ev` t) . env)

-- | Tests two given a for conversion and produces a TypeError based on the given function.
convTC :: (ReadBack a, Conv a) => AtStage ((SrcSpan -> Quot a -> Quot a -> ConvError -> TypeError) -> a -> a -> TypeChecker ())
convTC e x y = case x `conv` y of
  Left err -> asks pos >>= \ss -> throwError $ e ss (readBack x) (readBack y) err
  Right () -> return ()


---- Source Position handling and errors

at :: SrcSpan -> TypeChecker a -> TypeChecker a
at ss = local (\cxt -> cxt{pos = ss})

atArgPos :: (PTm -> TypeChecker a) -> (PTm -> TypeChecker a)
atArgPos k t = at (P.srcSpan t) (k t)

hoistEither :: Either TypeError a -> TypeChecker a
hoistEither = either throwError pure


--------------------------------------------------------------------------------
---- Matching Types

isU :: AtStage (VTy -> TypeChecker ())
isU VU = return ()
isU t  = fail $ "Expected U, got " ++ prettyVal t

isExt :: AtStage (VTy -> TypeChecker (VTy, VSys (VTy, Val, Val)))
isExt (VExt a bs) = return (a, bs)
isExt t           = fail $ "Expected Ext-type, got " ++ prettyVal t

isPi :: AtStage (VTy -> TypeChecker (VTy, Closure))
isPi (VPi a b) = return (a, b)
isPi t         = fail $ "Expected Π-type, got " ++ prettyVal t

isPath :: AtStage (VTy -> TypeChecker (TrIntClosure, Val, Val))
isPath (VPath a a0 a1) = return (a, a0, a1)
isPath t               = fail $ "Expected Path-type, got " ++ prettyVal t

isPiOrPath :: AtStage (VTy -> TypeChecker (Either (VTy, Closure) (TrIntClosure, Val, Val)))
isPiOrPath (VPi a b)       = return $ Left (a, b)
isPiOrPath (VPath a a0 a1) = return $ Right (a, a0, a1)
isPiOrPath t               = fail $ "Expected Path-Type or Π-Type, got " ++ prettyVal t

isSigma :: AtStage (VTy -> TypeChecker (VTy, Closure))
isSigma (VSigma a b) = return (a, b)
isSigma t            = fail $ "Expected Σ-Type, got " ++ prettyVal t

isSum :: AtStage (VTy -> TypeChecker (Either (Val, [VLabel]) (Val, [VHLabel])))
isSum (VSum d lbl)  = return $ Left (d, lbl)
isSum (VHSum d lbl) = return $ Right (d, lbl)
isSum t             = fail $ "Expected (Higher) Sum-type, got " ++ prettyVal t


--------------------------------------------------------------------------------
---- Core Bidirectional type checker

-- | Checks whether the given term has the given type.
--
-- If the term is a constructor, then it should be handled in this case.
-- TODO: should types be in this case? We could infer them. See MiniTT vs other CTT impls
check :: AtStage (PTm -> VTy -> TypeChecker Tm)
check = flip $ \ty -> atArgPos $ \case
  P.Let _ x s a t -> do
    (a', va) <- checkAndEval a VU
    s' <- check s va
    Let x s' a' <$> local (extDef x s' a' va) (check t ty)
  P.U _ -> do
    () <- isU ty
    return U
  P.Pi _ x a b -> do
    () <- isU ty
    (a', va) <- checkAndEval a VU
    b' <- bindFibVar x va (\_ -> check b VU)
    return $ BPi a' x b'
  P.Sigma _ x a b -> do
    () <- isU ty
    (a', va) <- checkAndEval a VU
    b' <- bindFibVar x va (\_ -> check b VU)
    return $ BSigma a' x b'
  P.Path _ i a a₀ a₁ -> do
    () <- isU ty
    (a', va) <- bindIntVar i $ \_ -> checkAndEval a VU
    BPath i a' <$> check a₀ (va @  (0 `for` i)) <*> check a₁ (va @  (1 `for` i))
  P.Sum _ d cs -> do
    () <- isU ty
    Sum d <$> mapM checkLabel cs
  P.HSum _ d cs -> do
    () <- isU ty
    vd <- evalTC reAppDef d
    HSum d <$> checkHLabels vd cs
  P.Ext _ a sys -> do
    () <- isU ty
    (a', va) <- checkAndEval a VU

    sys' <- checkSys sys $ \_ (b, e, p) -> do
      (b', vb) <- checkAndEval b VU
      let vaη = re va
      (e', ve) <- checkAndEval e (vb `funType` vaη)
      p' <- check p (isEquiv vb vaη ve)
      return (b', e', p')

    vsys' <- evalTC (evalSys eval3) sys'
    () <- either (\_ -> return ()) compatible vsys'

    return $ Ext a' sys'
  P.Lam _ x _ t ->
    isPiOrPath ty >>= \case
      Left (a, b) ->
        BLam x <$> bindFibVar x a (\vx -> check t (b $$ vx))
      Right (a, a₀, a₁) -> do
        let i = x
        (t', vt) <- bindIntVar i (\vi -> checkAndEval t (a $$ vi))
        convTC (TypeErrorEndpoint i I0) a₀ (vt @ (0 `for` i))
        convTC (TypeErrorEndpoint i I1) a₁ (vt @ (1 `for` i))
        return $ BPLam i t' (readBack a₀) (readBack a₁)
  P.Pair _ s t -> do
    (a, b) <- isSigma ty
    (s', vs) <- checkAndEval s a
    Pair s' <$> check t (b $$ vs)
  P.Con ss c as -> do
    isSum ty >>= \case
      Left (d, cs) -> do
        asTys <- hoistEither $ maybe (Left $ TypeErrorMissingCon ss c (readBack d)) Right (c `lookup` cs)
        unless (length as == lengthVTel asTys) $ throwError $ TypeErrorConArgCount ss c (length as) (lengthVTel asTys)
        Con c <$> checkConArgs as asTys
      Right (d, cs) -> do
        asTys <- hoistEither $ maybe (Left $ TypeErrorMissingCon ss c (readBack d)) Right (c `lookup` cs)
        unless (length as == lengthVHTel asTys) $ throwError $ TypeErrorConArgCount ss c (length as) (lengthVHTel asTys)
        uncurry3 (HCon c) <$> checkHConArgs as asTys
  P.Split ss f bs -> do
    (a, b) <- isPi ty
    isSum a >>= \case
      Left (d, cs) -> do -- split on ordinary type
        unless (length cs == length bs && and (zipWith (\b c -> P.branchConstructor b == fst c) bs cs))
          $ throwError $ TypeErrorInvalidSplit ss (readBack d) (map P.branchConstructor bs) (map fst cs)
        Split f <$> zipWithM (checkBranch b) bs (map snd cs)
      Right (d, cs) -> do -- split on higher inductive type
        unless (length cs == length bs && and (zipWith (\b c -> P.branchConstructor b == fst c) bs cs))
          $ throwError $ TypeErrorInvalidSplit ss (readBack d) (map P.branchConstructor bs) (map fst cs)

        vf <- evalTC reAppDef f
        (bs', vbs) <- unzip <$> zipWithM (checkAndEvalHBranch b) bs (map snd cs)

        forM_ (cs `zip` bs `zip` vbs) $ \(((_, tel), P.Branch _ _ ns _), (_, vb)) ->
          bindFibIntVars ns tel $ \xs is sys -> do
            let fv = vb $$ (xs, is)
            mapSysM sys $ \v -> do
              convTC (TypeErrorHSplitCompat (readBack vf)) (re fv) (doHSplit vf b vbs v)

        return $ HSplit f (readBack b) bs'
  P.ExtElm _ s ts -> do
    (a, bs) <- isExt ty
    (s', vs) <- checkAndEval s a

    unless (length ts == length (unVSys bs)) $ fail "Shape of extElem and Ext does not agree! Did the in the type system simplify?"

    ts' <- mapSysM (bs `zipSys` ts) $ \((b, w, _), t) -> do
      (t', vt) <- checkAndEval t b
      let vwt = w `doApp` vt
      convTC TypeErrorExtElmCompat (re vs) vwt
      return (t', vwt)

    compatible $ mapSys ts' snd

    return $ ExtElm s' $ readBackSysCof $ mapSys ts' fst
  t -> do
    (t', ty') <- infer t
    () <- convTC TypeErrorConv ty ty'
    return t'

checkAndEval :: AtStage (PTm -> VTy -> TypeChecker (Tm, Val))
checkAndEval t a = do
  t' <- check t a
  (t',) <$> evalTC eval t'


-- | Tries to infer the type of the given term.
--
-- If the term is neutral, then it should be handled in this case.
infer :: AtStage (PTm -> TypeChecker (Tm, VTy))
infer = atArgPos $ \case
  P.Var _ x ->
    (Var x,) <$> checkFibVar x
  P.App _ s t -> do
    (s', ty) <- infer s
    isPiOrPath ty >>= \case
      Left (a, b) -> do
        (t', vt) <- checkAndEval t a
        return (App s' t', b $$ vt)
      Right (a, a₀, a₁) -> do
        (t', vt) <- checkAndEvalI t
        return (PApp s' (readBack a₀) (readBack a₁) t', a $$ vt)
  P.Pr1 _ t -> do
    (t', tt) <- infer t
    (a, _) <- isSigma tt
    return (Pr1 t', a)
  P.Pr2 _ t -> do
    (t', vt, tt) <- inferAndEval t
    (_, b) <- isSigma tt
    return (Pr2 t', b $$ doPr1 vt)
  P.Coe _ r₀ r₁ i a -> do
    (r'₀, vr₀) <- checkAndEvalI r₀
    (r'₁, vr₁) <- checkAndEvalI r₁
    (a', va) <- bindIntVar i $ \_ -> checkAndEval a VU
    return (BCoe r'₀ r'₁ i a', (va @ (vr₀ `for` i)) `funType` (va @ (vr₁ `for` i)))
  P.HComp _ r₀ r₁ a u₀ tb -> do
    (a', va) <- checkAndEval a VU
    (r'₀, vr₀) <- checkAndEvalI r₀
    r'₁ <- checkI r₁
    (u'₀, vu₀) <- checkAndEval u₀ va

    tb' <- checkSys tb $ \_ (i, u) -> do
      (u', vu) <- bindIntVar i (\_ -> checkAndEval u va)
      () <- convTC (TypeErrorBoundary (IVar i)) (re vu₀) (vu @ (re vr₀ `for` i))
      return (TrIntBinder i u')

    vtb' <- evalTC (evalSys evalTrIntBinder) tb'
    () <- either (\_ -> return ()) compatible vtb'

    return (HComp r'₀ r'₁ a' u'₀ tb', va)
  t -> error $ show t

inferAndEval :: AtStage (PTm -> TypeChecker (Tm, Val, VTy))
inferAndEval t = do
  (t', a) <- infer t
  vt <- evalTC eval t'
  return (t', vt, a)


---- Data types

checkLabel :: AtStage (P.Label -> TypeChecker Label)
checkLabel (P.Label _ c argTel) = Label c <$> checkTel argTel return

checkTel :: AtStage (P.Tel -> AtStage (Tel -> TypeChecker a) -> TypeChecker a)
checkTel []              k = k TelNil
checkTel ((_, x, a):tel) k = do
  (a', va) <- checkAndEval a VU
  bindFibVar x va (\_ -> checkTel tel (k . telCons x a'))

checkConArgs :: AtStage ([PTm] -> VTel -> TypeChecker [Tm])
checkConArgs []     (VTel [] _) = return []
checkConArgs (t:ts) tel         = do
   (t', vt) <- checkAndEval t (headVTel tel)
   (t':) <$> checkConArgs ts (tailVTel tel vt)
checkConArgs _      _           = impossible "checkConArgs: Argument numbers do not match"

checkBranch :: AtStage (Closure -> P.Branch -> VTel -> TypeChecker Branch)
checkBranch b (P.Branch _ c as t) argTys =
  BBranch c as <$> bindFibVars as argTys (\as' -> check t (b $$ VCon c as'))


---- Higher inductive types

checkHLabels :: AtStage (VTy -> [P.HLabel] -> TypeChecker [HLabel])
checkHLabels a = fmap (sortOn hLabelName) . go [] a
  where
    go :: AtStage ([VHLabel] -> VTy -> [P.HLabel] -> TypeChecker [HLabel])
    go _    _ []                              = return []
    go vlbl d ((P.HLabel _ c tel is sys):lbl) = do
      l <- checkTel tel $ \tel' -> bindIntVars is $ \_ -> do
        sys' <- checkSys sys $ \_ t -> check t $ VHSum d vlbl
        vsys <- evalTC (evalSys eval) sys'
        either (\_ -> pure ()) compatible vsys
        return $ HLabel c tel' is sys'
      vl <- evalTC evalHLabel l
      (l:) <$> go (vl:vlbl) d lbl

checkHConArgs :: AtStage ([PTm] -> VHTel -> TypeChecker ([Tm], [I], Sys Tm))
checkHConArgs (t:ts) (VHTelConsFib a tel) = do
  (t', vt) <- checkAndEval t a
  first3 (t':) <$> checkHConArgs ts (tel vt)
checkHConArgs (t:ts) (VHTelConsInt tel)   = do
  (t', vt) <- checkAndEvalI t
  second3 (t':) <$> checkHConArgs ts (tel vt)
checkHConArgs [] (VHTelNil (Right sys)) = return ([], [], readBack sys)
checkHConArgs _  _                      = impossible "checkHConArgs: Argument numbers do not match"

checkAndEvalHBranch :: AtStage (Closure -> P.Branch -> VHTel -> TypeChecker (Branch, VBranch))
checkAndEvalHBranch b (P.Branch _ c as t) tel = do
  b' <- BBranch c as <$> bindFibIntVars as tel (\as' is' sys -> check t (b $$ VHCon c as' is' sys))
  (b',) <$> evalTC evalBranch b'


---- Interval

-- | Checks whether the given term is an interval expression.
checkI :: PTm -> TypeChecker I
checkI = atArgPos $ \case
  P.Var _ x   -> checkIntVar x
  P.Zero _    -> return I0
  P.One _     -> return I1
  P.Inf _ r s -> Inf <$> checkI r <*> checkI s
  P.Sup _ r s -> Sup <$> checkI r <*> checkI s
  _           -> fail "Expected expression of type I!"

checkAndEvalI :: PTm -> TypeChecker (I, VI)
checkAndEvalI r = do
  r' <- checkI r
  asks ((r',) . flip evalI r' . env)


---- Systems

checkSys :: AtStage (P.Sys a -> AtStage (VCof -> a -> TypeChecker b) -> TypeChecker (Sys b))
checkSys (P.Sys _ sys) k =
  fmap Sys $ forM sys $ \(φ, x) -> do
    (φ', vφ) <- checkAndEvalCof φ
    (φ',) <$> extCof vφ (k vφ x)

-- | Checks whether the system agrees on all overlaps.
compatible :: (Restrictable a, Conv (Alt a), ReadBack (Alt a)) => AtStage (VSys a -> TypeChecker ())
compatible sys = do
  let sys' = fromRight (impossible "Given sys was not reduced!") $ simplifySys $ sidePairs sys
  _ <- mapSysM sys' $ uncurry (convTC $ \ss _ _ -> TypeErrorSystemCompat ss)
  return ()


---- Cofibrations

checkAndEvalCof :: [(P.ITm, P.ITm)] -> TypeChecker (Cof, VCof)
checkAndEvalCof eqs = do
  eqs' <- forM eqs $ \(r, s) -> (,) <$> checkAndEvalI r <*> checkAndEvalI s
  let (cof, vcof) = unzip $ map (\((r, vr), (s, vs)) -> ((r, s), (vr, vs))) eqs'
  return (Cof cof, VCof vcof)


--------------------------------------------------------------------------------
---- Checking lists of declarations

checkDecl :: AtStage (P.Decl -> TypeChecker (Name, Tm, Ty, VTy))
checkDecl (P.Decl _ x b t) = do
  traceM $ "\nChecking Definition: " ++ show x

  (t', vt) <- checkAndEval t VU
  b' <- bindFibVar x vt $ \_ -> check b vt -- we treat every definition as recursive

  traceM $ prettyVal vt
  traceM $ pretty b'

  return (x, b', t', vt)

checkDeclsCxt :: [P.Decl] -> Either TypeError Cxt
checkDeclsCxt decls = runTC emptyCxt (go decls)
  where
    go :: AtStage ([P.Decl] -> TypeChecker Cxt)
    go []     = ask
    go (d:ds) = do
      (x, b, t, vt) <- checkDecl d
      local (extDef x b t vt) (go ds)

checkDeclsEnv :: [P.Decl] -> Either TypeError Env
checkDeclsEnv = fmap env . checkDeclsCxt
