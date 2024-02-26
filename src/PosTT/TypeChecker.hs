module PosTT.TypeChecker where

import           Control.Monad.Reader
import           Control.Monad.Except

import           Data.Either (fromRight)

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

-- | Extends context Γ with a (fibrant) value to a context Γ,(x=v:a)checkSys
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
bindFibVars []     (VTel [] _) k = k []
bindFibVars (x:xs) tel         k = 
  bindFibVar x (headVTel tel) (\v -> bindFibVars xs (tailVTel tel v) (\vs -> k (v:vs)))

-- | Extends the context Γ with a free variable to a context Γ,(i=i:I)
bindIntVar :: AtStage (Gen -> AtStage (VI -> TypeChecker a) -> TypeChecker a)
bindIntVar i k = extGen i (local (extInt i (iVar i)) (k (iVar i)))


---- lookup types in context

checkIntVar :: Name -> TypeChecker I
checkIntVar (Gen -> i) = asks (elem i . intVars) >>= \case
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
at ss ma = local (\cxt -> cxt{pos = ss}) ma

atArgPos :: (PTm -> TypeChecker a) -> (PTm -> TypeChecker a)
atArgPos k t = at (P.srcSpan t) (k t)

hoistEither :: Either TypeError a -> TypeChecker a
hoistEither e = either throwError pure e


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

isPath :: AtStage (VTy -> TypeChecker (VTy, Val, Val))
isPath (VPath a a0 a1) = return (a, a0, a1)
isPath t               = fail $ "Expected Path-type, got " ++ prettyVal t

isPiOrPath :: AtStage (VTy -> TypeChecker (Either (VTy, Closure) (VTy, Val, Val)))
isPiOrPath (VPi a b)       = return $ Left (a, b)
isPiOrPath (VPath a a0 a1) = return $ Right (a, a0, a1)
isPiOrPath t               = fail $ "Expected Path-Type or Π-Type, got " ++ prettyVal t

isSigma :: AtStage (VTy -> TypeChecker (VTy, Closure))
isSigma (VSigma a b) = return (a, b)
isSigma t            = fail $ "Expected Σ-Type, got " ++ prettyVal t

isSum :: AtStage (VTy -> TypeChecker (Val, [VLabel]))
isSum (VSum d lbl) = return (d, lbl)
isSum t            = fail $ "Expected Sum-type, got " ++ prettyVal t


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
  P.Path _ a a₀ a₁ -> do
    () <- isU ty
    (a', va) <- checkAndEval a VU
    Path a' <$> check a₀ va <*> check a₁ va
  P.Sum _ d cs -> do
    () <- isU ty
    Sum d <$> forM cs checkLabel
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
        let i = Gen x
        (t', vt) <- bindIntVar i (\_ -> checkAndEval t a)
        convTC (TypeErrorEndpoint I0) a₀ (vt @ (0 `for` i))
        convTC (TypeErrorEndpoint I1) a₁ (vt @ (1 `for` i))
        return $ BPLam i t' (readBack a₀) (readBack a₁)
  P.Pair _ s t -> do
    (a, b) <- isSigma ty
    (s', vs) <- checkAndEval s a
    Pair s' <$> check t (b $$ vs)
  P.Con ss c as -> do
    (d, cs) <- isSum ty
    asTys <- hoistEither $ maybe (Left $ TypeErrorMissingCon ss c (readBack d)) Right (c `lookup` cs)
    Con c <$> checkArgs as asTys
  P.Split ss f bs -> do
    (a, b) <- isPi ty
    (d, cs) <- isSum a

    unless (length cs == length bs && and (zipWith (\b c -> P.branchConstructor b == fst c) bs cs))
      $ throwError $ TypeErrorInvalidSplit ss (readBack d) (map P.branchConstructor bs) (map fst cs)

    Split f <$> zipWithM (checkBranch b) bs (map snd cs)
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
        t' <- checkI t
        return (PApp s' (readBack a₀) (readBack a₁) t' ,a)
  P.Pr1 _ t -> do
    (t', tt) <- infer t
    (a, _) <- isSigma tt
    return (Pr1 t', a)
  P.Pr2 _ t -> do
    (t', vt, tt) <- inferAndEval t
    (_, b) <- isSigma tt
    return (Pr2 t', b $$ doPr1 vt)
  P.Coe _ r₀ r₁ (Gen -> i) a -> do
    (r'₀, vr₀) <- checkAndEvalI r₀
    (r'₁, vr₁) <- checkAndEvalI r₁
    (a', va) <- bindIntVar i $ \_ -> checkAndEval a VU
    return (BCoe r'₀ r'₁ i a', (va @ (vr₀ `for` i)) `funType` (va @ (vr₁ `for` i)))
  P.HComp _ r₀ r₁ a u₀ tb -> do
    (a', va) <- checkAndEval a VU
    (r'₀, vr₀) <- checkAndEvalI r₀
    r'₁ <- checkI r₁
    (u'₀, vu₀) <- checkAndEval u₀ va
  
    tb' <- checkSys tb $ \_ (Gen -> i, u) -> do
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
checkLabel (P.Label _ c argTel) = Label c <$> checkTel argTel

checkTel :: AtStage (P.Tel -> TypeChecker Tel)
checkTel []              = return TelNil
checkTel ((_, x, a):tel) = do
  (a', va) <- checkAndEval a VU
  telCons x a' <$> bindFibVar x va (\_ -> checkTel tel)

checkArgs :: AtStage ([PTm] -> VTel -> TypeChecker [Tm])
checkArgs []     (VTel [] _) = return []
checkArgs (t:ts) tel         = do
   (t', vt) <- checkAndEval t (headVTel tel)
   (t':) <$> checkArgs ts (tailVTel tel vt)

checkBranch :: AtStage (Closure -> P.Branch -> VTel -> TypeChecker Branch)
checkBranch b (P.Branch ss c as t) argTys =
  BBranch c as <$> bindFibVars as argTys (\as' -> check t (b $$ VCon c as'))


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
  (r',) <$> asks (flip evalI r' . env) 


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

-- checkDecls' :: [P.Decl] -> Either TypeError (Cxt, Env)
-- checkDecls' = error "TODO: shouldn't we yield an env?"

checkDecl :: AtStage (P.Decl -> TypeChecker (Name, Tm, Ty, VTy))
checkDecl (P.Decl _ x b t) = do
  traceM $ "\nChecking Definition: " ++ show x

  (t', vt) <- checkAndEval t VU
  b' <- bindFibVar x vt $ \_ -> check b vt

  traceM $ prettyVal vt
  traceM $ pretty b'

  return (x, b', t', vt)

checkDecls :: [P.Decl] -> Either TypeError (Cxt, [(Name, Tm, Ty)])
checkDecls decls = runTC emptyCxt (go decls)
  where
    go :: AtStage ([P.Decl] -> TypeChecker (Cxt, [(Name, Tm, Ty)]))
    go []     = asks (,[])
    go (d:ds) = do
      (x, b', t', vt) <- checkDecl d
      (cxt, ds') <- local (extDef x b' t' vt) (go ds)
      return (cxt, (x, b', t'):ds')
