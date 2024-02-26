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
import           PosTT.Terms
import           PosTT.Values hiding (extCof)

import           Debug.Trace


-- TODO: Note the following bug: if we use mapSys or mapSysM etc. then we do not modify the stage *in* the context, only the ambient one!
--       Should there even by a stage in the context? We can pass it around as usual and combine it with the TC code


--------------------------------------------------------------------------------
---- Type Checking Monad

-- | Type checking context
data Cxt = Cxt { stage :: Stage, env :: Env, types :: [(Name, VTy)], intVars :: [Gen], pos :: SrcSpan }

emptyCxt :: Cxt
emptyCxt = Cxt terminalStage EmptyEnv [] [] Nothing

newtype TypeChecker a = TypeChecker { unTypeChecker :: ReaderT Cxt (Either TypeError) a }
  deriving (Functor, Applicative, Monad, MonadReader Cxt, MonadError TypeError)

runTypeChecker :: Cxt -> TypeChecker a -> Either TypeError a
runTypeChecker cxt = flip runReaderT cxt . unTypeChecker

instance MonadFail TypeChecker where
  fail :: String -> TypeChecker a
  fail s = asks pos >>= \ss -> throwError (TypeErrorMsg ss s)


--------------------------------------------------------------------------------
---- Utility Functions

-- TODO: should we extend the stage here? These names to do not appear in *resulting* values.
-- OLD: sExtName x s in extDef and extFib
-- claim: this should be used when we introduce a new *free* variable

-- | Extends context Γ with a definition to a context Γ,(x=t:a)
extDef :: Name -> Tm -> Ty -> VTy -> Cxt -> Cxt
extDef x t a va (Cxt s ρ ts is pos) = Cxt s (EnvDef ρ x t a) ((x, va):ts) is pos

-- | Extends context Γ with a (fibrant) value to a context Γ,(x=v:a)
extFib :: Name -> Val -> VTy -> Cxt -> Cxt
extFib x v a (Cxt s ρ ts is pos) = Cxt s (EnvFib ρ x v) ((x, a):ts) is pos

-- | Extends context Γ with a value of type I to a context Γ,(i=r:I)
extInt :: Gen -> VI -> Cxt -> Cxt
extInt i r (Cxt s ρ ts is pos) = Cxt s (EnvInt ρ i r) ts (i:is) pos

-- | Extends context Γ with a cofibration φ to a context Γ,φ
extCof :: VCof -> Cxt -> Cxt
extCof eqs (Cxt s ρ ts is pos) = Cxt (sExtCof eqs s) ρ ts is pos

-- | Modifies the stage in a context
modStage :: (Stage -> Stage) -> (Cxt -> Cxt)
modStage f cxt = cxt { stage = f (stage cxt) }


---- introduction of free variables

-- | Extends the context Γ with a free variable to a context Γ,(x=x:a)
bindFibVar :: Name -> VTy -> AtStage (Val -> TypeChecker a) -> TypeChecker a
bindFibVar x a k = local (modStage (sExtName x) . extFib x (VVar x) a) (withStageM (k (VVar x)))

bindFibVars :: [Name] -> VTel -> AtStage ([Val] -> TypeChecker a) -> TypeChecker a
bindFibVars []     (VTel [] _) k = withStageM (k [])
bindFibVars (x:xs) tel         k = withStageM (bindFibVar x (headVTel tel) (\v -> bindFibVars xs (tailVTel tel v) (k . (v:))))

-- | Extends the context Γ with a free variable to a context Γ,(i=i:I)
bindIntVar :: Gen -> AtStage (VI -> TypeChecker a) -> TypeChecker a
bindIntVar i k = local (modStage (sExtGen i) . extInt i (iVar i)) (withStageM (k (iVar i)))


---- Evaluation of computations using stage associated to context

withStage :: AtStage a -> TypeChecker a
withStage k = asks ((`bindStage` k) . stage)

withStageM :: AtStage (TypeChecker a) -> TypeChecker a
withStageM k = join $ withStage k


---- lookup types in context

checkIntVar :: Name -> TypeChecker I
checkIntVar (Gen . unName -> i) = asks (elem i . intVars) >>= \case
  True  -> return (IVar i)
  False -> fail $ unGen i ++ " is not an interval variable!"

checkFibVar :: Name -> TypeChecker VTy
checkFibVar x = asks (lookup x . types) >>= \case
  Just t  -> return t
  Nothing -> fail $ unName x ++ " is not a fibrant variable!"


---- Evaluation and Quotation using context

evalTC :: Eval a => a -> TypeChecker (Sem a)
evalTC t = withStageM (asks ((`eval` t) . env))

convTC :: (ReadBack a, Conv a) => (SrcSpan -> Quot a -> Quot a -> ConvError -> TypeError) -> a -> a -> TypeChecker ()
convTC e x y = withStageM $ case x `conv` y of
  Left err -> asks pos >>= \ss -> throwError $ e ss (readBack x) (readBack y) err
  Right () -> return ()

readBackTC :: ReadBack a => a -> TypeChecker (Quot a)
readBackTC x = withStage (readBack x)


---- Source Position handling and errors

at :: SrcSpan -> TypeChecker a -> TypeChecker a
at ss = local (\cxt -> cxt{pos = ss})

atArgPos :: AtStage (PTm -> TypeChecker a) -> (PTm -> TypeChecker a)
atArgPos k t = at (P.srcSpan t) (withStageM (k t))

hoistEither :: Either TypeError a -> TypeChecker a
hoistEither = either throwError pure


--------------------------------------------------------------------------------
---- Matching Types

isU :: VTy -> TypeChecker ()
isU VU = return ()
isU t  = withStageM $ fail $ "Expected U, got " ++ prettyVal t

isExt :: VTy -> TypeChecker (VTy, VSys (VTy, Val, Val))
isExt (VExt a bs) = return (a, bs)
isExt t           = withStageM $ fail $ "Expected Ext-type, got " ++ prettyVal t

isPi :: VTy -> TypeChecker (VTy, Closure)
isPi (VPi a b) = return (a, b)
isPi t         = withStageM $ fail $ "Expected Π-type, got " ++ prettyVal t

isPath :: VTy -> TypeChecker (VTy, Val, Val)
isPath (VPath a a0 a1) = return (a, a0, a1)
isPath t               = withStageM $ fail $ "Expected Path-type, got " ++ prettyVal t

isPiOrPath :: VTy -> TypeChecker (Either (VTy, Closure) (VTy, Val, Val))
isPiOrPath (VPi a b)       = return $ Left (a, b)
isPiOrPath (VPath a a0 a1) = return $ Right (a, a0, a1)
isPiOrPath t               = withStageM $ fail $ "Expected Path-Type or Π-Type, got " ++ prettyVal t

isSigma :: VTy -> TypeChecker (VTy, Closure)
isSigma (VSigma a b) = return (a, b)
isSigma t            = withStageM $ fail $ "Expected Σ-Type, got " ++ prettyVal t

isSum :: VTy -> TypeChecker (Val, [VLabel])
isSum (VSum d lbl) = return (d, lbl)
isSum t            = withStageM $ fail $ "Expected Sum-type, got " ++ prettyVal t


--------------------------------------------------------------------------------
---- Core Bidirectional type checker

-- | Checks whether the given term has the given type.
--
-- If the term is a constructor, then it should be handled in this case.
-- TODO: should types be in this case? We could infer them. See MiniTT vs other CTT impls
check :: PTm -> VTy -> TypeChecker Tm
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
    
    vsys' <- evalTC sys'
    () <- either (\_ -> return ()) compatible vsys'

    return $ Ext a' sys'
  P.Lam _ x _ t ->
    isPiOrPath ty >>= \case
      Left (a, b) ->
        BLam x <$> bindFibVar x a (\vx -> check t (b $$ vx))
      Right (a, a₀, a₁) -> do
        let i = Gen (unName x)
        (t', vt) <- bindIntVar i (\_ -> checkAndEval t a)
        () <- convTC (TypeErrorEndpoint I0) a₀ (vt @ (0 `for` i))
        () <- convTC (TypeErrorEndpoint I1) a₁ (vt @ (1 `for` i))
        BPLam i t' <$> readBackTC a₀ <*> readBackTC a₁
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
--  P.ExtElm _ s ts -> do
--    (a, bs) <- isExt ty
--    (s', vs) <- checkAndEval s a
--
--    unless (length ts == length (unVSys bs)) $ fail "Shape of extElem and Ext does not agree! Did the in the type system simplify?"
--
--    ts' <- mapSysM (bs `zipSys` ts) $ \((b, w, _), t) -> do
--      -- TODO: here stuff goes wrong! The checkAndEval is at the wrong stage w.r.t. the context!
--      (t', vt) <- checkAndEval t b
--      let vwt = w `doApp` vt
--      return _
--
--    return $ ExtElm s' _
  t -> do
    (t', ty') <- infer t
    () <- convTC TypeErrorConv ty ty'
    return t'

checkAndEval :: PTm -> VTy -> TypeChecker (Tm, Val)
checkAndEval t a = do
  t' <- check t a
  (t',) <$> evalTC t'


-- | Tries to infer the type of the given term.
--
-- If the term is neutral, then it should be handled in this case.
infer :: PTm -> TypeChecker (Tm, VTy)
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
        (,a) <$> (PApp s' <$> readBackTC a₀ <*> readBackTC a₁ <*> pure t')
  P.Pr1 _ t -> do
    (t', tt) <- infer t
    (a, _) <- isSigma tt
    return (Pr1 t', a)
  P.Pr2 _ t -> do
    (t', vt, tt) <- inferAndEval t
    (_, b) <- isSigma tt
    return (Pr2 t', b $$ doPr1 vt)
  P.Coe _ r₀ r₁ (Gen . unName -> i) a -> do
    (r'₀, vr₀) <- checkAndEvalI r₀
    (r'₁, vr₁) <- checkAndEvalI r₁
    (a', va) <- bindIntVar i $ \_ -> checkAndEval a VU
    return (BCoe r'₀ r'₁ i a', (va @ (vr₀ `for` i)) `funType` (va @ (vr₁ `for` i)))
  P.HComp ss r₀ r₁ a u₀ tb -> do
    (a', va) <- checkAndEval a VU
    (r'₀, vr₀) <- checkAndEvalI r₀
    r'₁ <- checkI r₁
    (u'₀, vu₀) <- checkAndEval u₀ va
  
    tb' <- checkSys tb $ \φ (Gen . unName -> i, u) -> do
      (u', vu) <- bindIntVar i (\_ -> checkAndEval u va)      
      () <- convTC (TypeErrorBoundary (IVar i)) (re vu₀) (vu @ (re vr₀ `for` i))
      return (TrIntBinder i u')
    
    vtb' <- evalTC tb'
    () <- either (\_ -> return ()) compatible vtb'

    return (HComp r'₀ r'₁ a' u'₀ tb', va)
  t -> error $ show t

inferAndEval :: PTm -> TypeChecker (Tm, Val, VTy)
inferAndEval t = do
  (t', a) <- infer t
  vt <- evalTC t'
  return (t', vt, a)


---- Data types

checkLabel :: P.Label -> TypeChecker Label
checkLabel (P.Label _ c argTel) = Label c <$> checkTel argTel

checkTel :: P.Tel -> TypeChecker Tel
checkTel []              = return TelNil
checkTel ((_, x, a):tel) = do
  (a', va) <- checkAndEval a VU
  telCons x a' <$> bindFibVar x va (\_ -> checkTel tel)

checkArgs :: [PTm] -> VTel -> TypeChecker [Tm]
checkArgs []     (VTel [] _) = return []
checkArgs (t:ts) tel         = do
   (t', vt) <- withStageM (checkAndEval t (headVTel tel))
   tel' <- withStage (tailVTel tel vt)
   (t':) <$> checkArgs ts tel'

checkBranch :: Closure -> P.Branch -> VTel -> TypeChecker Branch
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
  (r',) <$> withStageM (asks ((`eval` r') . env))


---- Systems

checkSys :: P.Sys a -> AtStage (VCof -> a -> TypeChecker b) -> TypeChecker (Sys b)
checkSys (P.Sys _ sys) k =
  fmap Sys $ forM sys $ \(φ, x) -> do
    (φ', vφ) <- checkAndEvalCof φ
    (φ',) <$> local (extCof vφ) (withStageM (k vφ x))

-- | Checks whether the system agrees on all overlaps.
compatible :: (Restrictable a, Conv (Alt a), ReadBack (Alt a)) => VSys a -> TypeChecker ()
compatible sys = withStageM $ do
  let sys'  = fromRight (impossible "Given sys was not reduced!") $ simplifySys $ sidePairs sys
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

-- checkDecls :: [P.Decl] -> Either Error (Cxt, Env) !?

checkDecls' :: [P.Decl] -> Either TypeError (Cxt, Env)
checkDecls' = error "TODO: shouldn't we yield an env?"

checkDecl :: P.Decl -> TypeChecker (Name, Tm, Ty, VTy)
checkDecl (P.Decl _ x b t) = do
  traceM $ "\nChecking Definition: " ++ unName x

  (t', vt) <- checkAndEval t VU
  b' <- bindFibVar x vt $ \_ -> check b vt

  () <- withStageM $ do
    traceM $ prettyVal vt
    traceM $ pretty b'
    return ()

  return (x, b', t', vt)

checkDecls :: [P.Decl] -> Either TypeError (Cxt, [(Name, Tm, Ty)])
checkDecls = runTypeChecker emptyCxt . go
  where
    go :: [P.Decl] -> TypeChecker (Cxt, [(Name, Tm, Ty)])
    go []     = asks (,[])
    go (d:ds) = do
      (x, b', t', vt) <- checkDecl d
      (cxt, ds') <- local (extDef x b' t' vt) (go ds)
      return (cxt, (x, b', t'):ds')
