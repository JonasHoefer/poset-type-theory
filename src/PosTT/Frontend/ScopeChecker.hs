-- | Checks that all used variables are bound, no binder shadows, and converts from raw to presyntax
module PosTT.Frontend.ScopeChecker (Module, ScopingEnv, parsePTm, parseModule, moduleName, checkModule, checkModules, moduleImports, printTree) where

import           Prelude hiding (id)

import           Control.Monad.Except
import           Control.Monad.Reader

import           Data.Bifunctor (bimap)
import           Data.Either.Extra (mapLeft)
import           Data.Function (on)
import           Data.Functor.Adjunction (uncozipL)
import           Data.List (isPrefixOf, sort, sortBy, sortOn, group)
import           Data.String (IsString(..))
import           Data.Tuple.Extra (uncurry3)
import qualified Data.Graph as G

import           PosTT.Frontend.Exp.Abs
import           PosTT.Frontend.Exp.Lex (tokens)
import           PosTT.Frontend.Exp.Layout (resolveLayout)
import           PosTT.Frontend.Exp.Par (pModule, pExp)
import           PosTT.Frontend.Exp.Print (printTree)

import           PosTT.Common
import           PosTT.Errors
import           PosTT.Frontend.PreTerms (PTm, PTy)
import qualified PosTT.Frontend.PreTerms as P


-- TODO: The src spans are handled in a bit of and ad-hoc way.
--       There are probably situations where they could be translated
--       "nicer" to presyntax.

--------------------------------------------------------------------------------
---- Exposed BNFC Functions and Utilities

-- | Tries to parse a preterm, using names from the given environment,
--   from the given string.
parsePTm :: ScopingEnv -> String -> Either String PTm
parsePTm env s = pExp (tokens s) >>= mapLeft show . flip runReaderT env . checkExp

parseModule :: String -> Either String Module
parseModule = pModule . resolveLayout True . tokens

moduleName :: Module -> String
moduleName (Module _ (AIdent (_, name)) _ _) = name

moduleDecls :: Module -> [Decl]
moduleDecls (Module _ _ _ decls) = decls

moduleImports :: Module -> [String]
moduleImports (Module _ _ imps _) = [ name | Import _ (AIdent (_, name)) <- imps ]


--------------------------------------------------------------------------------
---- Scope Checker

data SymKind = Variable | Constructor deriving Eq -- | HigherConstructor

type ScopingEnv = [(Name, (((Int, Int), (Int, Int)), SymKind))]

type ScopeChecker a = ReaderT ScopingEnv (Either ScopeError) a

runScopeChecker :: ScopeChecker a -> Either ScopeError a
runScopeChecker ss = runReaderT ss []

checkLams :: SrcSpan -> [AIdent] -> Exp -> ScopeChecker PTm
checkLams ss (id:ids) u = bindAIdent id $ \id' -> P.Lam ss id' Nothing <$> checkLams ss ids u
checkLams _  []       u = checkExp u

checkALams :: [(SrcSpan, Name, PTm)] -> Exp -> ScopeChecker PTm
checkALams ((ss,id,t):ids) u = P.Lam ss id (Just t) <$> checkALams ids u
checkALams []              u = checkExp u

-- TODO: PTele(s) cases are missing some check (or should not be CPSed)
-- I think Sigmas and Pis need to use bindAIdent as-well.
checkPTele :: PTele -> ([(SrcSpan, Name, PTy)] -> ScopeChecker a) -> ScopeChecker a
checkPTele (PTele ss ids ty) = checkTele (Tele ss id' ids' ty)
  where
    (id':ids') = unHackIds ids

    unHackIds (App _ (Var _ id) e) = id : unHackIds e
    unHackIds (Var _ id)           = [id]

checkPTeles :: [PTele] -> ([(SrcSpan, Name, PTy)] -> ScopeChecker a) -> ScopeChecker a
checkPTeles []     k = k []
checkPTeles (t:ts) k = checkPTele t $ \t' -> checkPTeles ts $ \ts' -> k (t' ++ ts')

checkPis :: [PTele] -> Exp -> ScopeChecker PTm
checkPis pts u = checkPTeles pts $ \ts -> flip (foldr (uncurry3 P.Pi)) ts <$> checkExp u

checkSigmas :: [PTele] -> Exp -> ScopeChecker PTm
checkSigmas pts u = checkPTeles pts $ \ts -> flip (foldr (uncurry3 P.Sigma)) ts <$> checkExp u

checkLets :: [Decl] -> Exp -> ScopeChecker PTm
checkLets []     u = checkExp u
checkLets (d:ds) u = bindDecl d $ \case
  P.Decl ss id v ty -> P.Let ss id v ty <$> checkLets ds u

checkSys :: Sys -> ScopeChecker (P.Sys PTm)
checkSys (Sys ss sys) = P.Sys ss <$> traverse checkSide sys

checkSide :: Side -> ScopeChecker ([(P.ITm, P.ITm)], PTm)
checkSide (Side _ fs e) = (,) <$> traverse checkFace fs <*> checkExp e

checkSysExt :: SysExt -> ScopeChecker (P.Sys (PTy, PTm, PTm))
checkSysExt (SysExt ss sys) = P.Sys ss <$> traverse checkSideExt sys

checkSideExt :: SideExt -> ScopeChecker ([(P.ITm, P.ITm)], (PTy, PTm, PTm))
checkSideExt (SideExt _ fs b w w') = (,) <$> traverse checkFace fs <*> ((,,) <$> checkExp b <*> checkExp w <*> checkExp w')

checkSysBinder :: SysBinder -> ScopeChecker (P.Sys (Name, PTm))
checkSysBinder (SysBinder ss sys) = P.Sys ss <$> traverse checkSideBinder sys

checkSideBinder :: SideBinder -> ScopeChecker ([(P.ITm, P.ITm)], (Name, PTm))
checkSideBinder (SideBinder _ fs i u) = (uncurry . (\x y z -> (x, (y, z))) <$> traverse checkFace fs) <*> bindAIdent i (\i' -> (i',) <$> checkExp u)

checkFace :: Face -> ScopeChecker (P.ITm, P.ITm)
checkFace (Face _ r s) = (,) <$> checkExp r <*> checkExp s

checkExp :: Exp -> ScopeChecker PTm
checkExp (Var ss id)           = checkVar id
checkExp (U ss)                = return $ P.U ss
checkExp (Let _ ds u)          = checkLets ds u
checkExp (Lam ss ids u)        = checkLams ss ids u
checkExp (ALam _ pts u)        = checkPTeles pts (`checkALams` u)
checkExp (Fun ss a b)          = P.Pi ss "_" <$> checkExp a <*> checkExp b
checkExp (Pi _ pts u)          = checkPis pts u
checkExp (Prod ss a b)         = P.Sigma ss "_" <$> checkExp a <*> checkExp b
checkExp (Sigma _ pts u)       = checkSigmas pts u
checkExp (Conj ss r s)         = P.Inf ss <$> checkExp r <*> checkExp s
checkExp (Disj ss r s)         = P.Sup ss <$> checkExp r <*> checkExp s
checkExp (App ss u v)          = P.app ss <$> checkExp u <*> checkExp v -- applies to constructors
checkExp (Path ss a u v)       = P.PathP ss "_" <$> checkExp a <*> checkExp u <*> checkExp v
checkExp (PathP ss i a u v)    = bindAIdent i (\i' -> P.PathP ss i' <$> checkExp a) <*> checkExp u <*> checkExp v
checkExp (Coe ss r s id a)     = uncurry <$> (P.Coe ss <$> checkExp r <*> checkExp s) <*> bindAIdent id (\id' -> (id',) <$> checkExp a)
checkExp (HComp ss r s a a0 α) = P.HComp ss <$> checkExp r <*> checkExp s <*> checkExp a <*> checkExp a0 <*> checkSysBinder α
checkExp (Fst ss u)            = P.Pr1 ss <$> checkExp u
checkExp (Snd ss u)            = P.Pr2 ss <$> checkExp u
checkExp (Pair ss u v)         = foldr1 (P.Pair ss) <$> mapM checkExp (u:v)
checkExp (ExtFun ss u)         = P.ExtFun ss <$> checkExp u
checkExp (ExtElm ss u vs)      = P.ExtElm ss <$> checkExp u <*> traverse checkExp vs
checkExp (Ext ss a bs)         = P.Ext ss <$> checkExp a <*> checkSysExt bs
checkExp (I ss)                = return $ P.I ss
checkExp (Dir _ (Dir0 ss))     = return $ P.Zero ss
checkExp (Dir _ (Dir1 ss))     = return $ P.One ss
checkExp e                     = error $ "[ScopeChecker] Missing Case: " ++ printTree e

checkVar :: AIdent -> ScopeChecker PTm
checkVar (AIdent (ss, id)) = asks (\ids -> guard (not $ "_" `isPrefixOf` id) *> fromString id `lookup` ids) >>= \case
  Nothing                     -> throwError $ NotBoundError id ss
  Just (_, Variable)          -> return $ P.Var (Just ss) (fromString id)
  Just (_, Constructor)       -> return $ P.Con (Just ss) (fromString id) []
--  Just (_, HigherConstructor) -> return $ P.HCon (Just ss) (fromString id) []

checkCon :: AIdent -> ScopeChecker Name
checkCon (AIdent (ss, id)) = asks (fromString id `lookup`) >>= \case
  Just (_, Constructor) -> return $ fromString id
  _                     -> throwError $ NotBoundError id ss

checkFreshAIdent :: AIdent -> ScopeChecker (Name, ((Int, Int), (Int, Int)))
checkFreshAIdent (AIdent (ss, "_")) = return ("_", ss)
checkFreshAIdent (AIdent (ss, id))  = asks (lookup (fromString id)) >>= \case
  Nothing                 -> return (fromString id, ss)
  Just (_  , Constructor) -> return (fromString id, ss)
  Just (ss', Variable)    -> throwError $ ReboundError id ss' ss

bindAIdent' :: AIdent -> (Name -> ((Int, Int), (Int, Int)) -> ScopeChecker a) -> ScopeChecker a
bindAIdent' id k = checkFreshAIdent id >>= \(id', ss) -> local ((id', (ss, Variable)):) (k id' ss)

bindHCon :: AIdent -> (Name -> ((Int, Int), (Int, Int)) -> ScopeChecker a) -> ScopeChecker a
bindHCon id k = checkFreshAIdent id >>= \(id', ss) -> local ((id', (ss, Constructor)):) (k id' ss)

bindAIdent :: AIdent -> (Name -> ScopeChecker a) -> ScopeChecker a
bindAIdent id k = bindAIdent' id (\id' _ -> k id')

bindAIdents :: [AIdent] -> ([Name] -> ScopeChecker a) -> ScopeChecker a
bindAIdents []       k = k []
bindAIdents (id:ids) k = bindAIdent id $ \id' -> bindAIdents ids $ \ids' -> k (id':ids')

checkTele :: Tele -> ([(SrcSpan, Name, PTy)] -> ScopeChecker a) -> ScopeChecker a
checkTele (Tele ss id ids ty) k = do
  ty' <- checkExp ty
  bindAIdents (id:ids) $ \ids' -> k ((ss,,ty') <$> ids')

checkTeles :: [Tele] -> ([(SrcSpan, Name, PTy)] -> ScopeChecker a) -> ScopeChecker a
checkTeles []     k = k []
checkTeles (t:ts) k = checkTele t $ \t' -> checkTeles ts $ \ts' -> k (t' ++ ts')

checkWhereExp :: ExpWhere -> ScopeChecker PTm
checkWhereExp (NoWhere _ e)   = checkExp e
checkWhereExp (Where ss e ds) = checkExp $ Let ss ds e

checkBody :: Name -> Body -> ScopeChecker PTm
checkBody _ (NoSplit _ bd) = checkWhereExp bd
checkBody f (Split ss bs)  = do
  bs' <- mapM checkBranch bs
  let cNms = map P.branchConstructor bs'
  forM_ (filter ((> 1) . length) $ group $ sort cNms) $ throwError . DuplicateLabel ss . head
  return $ P.Split ss f $ sortBy (compare `on` P.branchConstructor) bs'

checkBranch :: Branch -> ScopeChecker P.Branch
checkBranch (OBranch ss c as t) = do
  c' <- checkCon c
  bindAIdents as $ \as' -> P.Branch ss c' as' <$> checkWhereExp t
checkBranch (PBranch{}) = error "No HITs yet (branch)"


unLabel :: Label -> Either (SrcSpan, AIdent, [Tele], [AIdent], Sys) (SrcSpan, AIdent, [Tele])
unLabel = \case
  OLabel ssLbl idC args        -> Right (ssLbl, idC, args)
  PLabel ssLbl idC args is sys -> Left  (ssLbl, idC, args, is, sys)

uniformLabel :: [Label] -> Either [(SrcSpan, AIdent, [Tele], [AIdent], Sys)] [(SrcSpan, AIdent, [Tele])]
uniformLabel = unifyEither (\(ssLbl, idC, argsC) -> (ssLbl, idC, argsC, [], Sys ssLbl [])) . map unLabel


checkDeclHIT :: [(SrcSpan, AIdent, [Tele], [AIdent], Sys)] -> ScopeChecker [((Name, ((Int, Int),(Int, Int))), P.HLabel)]
checkDeclHIT []                               = return []
checkDeclHIT ((ssLbl, idC, args, is, sys):cs) = do
  (args', is', sys') <- checkTeles args $ \args' -> bindAIdents is $ \is' -> (args', is',) <$> checkSys sys
  bindHCon idC $ \idC' ss -> (((idC', ss), P.HLabel ssLbl idC' args' is' sys'):) <$> checkDeclHIT cs

checkDeclSum :: [(SrcSpan, AIdent, [Tele])] -> ScopeChecker [((Name, ((Int, Int),(Int, Int))), P.Label)]
checkDeclSum = mapM $ \(ssLbl, idC@(AIdent (ssIdC, idCStr)), argsC) -> do
  label <- P.Label ssLbl <$> fmap fst (checkFreshAIdent idC) <*> checkTeles argsC return
  return ((fromString idCStr, ssIdC), label)

-- | Checks function and data definitions.
--
-- Returns the desuggared declaration, as well as, the new names that may be used by subsequent definitions.
checkDecl :: Decl -> ScopeChecker (ScopingEnv, P.Decl)
checkDecl (DeclDef ss id ts ty bd) = do
  checkTeles ts $ \ts' -> do
    bindAIdent' id $ \id' idss -> do
      let ty' = flip (foldr (\(ss', x, t) -> P.Pi ss' x t)) ts' <$> checkExp ty
          -- We could type annotate here, but then we would check the same type twice.
      let bd' = flip (foldr (\(ss', x, _) -> P.Lam ss' x Nothing)) ts' <$> checkBody id' bd
      ([(id', (idss, Variable))],) <$> (P.Decl ss id' <$> bd' <*> ty')
checkDecl (DeclData ss id ts cs) = do
  checkTeles ts $ \ts' ->
    bindAIdent' id $ \id' idss -> do
      (cs', d) <- either (fmap $ P.HSum ss id') (fmap $ P.Sum ss id' . sortOn P.labelName) . bimap unzip unzip
        <$> uncozipL (bimap checkDeclHIT checkDeclSum (uniformLabel cs))

      forM_ (filter ((> 1) . length) $ group $ sort $ map fst cs') $ throwError . DuplicateLabel ss . head

      let ty = foldr (\(ss', x, t) -> P.Pi ss' x t) (P.U ss) ts' -- a data declaration always yields a value in U
      let bd = foldr (\(ss', x, _) -> P.Lam ss' x Nothing) d ts'

      return ((id', (idss, Variable)):[ (c, (ssC, Constructor)) | (c, ssC) <- cs' ], P.Decl ss id' bd ty)

bindDecl :: Decl -> (P.Decl -> ScopeChecker a) -> ScopeChecker a
bindDecl d k = checkDecl d >>= \(ids, d') -> local (ids ++) (k d')

checkDecls :: [Decl] -> ScopeChecker (ScopingEnv, [P.Decl])
checkDecls []     = asks (,[])
checkDecls (d:ds) = bindDecl d (\d' -> fmap (d':) <$> checkDecls ds)

checkModule' :: Module -> ScopeChecker (ScopingEnv, [P.Decl])
checkModule' (Module _ _ _ ds) = checkDecls ds

checkModule :: Module -> Either ScopeError (ScopingEnv, [P.Decl])
checkModule = runScopeChecker . checkModule'

checkModules :: [Module] -> Either ScopeError (ScopingEnv, [P.Decl])
checkModules = runScopeChecker . (orderModules >=> checkDecls . concatMap moduleDecls)

orderModules :: [Module] -> ScopeChecker [Module]
orderModules ms = traverse unAcyclicComponent $ G.stronglyConnComp moduleGraph
  where
    moduleGraph :: [(Module, String, [String])]
    moduleGraph = [ (m, moduleName m, moduleImports m) | m <- ms ]

    unAcyclicComponent :: G.SCC Module -> ScopeChecker Module
    unAcyclicComponent (G.AcyclicSCC a) = return a
    unAcyclicComponent (G.CyclicSCC ms) = throwError $ CyclicDependency $ moduleName <$> ms
