module PosTT.Pretty where


import           Data.List

import           PosTT.Common
import           PosTT.Errors
import           PosTT.Terms
import           PosTT.Values
import           PosTT.Quotation

import qualified PosTT.Frontend.Exp.Abs as R
import qualified PosTT.Frontend.Exp.Print as R (printTree)


pretty :: Tm -> String
pretty = R.printTree . reflect

prettyConstr :: [(I, I)] -> String
prettyConstr constr = intercalate "," [ "(" ++ prettyI l ++ "=" ++ prettyI r ++ ")" | (l, r) <- constr ]

prettyI :: I -> String
prettyI = R.printTree . reflectFormula

prettyVal :: AtStage (Val -> String)
prettyVal = pretty . readBack

instance Show I where
  show :: I -> String
  show = prettyI

instance Show Cof where
  show :: Cof -> String
  show (Cof eqs) = intercalate "," (map (\(l, r) -> prettyI l ++ "=" ++ prettyI r) eqs)

instance Show Tm where
  show :: Tm -> String
  show = pretty

deriving instance Show ConvError
deriving instance Show TypeError

{-
instance Show TypeError where
  show = \case
    TypeErrorConv ss u v err -> "TYPE ERROR" ++ prettySrcSpan ss ++ ": Could not convert between\n\n" ++ pretty u
                                  ++ "\n\nand\n\n" ++ pretty v ++ "\n\nbecause " ++ show err
    TypeErrorEndpoint n e ss pi ti err -> "TYPE ERROR" ++ prettySrcSpan ss ++ ": Endpoints do not match at " ++ pretty (Var n)
      ++ " = " ++ prettyI e ++ "\n\n" ++ pretty pi ++ "\n\nand\n\n" ++ pretty ti ++ "\n\nbecause " ++ show err

    TypeErrorMsg ss msg -> "TYPE ERROR" ++ prettySrcSpan ss ++ ": " ++ msg
    -- TypeErrorBoundary :: I -> SrcSpan -> Tm -> Tm -> ConvError -> TypeError
    -- TypeErrorSystemCompat :: SrcSpan -> ConvError -> TypeError
    -- TypeErrorExtElmCompat :: SrcSpan -> Tm -> Tm -> ConvError -> TypeError
    -- TypeErrorMissingCon :: SrcSpan -> Name -> Tm -> TypeError
    -- TypeErrorConArgCount :: SrcSpan -> Name -> Int -> Int -> TypeError
    -- TypeErrorInvalidSplit :: SrcSpan -> Tm -> [Name] -> [Name] -> TypeError
    -- TypeErrorHSplitCompat :: Tm -> SrcSpan -> Tm -> Tm -> ConvError -> TypeError
    _ -> error "TODO: pretty print this error"
-}

prettySrcSpan :: SrcSpan -> String
prettySrcSpan (Just ((r1,c1),(r2,c2))) = " (" ++ show r1 ++ ":" ++ show c1 ++ ")-(" ++ show r2 ++ ":" ++ show c2 ++ ")"
prettySrcSpan Nothing                  = ""

--------------------------------------------------------------------------------
---- Reflect Terms back into BNFC expressions to reuse pretty printer

-- | Transforms a core term into a BNFC expression which can be printed.
reflect :: Tm -> R.Exp' ()
reflect = \case
  U                              -> R.U ()
  Var x                          -> R.Var () (reflectName x)
  Let x u t v                    -> R.Let () [R.DeclDef () (reflectName x) [] (reflect t) (R.NoSplit () (R.NoWhere () (reflect u)))] (reflect v)
  Pi a (Binder "_" b)            -> R.Fun () (reflect a) (reflect b)
  Pi a (Binder x b)              -> R.Pi () [R.PTele () (R.Var () (reflectName x)) (reflect a)] (reflect b)
  Lam (Binder x t)               -> R.Lam () [reflectName x] (reflect t)
  App s t                        -> R.App () (reflect s) (reflect t)
  Sigma a (Binder "_" b)         -> R.Prod () (reflect a) (reflect b)
  Sigma a (Binder x b)           -> R.Sigma () [R.PTele () (R.Var () (reflectName x)) (reflect a)] (reflect b)
  Pair s t                       -> R.Pair () (reflect s) [reflect t]
  Pr1 t                          -> R.Fst () (reflect t)
  Pr2 t                          -> R.Snd () (reflect t)
  Path (TrIntBinder "_" a) a₀ a₁ -> R.Path () (reflect a) (reflect a₀) (reflect a₁)
  Path (TrIntBinder x a) a₀ a₁   -> R.PathP () (reflectName x) (reflect a) (reflect a₀) (reflect a₁)
  PLam (IntBinder x t) _ _       -> R.Lam () [reflectGen x] (reflect t)
  PApp t a₀ a₁ r                 -> R.PAppAn () (reflect t) (reflect a₀) (reflect a₁) (reflectFormula r)
  Coe r₀ r₁ (TrIntBinder x a)    -> R.Coe () (reflectFormula r₀) (reflectFormula r₁) (reflectGen x) (reflect a)
  HComp r₀ r₁ a u₀ s             -> R.HComp () (reflectFormula r₀) (reflectFormula r₁) (reflect a) (reflect u₀) (reflectSysBinder s)
  Ext a bs                       -> R.Ext () (reflect a) (reflectSysExt bs)
  ExtElm s (Sys ts)              -> R.ExtElm () (reflect s) [ reflect t | (_, t) <- ts ]
  ExtFun _ t                     -> R.ExtFun () (reflect t)
  Sum _ _                        -> R.Var () (reflectName "[Sum]") -- Should only occur if we print non-normalized term!
  Con c as                       -> foldl1 (R.App ()) (R.Var () (reflectName c) : map reflect as)
  Split _ _                      -> R.Var () (reflectName "[Split]") -- Should only occur if we print non-normalized term!
  HSum _ _                       -> R.Var () (reflectName "[HSum]") -- Should only occur if we print non-normalized term!
  HCon c as is _                 -> foldl1 (R.App ()) (R.Var () (reflectName c) : map reflect as ++ map reflectFormula is)
  HSplit _ _ _                   -> R.Var () (reflectName "[Higher Split]") -- Should only occur if we print non-normalized term!

reflectSysBinder :: Sys (TrIntBinder Tm) -> R.SysBinder' ()
reflectSysBinder (Sys bs) = R.SysBinder () (map reflectSideBinder bs)

reflectSideBinder :: (Cof, TrIntBinder Tm) -> R.SideBinder' ()
reflectSideBinder (Cof c, TrIntBinder x t) = R.SideBinder () (map reflectFace c) (reflectGen x) (reflect t)

reflectSysExt :: Sys (Ty, Tm, Tm) -> R.SysExt' ()
reflectSysExt (Sys bs) = R.SysExt () (map reflectSideExt bs)

reflectSideExt :: (Cof, (Ty, Tm, Tm)) -> R.SideExt' ()
reflectSideExt (Cof c, (b, w, w')) = R.SideExt () (map reflectFace c) (reflect b) (reflect w) (reflect w')

reflectFace :: (I, I) -> R.Face' ()
reflectFace (r, s) = R.Face () (reflectFormula r) (reflectFormula s)

reflectName :: Name -> R.AIdent
reflectName = R.AIdent . (((0, 0), (0, 0)),) . show

reflectGen :: Gen -> R.AIdent
reflectGen = R.AIdent . (((0, 0), (0, 0)),) . show

reflectFormula :: I -> R.Exp' ()
reflectFormula = \case
  IVar i  -> R.Var () $ reflectGen i
  Sup r s -> R.Disj () (reflectFormula r) (reflectFormula s)
  Inf r s -> R.Conj () (reflectFormula r) (reflectFormula s)
  I0      -> R.Dir () (R.Dir0 ())
  I1      -> R.Dir () (R.Dir1 ())
