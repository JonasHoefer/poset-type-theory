module PosTT.Errors where

import PosTT.Common
import PosTT.Terms


data ConvError where
  ConvErrorTm :: Tm -> Tm -> ConvError
  ConvErrorI :: I -> I -> ConvError
  ConvErrorCof :: Cof -> Cof -> ConvError
  ConvErrorString :: String -> ConvError

data ScopeError where
  ReboundError :: String -> ((Int, Int), (Int, Int)) -> ((Int, Int), (Int, Int)) -> ScopeError
  NotBoundError :: String -> ((Int, Int), (Int, Int)) -> ScopeError
  CyclicDependency :: [String] -> ScopeError
  DuplicateLabel :: SrcSpan -> Name -> ScopeError
  IllformedTelescopeBinder :: SrcSpan -> ScopeError
deriving instance Show ScopeError

data TypeError where
  TypeErrorMsg :: SrcSpan -> String -> TypeError
  TypeErrorConv :: SrcSpan -> Tm -> Tm -> ConvError -> TypeError
  TypeErrorEndpoint :: Ty -> Name -> I -> SrcSpan -> Tm -> Tm -> ConvError -> TypeError
  TypeErrorBoundary :: I -> Cof -> SrcSpan -> Tm -> Tm -> ConvError -> TypeError
  TypeErrorSystemCompat :: SrcSpan -> ConvError -> TypeError
  TypeErrorExtElmCompat :: SrcSpan -> Tm -> Tm -> ConvError -> TypeError
  TypeErrorMissingCon :: SrcSpan -> Name -> Tm -> TypeError
  TypeErrorConArgCount :: SrcSpan -> Name -> Int -> Int -> TypeError
  TypeErrorInvalidSplit :: SrcSpan -> Tm -> [Name] -> [Name] -> TypeError
  TypeErrorHSplitCompat :: Tm -> SrcSpan -> Tm -> Tm -> ConvError -> TypeError
  TypeErrorCollection :: [TypeError] -> TypeError

instance Semigroup TypeError where
  TypeErrorCollection es <> TypeErrorCollection es' = TypeErrorCollection (es ++ es')
  TypeErrorCollection es <> e                       = TypeErrorCollection (es ++ [e])
  e                      <> TypeErrorCollection es' = TypeErrorCollection (e  :  es')
  e                      <> e'                      = TypeErrorCollection [e, e']

instance Monoid TypeError where
  mempty = TypeErrorCollection []
  
