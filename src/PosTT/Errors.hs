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
deriving instance Show ScopeError

data TypeError where
  TypeErrorMsg :: SrcSpan -> String -> TypeError
  TypeErrorConv :: SrcSpan -> Tm -> Tm -> ConvError -> TypeError
  TypeErrorEndpoint :: Name -> I -> SrcSpan -> Tm -> Tm -> ConvError -> TypeError
  TypeErrorBoundary :: I -> SrcSpan -> Tm -> Tm -> ConvError -> TypeError
  TypeErrorSystemCompat :: SrcSpan -> ConvError -> TypeError
  TypeErrorExtElmCompat :: SrcSpan -> Tm -> Tm -> ConvError -> TypeError
  TypeErrorMissingCon :: SrcSpan -> Name -> Tm -> TypeError
  TypeErrorConArgCount :: SrcSpan -> Name -> Int -> Int -> TypeError
  TypeErrorInvalidSplit :: SrcSpan -> Tm -> [Name] -> [Name] -> TypeError
  TypeErrorHSplitCompat :: Tm -> SrcSpan -> Tm -> Tm -> ConvError -> TypeError
