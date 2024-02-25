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
