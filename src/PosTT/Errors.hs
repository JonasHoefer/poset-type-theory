module PosTT.Errors where

import PosTT.Common
import PosTT.Terms

data ConvError = ConvErrorTm Tm Tm | ConvErrorString String

data ScopeError where
  ReboundError :: String -> ((Int, Int), (Int, Int)) -> ((Int, Int), (Int, Int)) -> ScopeError
  NotBoundError :: String -> ((Int, Int), (Int, Int)) -> ScopeError
  CyclicDependency :: [String] -> ScopeError
  DuplicateLabel :: SrcSpan -> Name -> ScopeError
deriving instance Show ScopeError
