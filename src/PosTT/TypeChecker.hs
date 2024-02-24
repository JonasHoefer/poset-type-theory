module PosTT.TypeChecker where

import Control.Monad.Reader

--------------------------------------------------------------------------------
---- Type Checker

data Cxt = Cxt {  }

newtype TypeChecker a = TypeChecker { unTypeChecker :: ReaderT Cxt (Either String) a }

class Check a where


class Infer a where