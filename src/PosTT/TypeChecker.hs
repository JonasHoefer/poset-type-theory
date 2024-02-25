module PosTT.TypeChecker where

import           Control.Monad.Reader
import           Control.Monad.Except

import           PosTT.Common
import           PosTT.Errors
import           PosTT.Eval
import qualified PosTT.Frontend.PreTerms as P
import           PosTT.Frontend.PreTerms (PTm)
import           PosTT.Terms
import           PosTT.Values


--------------------------------------------------------------------------------
---- Type Checking Monad

data Cxt = Cxt { stage :: Stage }

emptyCxt :: Cxt
emptyCxt = Cxt terminalStage

newtype TypeChecker a = TypeChecker { unTypeChecker :: ReaderT Cxt (Either Error) a }
  deriving (Functor, Applicative, Monad, MonadReader Cxt, MonadError Error)

runTypeChecker :: Cxt -> TypeChecker a -> Either Error a
runTypeChecker cxt = flip runReaderT cxt . unTypeChecker




--------------------------------------------------------------------------------
---- Core Bidirectional type checker


inferAndEval :: PTm -> TypeChecker (Tm, Val, VTy)
inferAndEval = error "TODO: inferAndEval"

--------------------------------------------------------------------------------
---- Checking lists of declarations

-- checkDecls :: [P.Decl] -> Either Error (Cxt, Env) !?


checkDecls :: [P.Decl] -> Either Error (Cxt, [(Name, Tm, Ty)])
checkDecls = error "TODO: checkDecls"
