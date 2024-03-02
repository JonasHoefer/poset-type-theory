module Main where

import           Data.List (find, intercalate)
import qualified Data.Map as M
import           Data.String (IsString(..))
import           Data.Tuple.Extra (fst3, snd3)

import           Control.Monad.State.Strict

import           System.Console.Haskeline
import           System.Directory
import           System.Exit
import           System.FilePath

import           Options.Applicative as O

import           PosTT.Common
import           PosTT.Terms
import           PosTT.Values
import           PosTT.HeadLinearReduction
import           PosTT.Pretty
import           PosTT.Quotation
import           PosTT.Frontend.ScopeChecker
import           PosTT.TypeChecker


--------------------------------------------------------------------------------
---- Command Line Options

data EvalMode = Default | HeadLinear deriving (Show, Read, Eq)

data Options = Repl (Maybe FilePath) | Eval EvalMode FilePath deriving Show

evalModeParser :: Parser EvalMode
evalModeParser = option auto (short 'm' <> metavar "Default|HeadLinear" <> showDefault <> value Default)

replOptions :: Parser Options
replOptions = Repl <$> optional (argument str (metavar "FILE"))

evalOptions :: Parser Options
evalOptions = Eval <$> evalModeParser <*> argument str (metavar "FILE")

optionsParser :: Parser Options
optionsParser = subparser (command "repl" (info replOptions (progDesc "Read-Eval-Print-Loop"))
                            <> command "eval" (info evalOptions (progDesc "Evaluate file")))

options :: ParserInfo Options
options = info (optionsParser <**> helper)
  (fullDesc <> header "PosTT - A minimal implementation of a variant of CTT")


--------------------------------------------------------------------------------
---- Eval

evalModule :: EvalMode -> FilePath -> IO ()
evalModule m p = do
  rawTm <- recursiveLoad p
  preTm <- either (error . show) (return . snd) (checkModules rawTm)
  rho   <- either (error . show) return (checkDeclsEnv preTm)

  putStrLn $ "\nSuccessfully checked " ++ show (length rho) ++ " definitions"

  case m of
    Default | EnvCons _ x (EntryDef s _) <- rho -> do
      putStrLn $ "Evaluation of " ++ pretty s
      putStrLn $ "Yields " ++ pretty (normalize rho $ Var x)
    HeadLinear -> do
      error "FOO"
      -- let defs = map (\(x, t, _) -> (x, t)) tms
      -- let (u, s, t) = headUnfoldAll mempty defs (Var $ fst3 $ last tms)

      -- putStrLn $ "Head linear unfolding of " ++ pretty (snd3 $ last tms)
      -- putStrLn $ "Yields " ++ pretty t
      -- putStrLn ""
      -- putStrLn $ "Unfold counts: " ++ intercalate ", " [ show d ++ ": " ++ show c | (d, c) <- M.toList u]
      -- putStrLn $ "Hence " ++ show s ++ " unfold steps"


--------------------------------------------------------------------------------
---- Repl

data ReplCmd = Term String | Load FilePath | Reload | Quit | Unfold Int String deriving (Show, Read, Eq)

loadCmd :: Mod CommandFields ReplCmd
loadCmd = command ":load" (info (Load <$> argument str (metavar "FILE")) (progDesc "Load file"))

reloadCmd :: Mod CommandFields ReplCmd
reloadCmd = command ":reload" (info (pure Reload) (progDesc "Reload current module"))

quitCmd :: Mod CommandFields ReplCmd
quitCmd = command ":quit" (info (pure Quit) (progDesc "Quit repl"))

unfoldCmd :: Mod CommandFields ReplCmd
unfoldCmd = command ":unfold" $ info
  (Unfold <$> option auto (short 's' <> metavar "STEPS" <> showDefault <> value 1)
          <*> argument str (metavar "DEF"))
  (progDesc "Perform head linear unfold on given definition")

replCmds :: ParserInfo ReplCmd
replCmds = info (subparser (quitCmd <> loadCmd <> reloadCmd <> unfoldCmd)) mempty

parseReplCmd :: String -> Either String ReplCmd
parseReplCmd ""          = Left ""
parseReplCmd cmd@(':':_) = case execParserPure (prefs showHelpOnError) replCmds (words cmd) of
  Success replCmd           -> Right replCmd
  Failure (ParserFailure f) -> Left $ show $ (fst3 (f "")) { helpUsage = mempty }
  CompletionInvoked{}       -> error "Completion triggered, this should be impossible"
parseReplCmd t = Right (Term t)

instance MonadState s m => MonadState s (InputT m) where
  get :: MonadState s m => InputT m s
  get = lift get

  put :: MonadState s m => s -> InputT m ()
  put = lift . put

data ReplState = ReplState
  { currentModule :: !String
  , currentFile :: !(Maybe FilePath)
  , scopeCheckerEnv :: !ScopingEnv
  , context :: !Cxt
  }

environment :: ReplState -> Env
environment = env . context

type Repl a = InputT (StateT ReplState IO) a

runRepl :: Repl a -> IO a
runRepl = flip evalStateT initialReplState . runInputT (defaultSettings { historyFile = Just ".postt_history" })

initialReplState :: ReplState
initialReplState = ReplState "" Nothing mempty emptyCxt

repl :: Repl ()
repl = do
  input <- getInputLine . (++ "> ") =<< gets currentModule
  case input of
    Nothing -> return ()
    Just l  -> do
      case parseReplCmd l of
        Left err       -> do
          unless (null err) (outputStrLn err)
          repl
        Right Quit     -> return ()
        Right (Load p) -> do
          replLoad p
          repl
        Right Reload -> do
          gets currentFile >>= \case
            Just p  -> replLoad p
            Nothing -> outputStrLn "No module loaded!"
          repl
        Right (Term t) -> do
          scpEnv <- gets scopeCheckerEnv
          case parsePTm scpEnv t of
            Left err -> outputStrLn err
            Right pt -> do
              cxt <- gets context
              case runTC cxt (inferAndEval pt) of -- TODO: recheck stages
                Left err          -> outputStrLn $ show err
                Right (_, val, _) -> outputStrLn $ bindStage terminalStage prettyVal val
          repl
        Right (Unfold k d) -> do
          gets (lookup (fromString d) . environment) >>= \case
            Nothing        -> do
              outputStrLn $ d ++ " is not defined!"
            Just (EntryDef t _) -> do
              ρ <- gets environment
              let (u, t') = headUnfold ρ t (Just k)
              modify $ \s -> s{ context = (context s) { env = modifyAt (fromString d) (\(EntryDef _ ty) -> EntryDef t' ty) (env (context s)) } }
              outputStrLn $ pretty t'
              outputStrLn ""
              outputStrLn $ "Unfold counts: " ++ intercalate ", " [ show x ++ ": " ++ show c | (x, c) <- M.toList u]
          repl

replLoad :: FilePath -> Repl ()
replLoad p = do
  ms <- liftIO $ recursiveLoad p
  (scpEnv, ds) <- either (error . show) return $ checkModules ms
  cxt <- either (error . show) return $ checkDeclsCxt ds
  let rho = env cxt
  put $ ReplState (moduleName $ head ms) (Just p) scpEnv cxt
  outputStrLn $ "Successfully checked " ++ show (length rho) ++ " definitions"


--------------------------------------------------------------------------------
---- File Loading

moduleRoot :: Module -> FilePath -> Either String FilePath
moduleRoot m p | takeFileName p /= moduleName m ++ ".ctt" =
  Left $ "File name " ++ takeFileName p ++ " does not match expected file name " ++ moduleName m ++ ".ctt"
moduleRoot _ p = Right $ dropFileName p

recursiveLoad :: FilePath -> IO [Module]
recursiveLoad rp = makeAbsolute rp >>= go [] . pure
  where
    go :: [FilePath] -> [FilePath] -> IO [Module]
    go _    []     = return []
    go done (p:ps) | p `elem` done = go done ps
    go done (p:ps) = do
      m <- either (\msg -> putStrLn (msg ++ " in " ++ p) >> exitFailure) return . parseModule =<< readFile p
      d <- either error return $ moduleRoot m p
      (m:) <$> go (p:done) (ps ++ [ d </> i -<.> "ctt" | i <- moduleImports m ])


--------------------------------------------------------------------------------
---- Main

main :: IO ()
main = execParser options >>= \case
  Eval m p -> evalModule m p
  Repl _   -> runRepl repl
