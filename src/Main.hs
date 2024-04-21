module Main where

import           Data.Char (isAlphaNum)
import           Data.Either.Extra (maybeToEither)
import           Data.List (intercalate, isSuffixOf, isPrefixOf)
import           Data.List.Extra (dropSuffix)
import           Data.List.Split (splitOn)
import qualified Data.Map as M
import           Data.String (IsString(..))
import           Data.Tuple.Extra (fst3)

import           Control.Monad.Except
import           Control.Monad.Extra (ifM)
import           Control.Monad.State.Strict

import           System.Console.Haskeline
import           System.Directory
import           System.FilePath (stripExtension, (</>), (-<.>), stripExtension, splitFileName, splitDirectories, joinPath)

import           Options.Applicative as O

import           PosTT.Common
import           PosTT.Terms
import           PosTT.Values
import           PosTT.HeadLinearReduction
import           PosTT.Pretty (pretty, prettyVal)
import           PosTT.Quotation (normalize)
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
  rawTm <- either (error . show) id <$> runExceptT (recursiveLoad p)
  preTm <- either (error . show) (return . snd) (checkModules rawTm)
  rho   <- either (error . show) return (checkDeclsEnv preTm)

  putStrLn $ "\nSuccessfully checked " ++ show (length rho) ++ " definitions"

  case rho of
    EnvCons _ x (EntryDef s _) -> case m of
      Default -> do
        putStrLn $ "Evaluation of " ++ pretty s
        putStrLn $ "Yields " ++ pretty (normalize rho $ Var x)
      HeadLinear -> do
        let (u, s') = headUnfold rho s Nothing

        putStrLn $ "Head linear unfolding of " ++ pretty s
        putStrLn $ "Yields " ++ pretty s'
        putStrLn ""
        putStrLn $ "Unfold counts: " ++ intercalate ", " [ show d ++ ": " ++ show c | (d, c) <- M.toList u]
        putStrLn $ "Hence " ++ show (sum u) ++ " unfold steps"
    _ -> putStrLn "No definitions"


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
  (progDesc "Perform head linear unfolding steps on a definition in the context")

replCmdStrings :: [String]
replCmdStrings = [":load", ":reload", ":quit", ":unfold"]

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

replCompletion :: CompletionFunc (StateT ReplState IO)
replCompletion input@(s, _)
  | ":load" `isPrefixOf` reverse s = completeFilename input -- also for unfold?
  | ":"     `isPrefixOf` reverse s = completeWord Nothing [] (return . cmdSearch) input
  | otherwise                      = completeWord' Nothing (\c -> not (isAlphaNum c || c == '-')) nameSearch input
  where
    cmdSearch :: String -> [Completion]
    cmdSearch s = map simpleCompletion $ filter (s `isPrefixOf`) replCmdStrings

    nameSearch :: String -> StateT ReplState IO [Completion]
    nameSearch s = map simpleCompletion <$> gets (filter (s `isPrefixOf`) . map show . envIdents . env . context)

replSettings :: Settings (StateT ReplState IO)
replSettings = Settings { historyFile = Just ".postt_history", complete = replCompletion, autoAddHistory = True }

runRepl :: Repl a -> IO a
runRepl = flip evalStateT initialReplState . runInputT replSettings

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
          () <- ifM (liftIO (doesFileExist p))
            (replLoad p)
            (outputStrLn $ "File " ++ show p ++ " does not exist!")
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
            Just (EntryDef t _) -> do
              ρ <- gets environment
              let (u, t') = headUnfold ρ t (Just k)
              modify $ \s -> s{ context = (context s) { env = modifyAt (fromString d) (\(EntryDef _ ty) -> EntryDef t' ty) (env (context s)) } }
              outputStrLn $ pretty t'
              outputStrLn ""
              outputStrLn $ "Unfold counts: " ++ intercalate ", " [ show x ++ ": " ++ show c | (x, c) <- M.toList u]
            _ -> outputStrLn $ d ++ " is not defined!"
          repl

replLoad :: FilePath -> Repl ()
replLoad p = do
  liftIO (runExceptT $ recursiveLoad p) >>= \case
    Right ms -> case checkModules ms of
      Right (scpEnv, ds) -> case checkDeclsCxt ds of
        Right cxt -> do
          put $ ReplState (moduleName $ head ms) (Just p) scpEnv cxt
          outputStrLn $ "Successfully checked " ++ show (length (env cxt)) ++ " definitions"
        Left err -> outputStrLn $ show err
      Left err -> outputStrLn $ show err
    Left err -> outputStrLn $ show err


--------------------------------------------------------------------------------
---- File Loading

moduleRoot :: Module -> FilePath -> Either String FilePath
moduleRoot m p = go (splitOn "." $ moduleName m) =<< maybeToEither "Expected .ctt file" (stripExtension "ctt" p)
  where
    go :: [String] -> FilePath -> Either String FilePath
    go parts (splitDirectories -> path)
      | parts `isSuffixOf` path = Right $ joinPath (dropSuffix parts path)
      | otherwise               = Left $ "Module name " ++ moduleName m ++ " does not match path " ++ p ++ show (parts, path)

recursiveLoad :: FilePath -> ExceptT String IO [Module]
recursiveLoad rp = liftIO (makeAbsolute rp) >>= go [] . pure
  where
    go :: [FilePath] -> [FilePath] -> ExceptT String IO [Module]
    go _    []     = return []
    go done (p:ps) | p `elem` done = go done ps
    go done (p:ps) = do
      m <- ExceptT $ parseModule <$> readFile p
      d <- either error return $ moduleRoot m p
      (m:) <$> go (p:done) (ps ++ [ foldl (</>) d (splitOn "." i) -<.> "ctt" | i <- moduleImports m ])


--------------------------------------------------------------------------------
---- Main

main :: IO ()
main = execParser options >>= \case
  Eval m p -> evalModule m p
  Repl _   -> runRepl repl
