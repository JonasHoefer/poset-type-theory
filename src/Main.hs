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
import           System.FilePath (stripExtension, (</>), (-<.>), stripExtension, splitDirectories, joinPath)

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
  let (res, msgs) = checkDeclsEnv preTm
  mapM_ putStrLn msgs
  rho   <- either (error . show) return res

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

data ReplCmd = Term String | Load Bool FilePath | Reload Bool | Quit | Unfold Int String | Infer String deriving (Show)

inferCmd :: Mod CommandFields ReplCmd
inferCmd = command ":infer"
  (info
    (Infer . unwords <$> many (strArgument (metavar "FILE"))) -- we just take all remaining strings
    (progDesc "Infers type of give term and remembers it"))

loadCmd :: Mod CommandFields ReplCmd
loadCmd = command ":load"
  (info
    (Load <$> switch (long "silent" <> short 's' <> help "Hide non-error messages")
          <*> argument str (metavar "FILE"))
    (progDesc "Load file"))

reloadCmd :: Mod CommandFields ReplCmd
reloadCmd = command ":reload"
  (info
     (Reload <$> switch (long "silent" <> short 's' <> help "Hide non-error messages"))
     (progDesc "Reload current module"))

quitCmd :: Mod CommandFields ReplCmd
quitCmd = command ":quit" (info (pure Quit) (progDesc "Quit repl"))

unfoldCmd :: Mod CommandFields ReplCmd
unfoldCmd = command ":unfold" $ info
  (Unfold <$> option auto (short 's' <> metavar "STEPS" <> showDefault <> value 1 <> help "Number of unfold steps")
          <*> (unwords <$> many (argument str (metavar "DEF"))))
  (progDesc "Perform a single unfolding steps on given definition or, if not argument is given, on the last considered term.")

replCmdStrings :: [String]
replCmdStrings = [":load", ":reload", ":quit", ":unfold", ":infer"]

replCmds :: ParserInfo ReplCmd
replCmds = info (subparser (quitCmd <> loadCmd <> reloadCmd <> unfoldCmd <> inferCmd)) mempty

parseReplCmd :: String -> Either String ReplCmd
parseReplCmd ""                                 = Left ""
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
  , lastUnfold :: !(Maybe (Either String Tm))
  }

environment :: ReplState -> Env
environment = env . context

type Repl a = InputT (StateT ReplState IO) a

replCompletion :: CompletionFunc (StateT ReplState IO)
replCompletion input@(reverse -> s, _)
  | ":load"   `isPrefixOf` s = completeFilename input -- also for unfold?
  | ":infer"  `isPrefixOf` s = identCompletion
  | ":unfold" `isPrefixOf` s = identCompletion
  | ":"       `isPrefixOf` s = completeWord Nothing [] (return . cmdSearch) input
  | otherwise                = identCompletion
  where
    identCompletion :: StateT ReplState IO (String, [Completion])
    identCompletion = completeWord' Nothing (\c -> not (isAlphaNum c || c `elem` ("-/\\<>"::String))) nameSearch input

    cmdSearch :: String -> [Completion]
    cmdSearch s' = map simpleCompletion $ filter (s' `isPrefixOf`) replCmdStrings

    nameSearch :: String -> StateT ReplState IO [Completion]
    nameSearch s' = map simpleCompletion <$> gets (filter (s' `isPrefixOf`) . map show . envIdents . env . context)

replSettings :: Settings (StateT ReplState IO)
replSettings = Settings { historyFile = Just ".postt_history", complete = replCompletion, autoAddHistory = True }

runRepl :: Repl a -> IO a
runRepl = flip evalStateT initialReplState . runInputT replSettings

initialReplState :: ReplState
initialReplState = ReplState "" Nothing mempty emptyCxt Nothing

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
        Right (Load silent p) -> do
          () <- ifM (liftIO (doesFileExist p))
            (replLoad silent p)
            (outputStrLn $ "File " ++ show p ++ " does not exist!")
          repl
        Right (Reload silent) -> do
          gets currentFile >>= \case
            Just p  -> replLoad silent p
            Nothing -> outputStrLn "No module loaded!"
          repl
        Right (Infer t) -> do
          scpEnv <- gets scopeCheckerEnv
          case parsePTm scpEnv t of
            Left err -> outputStrLn err
            Right pt -> do
              cxt <- gets context
              let (res, msgs) = runTC cxt (infer pt)
              mapM_ outputStrLn msgs
              case res of
                Left err       -> outputStrLn $ show err
                Right (tm, ty) -> do
                  outputStrLn ("Infered Type: " ++ bindStage terminalStage prettyVal ty)
                  modify $ \s -> s{ lastUnfold = Just (Right tm) }
          repl
        Right (Term t) -> do
          scpEnv <- gets scopeCheckerEnv
          case parsePTm scpEnv t of
            Left err -> outputStrLn err
            Right pt -> do
              cxt <- gets context
              let (res, msgs) = runTC cxt (inferAndEval pt)
              mapM_ outputStrLn msgs
              case res of
                Left err          -> outputStrLn $ show err
                Right (_, val, _) -> outputStrLn $ bindStage terminalStage prettyVal val
          repl
        Right (Unfold k "") -> do
          lastUnfoldTarget >>= \case
            Nothing       ->
              outputStrLn "No current unfold target. Either unfold a definition using `:unfold DEF` or load a term using `:infer TERM`"
            Just (t, rep) -> do
              unfoldTerm k t >>= rep
          repl
        Right (Unfold k d) -> do
          defUnfoldTarget d >>= \case
            Just (t, rep) -> 
              unfoldTerm k t >>= rep
            Nothing       ->
              outputStrLn $ d ++ " is not a definition!"
          repl

unfoldTerm :: Int -> Tm -> Repl Tm
unfoldTerm k t = do
  ρ <- gets environment
  let (u, t') = headUnfold ρ t (Just k)
  outputStrLn $ pretty t'
  outputStrLn ""
  outputStrLn $ "Unfold counts: " ++ intercalate ", " [ show x ++ ": " ++ show c | (x, c) <- M.toList u]
  return t'
  
-- | Returns the term associated to a definition, and a way to replace it, if this definition exists.
defUnfoldTarget :: String -> Repl (Maybe (Tm, Tm -> Repl ()))
defUnfoldTarget d = gets (lookup (fromString d) . environment) >>= \case
  Just (EntryDef t _) -> do
    let rep t' = modify $ \s ->
          s{ context = (context s) { env = modifyAt (fromString d) (\(EntryDef _ ty) -> EntryDef t' ty) (env (context s)) }
           , lastUnfold = Just (Left d)
           }
    return $ Just (t, rep)
  _notDefined -> return Nothing

-- | Returns the term that was last unfolded, and a way to replace it, if such a term exists.
lastUnfoldTarget :: Repl (Maybe (Tm, Tm -> Repl ()))
lastUnfoldTarget = gets lastUnfold >>= \case
  Nothing        -> return Nothing
  Just (Left d)  -> defUnfoldTarget d
  Just (Right t) -> do
    let rep t' = modify $ \s -> s{ lastUnfold = Just (Right t') }
    return $ Just (t, rep)

replLoad :: Bool -> FilePath -> Repl ()
replLoad silent p = do
  liftIO (runExceptT $ recursiveLoad p) >>= \case
    Right ms -> case checkModules ms of
      Right (scpEnv, ds) -> do
        let (res, msgs) = checkDeclsCxt ds
        unless silent $ mapM_ outputStrLn msgs
        case res of
          Right cxt -> do
            put $ ReplState (moduleName $ head ms) (Just p) scpEnv cxt Nothing
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
  Repl p   -> runRepl (mapM (replLoad False) p *> repl)
