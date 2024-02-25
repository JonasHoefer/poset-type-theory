module Main where

import PosTT.Eval
import PosTT.Terms
import PosTT.Values
import PosTT.Quotation
import PosTT.Pretty

main :: IO ()
main = putStrLn $ pretty $ bindStage terminalStage $ readBack $ eval EmptyEnv $ Lam $ Binder "A" $ Lam $ Binder "B" $ Sigma (Var "A") (Binder "x" (Var "B"))

