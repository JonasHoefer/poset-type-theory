module PosTT.HeadLinearReduction where

import qualified Data.Map as M

import           PosTT.Common
import           PosTT.Terms

headUnfoldN :: Int -> M.Map Name Int -> [(Name, Tm)] -> Tm -> (M.Map Name Int, Int, Tm)
headUnfoldN = error "TODO"

headUnfoldAll :: M.Map Name Int -> [(Name, Tm)] -> Tm -> (M.Map Name Int, Int, Tm)
headUnfoldAll = error "TODO"
