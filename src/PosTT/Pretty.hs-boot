module PosTT.Pretty (prettyVal, pretty) where

import           PosTT.Terms
import           PosTT.Values


prettyVal :: AtStage (Val -> String)

pretty :: Tm -> String