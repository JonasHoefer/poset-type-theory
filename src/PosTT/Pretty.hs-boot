-- | hs-boot file for circular inclusion of the pretty printing module.
--
-- This file is only needed for debugging. The core has no circular dependencies.
module PosTT.Pretty (prettyVal, pretty) where

import           PosTT.Terms
import           PosTT.Values


prettyVal :: AtStage (Val -> String)

pretty :: Tm -> String