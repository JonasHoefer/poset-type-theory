-- | Algorithms and instances for computing with objects of the base category
module PosTT.Poset where

import           Algebra.Lattice

import           Control.Monad (unless)

import           Data.Bifunctor
import           Data.Either (fromRight)
import           Data.Maybe
import qualified Data.Graph as G
import qualified Data.IntSet as S

import           PosTT.Common
import           PosTT.Errors (ConvError(..))
import           PosTT.SAT
import           PosTT.Values


--------------------------------------------------------------------------------
---- Interval

forAll :: AtStage (Gen -> VCof -> VCof)
forAll i φ = (φ @ (0 `for` i)) /\ (φ @ (1 `for` i)) 

instance SupSemilattice VI where
  (\/) :: VI -> VI -> VI
  VI r \/ VI s = VI (r ++ s)

  bot :: VI
  bot = VI []

instance InfSemilattice VI where
  (/\) :: VI -> VI -> VI
  VI r /\ VI s = VI [ m ++ n | m <- r, n <- s ]

  top :: VI
  top = VI [[]]

instance Num VI where
  fromInteger :: Integer -> VI
  fromInteger 0 = bot
  fromInteger 1 = top

  (+) :: VI -> VI -> VI
  (+) = error "Only for literals"

  (*) :: VI -> VI -> VI
  (*) = error "Only for literals"

  abs :: VI -> VI
  abs = error "Only for literals"
  
  signum :: VI -> VI
  signum = error "Only for literals"
  
  negate :: VI -> VI
  negate = error "Only for literals"


--------------------------------------------------------------------------------
---- Restriction Maps

for :: VI -> Gen -> Restr
r `for` i = Restr [(i, r)]

comp :: Restr -> Restr -> Restr
comp (Restr α) (Restr β) = 
  Restr $ [ (z, r) | (z, r) <- α, z `notElem` map fst β ] ++ [ (x, r `subst` Restr α) | (x, r) <- β ]

subst :: VI -> Restr -> VI
subst r     IdRestr    = r
subst (VI r) (Restr α) = sup [ inf [ fromMaybe (iVar x) (lookup x α) | x <- cs ] | cs <- r ]

instance Restrictable VI where
  type Alt VI = VI

  act :: AtStage (Restr -> VI -> VI)
  act = flip subst

instance Restrictable VCof where
  type Alt VCof = VCof

  act :: AtStage (Restr -> VCof -> VCof)
  f `act` VCof eqs = VCof (map (bimap (@ f) (@ f)) eqs)


--------------------------------------------------------------------------------
---- Conversion

instance Conv VI where
  conv :: AtStage (VI -> VI -> Either ConvError ())
  r `conv` s = unless (r `equivalent` s) $ Left (ConvErrorI (readBack r) (readBack s))

instance Conv VCof where
  conv :: AtStage (VCof -> VCof -> Either ConvError ())
  conv φ ψ = unless (φ `equivalentCof` ψ) $ Left (ConvErrorCof (readBack φ) (readBack ψ))


--------------------------------------------------------------------------------
---- SAT

toBoolExpr :: VI -> Form Gen
toBoolExpr (VI sys) = sup [ inf (map return cl) | cl <- sys ]

-- | Checks whether two interval expression are equivalent w.r.t. to a set of cofibrations.
--
-- If I, φ₁, …, φₙ ⊢ r : 𝕀 and I, φ₁, …, φₙ ⊢ s : 𝕀 then we decide if I, Ψ ⊢ r ≡ s : 𝕀
-- For that we check the validity of the formula φ₁ ∧ … ∧ φₙ → (r ↔ s) as a boolean formula.
-- Here, we interpret a cofibration φₗ = φᵣ as the boolean formula φₗ ↔ φᵣ.
--
-- Formally, we decide a word problem in a finite distrib lattice D=⟨X∣R⟩ with r,s ∈ Free(X)
equivalent :: AtStage (VI -> VI -> Bool)
equivalent r s = val $ stageCofForm `impl` (toBoolExpr r `equiv` toBoolExpr s)

cofToBoolExpr :: VCof -> Form Gen
cofToBoolExpr (VCof φ) = And [ toBoolExpr lhs `equiv` toBoolExpr rhs | (lhs, rhs) <- φ ]

stageCofForm :: AtStage (Form Gen)
stageCofForm = cofToBoolExpr (cof ?s)

impliesCof :: AtStage (VCof -> VCof -> Bool)
impliesCof φ ψ = val $ stageCofForm `impl` (cofToBoolExpr φ `impl` cofToBoolExpr ψ)

equivalentCof :: AtStage (VCof -> VCof -> Bool)
equivalentCof φ ψ = val $ stageCofForm `impl` (cofToBoolExpr φ `equiv` cofToBoolExpr ψ)

validCof :: AtStage (VCof -> Bool)
validCof φ = val $ stageCofForm `impl` cofToBoolExpr φ

satisfiableCof :: AtStage (VCof -> Bool)
satisfiableCof φ = sat $ stageCofForm /\ cofToBoolExpr φ


--------------------------------------------------------------------------------
---- Systems

simplifySys :: forall a. AtStage (VSys a -> Either a (VSys a))
simplifySys (VSys sys) = reducedRemaining  -- TODO: pick only satisfyable ones!
  where
    branches :: [(Int, VCof, a)]
    branches = [ (key, φ, a) | (key, (φ, a)) <- [0..] `zip` sys ]

    cofibGraph :: [((VCof, a), Int, [Int])]
    cofibGraph = [ ((φ₁, a₁), k₁, [ k₂ | (k₂, φ₂, _) <- branches, k₂ /= k₁, φ₁ `impliesCof` φ₂ ]) | (k₁, φ₁, a₁) <- branches]

    remaining :: [(VCof, a)]
    remaining = map pickRep $ takeWhile (not . hasOutgoing) $ G.stronglyConnCompR cofibGraph

    reducedRemaining :: Either a (VSys a)
    reducedRemaining = case remaining of
      [(cofibs, b)] | validCof cofibs             -> Left b
      [(cofibs, _)] | not (satisfiableCof cofibs) -> Right $ VSys []
      _                                           -> Right $ VSys remaining

    hasOutgoing :: G.SCC (node, Int, [Int]) -> Bool
    hasOutgoing (G.AcyclicSCC (_, x, xs)) = any (x /=) xs -- outgoing, that is not self-loop
    hasOutgoing (G.CyclicSCC ns)          = any (\out -> not $ out `S.isSubsetOf` inSCC) [ S.fromList out | (_, _, out) <- ns ]
      where inSCC = S.fromList $ map (\(_, x, _) -> x) ns -- any node in scc has outgoing (`out`) that is not in same SCC (`inSCC`)

    pickRep :: G.SCC (node, Int, [Int]) -> node
    pickRep (G.AcyclicSCC (n, _, _))    = n
    pickRep (G.CyclicSCC ((n, _, _):_)) = n

unionSys :: AtStage (VSys a -> VSys a -> VSys a)
unionSys sys₁ sys₂ = fromRight (error "Union of non-trivial systems is trivial!") (simplifySys (sys₁ <> sys₂))

sidePairs :: Restrictable a => AtStage (VSys a -> VSys (Alt a, Alt a))
sidePairs (VSys bs) = VSys [ (φ, extCof φ (re a₀, re a₁)) | ((φ₀, a₀), (φ₁, a₁)) <- incrPairs bs, let φ = φ₀ /\ φ₁ ]
  where
    incrPairs :: [a] -> [(a, a)]
    incrPairs []     = []
    incrPairs (x:xs) = map (x,) xs ++ incrPairs xs

-- | Maps over a system, adjusting the stage.
mapSys :: AtStage (VSys a -> AtStage (a -> b) -> VSys b)
mapSys (VSys sys) f = VSys [ (φ, extCof φ (f a)) | (φ, a) <- sys ]

-- | Part of ' collection of functions for working on potentially simplified systems
mapSys' :: AtStage (Either a (VSys a) -> AtStage (a -> b) -> Either b (VSys b))
mapSys' sys f = bimap f (`mapSys` f) sys

-- | Monadic version of `mapSys` 
mapSysM :: Monad m => AtStage (VSys a -> AtStage (a -> m b) -> m (VSys b))
mapSysM sys f = fmap VSys $ mapM sequence $ unVSys $ mapSys sys f


consSys :: AtStage (VSys a -> VCof -> AtStage a -> VSys a)
consSys (VSys sys) φ a = VSys ((φ, extCof φ a) : sys)

singSys :: AtStage (VCof -> AtStage a -> VSys a)
singSys = consSys EmptySys

-- | Modifies the cofibrations in the branches of a systems, but does *not* simplify.
mapSysCof :: (VCof -> VCof) -> VSys a -> VSys a
mapSysCof f (VSys bs) = VSys (map (first f) bs)

-- | Combines the branches of a system, with a list of the same length.
--   Does not modify the system itself. 
zipSys :: VSys a -> [b] -> VSys (a, b)
zipSys (VSys sys) bs = VSys [ (φ, (a, b)) | ((φ, a), b) <- sys `zip` bs ]
