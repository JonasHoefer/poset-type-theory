-- | Minimal SAT solver by Koen Claessen
module PosTT.SAT where

import           Prelude hiding (mod)

import           Control.Monad

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (isJust, isNothing)

import           Algebra.Lattice


data Form a
  = Var a
  | And [Form a]
  | Or [Form a]
  | Not (Form a)
 deriving (Eq, Ord, Show, Functor)

instance Applicative Form where
  pure :: a -> Form a
  pure = Var

  (<*>) :: Form (a -> b) -> Form a -> Form b
  (<*>) = ap

instance Monad Form where
  (>>=) :: Form a -> (a -> Form b) -> Form b
  Var x  >>= k = k x
  And ts >>= k = And (map (>>= k) ts)
  Or ts  >>= k = Or (map (>>= k) ts)
  Not t  >>= k = Not (t >>= k)

instance SupSemilattice (Form a) where
  bot = Or []
  s \/ t = Or [s, t]

instance InfSemilattice (Form a) where
  top = And []
  s /\ t = And [s, t]

impl :: Form a -> Form a -> Form a
impl r s = Or [Not r, s]

equiv :: Form a -> Form a -> Form a
equiv r s = Or [And [r, s], And [Not r, Not s]]

model :: Ord a => Form a -> Maybe (Map a Bool)
model p = search M.empty [p]
 where
  search mod []                 = Just mod
  search mod (Var x       : qs) = literal x True  mod qs
  search mod (Not (Var x) : qs) = literal x False mod qs
  search mod (And ps      : qs) = search mod (ps ++ qs)
  search _   (Or []       : _ ) = Nothing
  search mod (Or (p:ps)   : qs) = search mod (p:qs) <> search mod (Not p:Or ps:qs)
  search mod (Not (And ps): qs) = search mod (Or  (map Not ps):qs)
  search mod (Not (Or  ps): qs) = search mod (And (map Not ps):qs)
  search mod (Not (Not p) : qs) = search mod (p:qs)

  literal x b mod ps =
    case M.lookup x mod of
      Just a | a /= b -> Nothing
      _               -> (search $! M.insert x b mod) ps

-- | Has a model
sat :: Ord a => Form a -> Bool
sat = isJust . model

-- | Has no models
unsat :: Ord a => Form a -> Bool
unsat = isNothing . model

-- | All valuations are models
val :: Ord a => Form a -> Bool
val = unsat . Not
