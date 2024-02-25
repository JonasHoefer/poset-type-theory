-- | Algorithms for operating on objects of the base category
module PosTT.Poset where

import Algebra.Lattice

import Data.Maybe

import PosTT.Values



comp :: Restr -> Restr -> Restr
comp (Restr α) (Restr β) = Restr $ [ (z, r) | (z, r) <- α, z `notElem` map fst β ] ++ [ (x, r `subst` Restr α) | (x, r) <- β ]

subst :: VI -> Restr -> VI
subst r     IdRestr    = r
subst (VI r) (Restr α) = sup [ inf [ fromMaybe (iVar x) (lookup x α) | x <- cs ] | cs <- r ]

instance Restrictable VI where
  type Alt VI = VI

  act :: AtStage (Restr -> VI -> VI)
  act = flip subst

instance Conv VI where
  conv :: AtStage (VI -> VI -> Either String ())
  conv = error "TODO: copy"

instance Conv VCof where

simplifySys :: VSys a -> Either a (VSys a)
simplifySys = error "TODO: copy"
