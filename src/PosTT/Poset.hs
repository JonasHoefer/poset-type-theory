-- | Algorithms for operating on objects of the base category
module PosTT.Poset where

import Algebra.Lattice

import Data.Maybe

import PosTT.Values


instance Restrictable VI where
  type Alt VI = VI

  act :: Restr -> VI -> VI
  act IdRestr   r      = r
  act (Restr α) (VI r) = sup [ inf [ fromMaybe (iVar x) (lookup x α) | x <- cs ] | cs <- r ]
    

instance Convertible VI where
  (===) = error "TODO: copy"

simplifySys :: VSys a -> Either a (VSys a)
simplifySys = error "TODO: copy"