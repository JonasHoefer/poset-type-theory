module Algebra.Lattice where

--------------------------------------------------------------------------------
---- Some Lattice Operators

class InfLattice a where
  (/\) :: a -> a -> a
  top :: a

inf :: (InfLattice a, Foldable t) => t a -> a
inf = foldr (/\) top

class SupLattice a where
  (\/) :: a -> a -> a
  bot :: a

sup :: (SupLattice a, Foldable t) => t a -> a
sup = foldr (\/) bot