module Algebra.Lattice where

--------------------------------------------------------------------------------
---- Some Lattice Operators

class InfSemilattice a where
  (/\) :: a -> a -> a
  top :: a

inf :: (InfSemilattice a, Foldable t) => t a -> a
inf = foldr (/\) top

class SupSemilattice a where
  (\/) :: a -> a -> a
  bot :: a

sup :: (SupSemilattice a, Foldable t) => t a -> a
sup = foldr (\/) bot
