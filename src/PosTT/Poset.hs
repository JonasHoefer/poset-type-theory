-- | Algorithms for operating on objects of the base category
module PosTT.Poset where

import PosTT.Values




instance Convertible VI where
  (===) = error "TODO: copy"

simplifySys :: VSys a -> Either a (VSys a)
simplifySys = error "TODO: copy"