module PosTT.Common where

extractWith :: (a -> a -> Bool) -> a -> [(a, b)] -> Maybe (b, [(a, b)])
extractWith p _ []             = Nothing
extractWith p k (e@(k', v):vs) 
  | p k k'    = Just (v, vs)
  | otherwise = fmap (fmap (e:)) (extractWith p k vs)