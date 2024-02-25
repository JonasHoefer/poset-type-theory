module PosTT.Common where

import Data.String (IsString(..))


newtype Name = Name { unName :: String } deriving (Eq, IsString)

type SrcSpan = Maybe ((Int, Int), (Int, Int))

extractWith :: (a -> a -> Bool) -> a -> [(a, b)] -> Maybe (b, [(a, b)])
extractWith p _ []             = Nothing
extractWith p k (e@(k', v):vs) 
  | p k k'    = Just (v, vs)
  | otherwise = fmap (fmap (e:)) (extractWith p k vs)