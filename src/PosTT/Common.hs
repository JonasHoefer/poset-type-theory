module PosTT.Common where

import           Data.ByteString.Char8 (unpack)
import qualified Data.ByteString as B
import qualified Data.ByteString.Internal as B
import           Data.String (IsString(..))


newtype Name = Name { unName :: B.ByteString } deriving (Eq, Ord, IsString)

instance Show Name where
  show = unpack . unName

newtype Gen = Gen { unGen :: B.ByteString } deriving (Eq, Ord, IsString)

instance Show Gen where
  show = unpack . unGen

type SrcSpan = Maybe ((Int, Int), (Int, Int))

extractWith :: (a -> a -> Bool) -> a -> [(a, b)] -> Maybe (b, [(a, b)])
extractWith p _ []             = Nothing
extractWith p k (e@(k', v):vs) 
  | p k k'    = Just (v, vs)
  | otherwise = fmap (fmap (e:)) (extractWith p k vs)

impossible :: String -> a
impossible msg = error $ "Impossible: " ++ msg
