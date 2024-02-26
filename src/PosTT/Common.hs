module PosTT.Common where

import           Data.ByteString.Char8 (unpack)
import qualified Data.ByteString as B
import qualified Data.ByteString.Internal as B
import           Data.Hashable
import           Data.String (IsString(..))


data Name = Name { code :: Int, unName :: B.ByteString } deriving (Eq, Ord)

instance Show Name where
  show = unpack . unName

instance IsString Name where
  fromString s = Name (hash s) (fromString s)

newtype Gen = Gen { unGen :: Name } deriving (Eq, Ord, IsString) deriving Show via Name

type SrcSpan = Maybe ((Int, Int), (Int, Int))

extractWith :: (a -> a -> Bool) -> a -> [(a, b)] -> Maybe (b, [(a, b)])
extractWith p _ []             = Nothing
extractWith p k (e@(k', v):vs) 
  | p k k'    = Just (v, vs)
  | otherwise = fmap (fmap (e:)) (extractWith p k vs)

impossible :: String -> a
impossible msg = error $ "Impossible: " ++ msg
