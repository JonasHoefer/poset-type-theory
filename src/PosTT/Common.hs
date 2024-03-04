module PosTT.Common where

import           Data.ByteString.Char8 (unpack)
import qualified Data.ByteString as B
import           Data.String (IsString(..))


newtype Name = Name { unName :: B.ByteString } deriving (Eq, Ord)

instance Show Name where
  show = unpack . unName

instance IsString Name where
  fromString s = Name (fromString s)

type Gen = Name

type SrcSpan = Maybe ((Int, Int), (Int, Int))

extractWith :: (a -> a -> Bool) -> a -> [(a, b)] -> Maybe (b, [(a, b)])
extractWith _ _ []             = Nothing
extractWith p k (e@(k', v):vs)
  | p k k'    = Just (v, vs)
  | otherwise = (fmap . fmap) (e:) (extractWith p k vs)

modifyAt :: Eq a => a -> (b -> b) -> [(a, b)] -> [(a, b)]
modifyAt x f = map $ \(y, u) -> if x == y then (y, f u) else (y, u)

unifyEither :: (b -> a) -> [Either a b] -> Either [a] [b]
unifyEither f xs = either (const $ Left $ map (either id f) xs) Right $ sequence xs

impossible :: String -> a
impossible msg = error $ "Impossible: " ++ msg
