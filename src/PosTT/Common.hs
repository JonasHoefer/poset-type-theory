module PosTT.Common where

import           Data.ByteString.Char8 (unpack)
import           Data.ByteString.Internal (c2w)
import qualified Data.ByteString as B
import           Data.String (IsString(..))
import qualified Data.Map.Strict as M
import qualified Data.IntSet as S


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


--------------------------------------------------------------------------------
---- Minor utilities for names

adjustDef :: Ord k => a -> (a -> a) -> k -> M.Map k a -> M.Map k a
adjustDef d f = M.alter (Just . maybe (f d) f)

type NameStore = M.Map B.ByteString S.IntSet

emptyStore :: NameStore
emptyStore = M.empty

breakName :: Name -> (B.ByteString, B.ByteString)
breakName = B.breakEnd (/= c2w '\'') . unName

addNameStore :: Name -> NameStore -> NameStore
addNameStore (breakName -> (s, primes)) = adjustDef S.empty (S.insert (B.length primes)) s

refreshNameStore :: Name -> NameStore -> (NameStore, Name)
refreshNameStore n store | n == "_" = (store, n)
refreshNameStore n@((breakName -> (s, B.length -> primes))) store = case S.member primes <$> (store M.!? s) of
  Just True -> let primes' = 1 + S.findMax (store M.! s)
               in (adjustDef S.empty (S.insert primes') s store, Name $ s `B.append` B.replicate primes' (c2w '\''))
  _         -> (adjustDef S.empty (S.insert primes) s store, n)
