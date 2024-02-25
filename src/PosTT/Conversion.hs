module PosTT.Conversion where

import Control.Monad (zipWithM_, unless)

import PosTT.Common
import PosTT.Poset
import PosTT.Eval
import PosTT.Terms
import PosTT.Values


--------------------------------------------------------------------------------
---- Conversion Checking

convPi :: AtStage (Val -> Val -> Either String ())
u `convPi` v = freshFibVar (\x -> (u `doApp` x) `conv` (v `doApp` x))

convSigma :: AtStage (Val -> Val -> Either String ())
u `convSigma` v = (doPr1 u, doPr2 u) `conv` (doPr1 v, doPr2 v)

convPath :: AtStage (Val -> Val -> Val -> Val -> Either String ())
convPath a₀ a₁ u v = freshIntVar (\i -> doPApp a₀ a₁ u i `conv` doPApp a₀ a₁ v i)

convExt :: AtStage (VSys Val -> Val -> Val -> Either String ())
convExt ws u v = doExtFun ws u `conv` doExtFun ws v -- TODO: is this correct?

instance Conv Val where
  conv :: AtStage (Val -> Val -> Either String ())
  conv = curry $ \case
    (VU, VU) -> pure ()

    (VPi a₀ b₀   , VPi a₁ b₁   ) -> (a₀, b₀) `conv` (a₁, b₁)
    (u@VLam{}    , v           ) -> u `convPi` v
    (u           , v@VLam{}    ) -> u `convPi` v
    (u@VCoePi{}  , v           ) -> u `convPi` v
    (u           , v@VCoePi{}  ) -> u `convPi` v
    (u@VHCompPi{}, v           ) -> u `convPi` v
    (u           , v@VHCompPi{}) -> u `convPi` v

    (VSigma a₀ b₀   , VSigma a₁ b₁   ) -> (a₀, b₀) `conv` (a₁, b₁)
    (u@VPair{}      , v              ) -> u `convSigma` v
    (u              , v@VPair{}      ) -> u `convSigma` v
    (u@VCoeSigma{}  , v              ) -> u `convSigma` v
    (u              , v@VCoeSigma{}  ) -> u `convSigma` v
    (u@VHCompSigma{}, v              ) -> u `convSigma` v
    (u              , v@VHCompSigma{}) -> u `convSigma` v

    (VPath a₀ a₀₀ a₀₁ , VPath a₁ a₁₀ a₁₁ ) -> (a₀, a₀₀, a₀₁) `conv` (a₁, a₁₀, a₁₁)
    (u@(VPLam _ a₀ a₁), v                ) -> convPath a₀ a₁ u v
    (u                , v@(VPLam _ a₀ a₁)) -> convPath a₀ a₁ u v
    (u@(VCoePath _ _ _ _ a₀ a₁ _ _), v)    -> convPath a₀ a₁ u v
    (u, v@(VCoePath _ _ _ _ a₀ a₁ _ _))    -> convPath a₀ a₁ u v
    (u@(VHCompPath _ _ _ a₀ a₁ _ _), v)    -> convPath a₀ a₁ u v
    (u, v@(VHCompPath _ _ _ a₀ a₁ _ _))    -> convPath a₀ a₁ u v

    (VCoePartial _ _ cl₀, VCoePartial _ _ cl₁) -> cl₀ `conv` cl₁

    (VExt a₀ b₀      , VExt a₁ b₁      ) -> (a₀, b₀) `conv` (a₁, b₁)
    (u@(VExtElm _ ws), v               ) -> convExt ws u v
    (u               , v@(VExtElm _ ws)) -> convExt ws u v

    (VSum d₀ _         , VSum d₁ _         ) -> d₀ `conv` d₁
    (VCon c₀ as₀       , VCon c₁ as₁       ) | c₀ == c₁ -> as₀ `conv` as₁
    (VSplitPartial f₀ _, VSplitPartial f₁ _) -> f₀ `conv` f₁

    (VNeu k₀, VNeu k₁) -> k₀ `conv` k₁

instance Conv (Closure Tm) where
  conv :: AtStage (Closure Tm -> Closure Tm -> Either String ())
  cl₀ `conv ` cl₁ = freshFibVar (\x -> (cl₀ $$ x) `conv` (cl₁ $$ x))

instance Conv TrIntClosure where
  conv :: AtStage (TrIntClosure -> TrIntClosure -> Either String ())
  cl₀ `conv ` cl₁ = freshIntVar (\x -> (cl₀ $$ x) `conv` (cl₁ $$ x))

instance Conv Neu where
  conv :: AtStage (Neu -> Neu -> Either String ())
  conv = curry $ \case
    (NVar x₀, NVar x₁) -> unless (x₀ == x₁) (Left "") -- (Left $ x₀ ++ " ≠ " ++ x₁)
--    NApp :: Neu -> Val -> Neu
--    NPr1 :: Neu -> Neu
--    NPr2 :: Neu -> Neu
--    NPApp :: Neu -> Val -> Val -> VI -> Neu
--    NCoePartial :: VI -> VI -> TrNeuIntClosure -> Neu
--    NHComp :: VI -> VI -> Neu -> Val -> VSys TrIntClosure -> Neu
    -- NHCompSum :: VI -> VI -> VTy -> [VLabel] -> Neu -> VSys IntClosure -> Neu
--    NExtFun :: VSys Val -> Neu -> Neu
--    NSplit :: Val -> [VBranch] -> Neu -> Neu


instance Conv a => Conv (VSys a) where
  conv :: Conv a => AtStage (VSys a -> VSys a -> Either String ())
  conv EmptySys            EmptySys   = pure ()
  conv (VSys ((phi,a):bs)) (VSys bs') = case extractWith (===) phi bs' of
    Just (a', bs'') -> (a, VSys bs) `conv` (a', VSys bs'')
    Nothing         -> Left "Systems have different cofibrations!"
  conv _                   _          = Left "Systems have different size!" 

instance Conv a => Conv [a] where
  conv :: AtStage ([a] -> [a] -> Either String ())
  xs `conv` ys | length xs == length ys = zipWithM_ conv xs ys

instance (Conv a, Conv b) => Conv (a, b) where
  conv :: AtStage ((a, b) -> (a, b) -> Either String ())
  (a₀, b₀) `conv` (a₁, b₁) = (a₀ `conv` a₁) *> (b₀ `conv` b₁)

instance (Conv a, Conv b, Conv c) => Conv (a, b, c) where
  conv :: AtStage ((a, b, c) -> (a, b, c) -> Either String ())
  (a₀, b₀, c₀) `conv` (a₁, b₁, c₁) = ((a₀, b₀) `conv` (a₁, b₁)) *> (c₀ `conv` c₁)
