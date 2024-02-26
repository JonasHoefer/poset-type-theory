module PosTT.Conversion (conv) where

import Control.Monad (zipWithM_, unless)
import Control.Monad.Except (throwError)

import PosTT.Common
import PosTT.Poset
import PosTT.Quotation
import PosTT.Errors
import PosTT.Eval
import PosTT.Terms
import PosTT.Values


--------------------------------------------------------------------------------
---- Conversion Checking

convPi :: AtStage (Val -> Val -> Either ConvError ())
u `convPi` v = freshFibVar (\x -> (u `doApp` x) `conv` (v `doApp` x))

convSigma :: AtStage (Val -> Val -> Either ConvError ())
u `convSigma` v = (doPr1 u, doPr2 u) `conv` (doPr1 v, doPr2 v)

convPath :: AtStage (Val -> Val -> Val -> Val -> Either ConvError ())
convPath a₀ a₁ u v = freshIntVar (\i -> doPApp u a₀ a₁ i `conv` doPApp v a₀ a₁ i)

convExt :: AtStage (VSys Val -> Val -> Val -> Either ConvError ())
convExt ws u v = doExtFun ws u `conv` doExtFun ws v -- TODO: is this correct?

instance Conv Val where
  conv :: AtStage (Val -> Val -> Either ConvError ())
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

    (u, v) -> Left $ ConvErrorTm (readBack u) (readBack v)

instance Conv Closure where
  conv :: AtStage (Closure -> Closure -> Either ConvError ())
  cl₀ `conv ` cl₁ = freshFibVar (\x -> (cl₀ $$ x) `conv` (cl₁ $$ x))

instance Conv TrIntClosure where
  conv :: AtStage (TrIntClosure -> TrIntClosure -> Either ConvError ())
  cl₀ `conv ` cl₁ = freshIntVar (\x -> (cl₀ $$ x) `conv` (cl₁ $$ x))

instance Conv TrNeuIntClosure where
  conv :: AtStage (TrNeuIntClosure -> TrNeuIntClosure -> Either ConvError ())
  cl₀ `conv ` cl₁ = freshIntVar (\x -> (cl₀ $$ x) `conv` (cl₁ $$ x))

instance Conv Neu where
  conv :: AtStage (Neu -> Neu -> Either ConvError ())
  conv = curry $ \case
    (NVar x₀               , NVar x₁               ) | x₀ == x₁ -> pure ()
    (NApp k₀ v₀            , NApp k₁ v₁            ) -> (k₀, v₀) `conv` (k₁, v₁)
    (NPr1 k₀               , NPr1 k₁               ) -> k₀ `conv` k₁
    (NPr2 k₀               , NPr2 k₁               ) -> k₀ `conv` k₁
    (NPApp v₀ _ _ r₀       , NPApp v₁ _ _ r₁       ) -> (v₀ `conv` v₁) *> (r₀ `conv` r₁)
    (NCoePartial r₀ s₀ c₀  , NCoePartial r₁ s₁ c₁  ) -> (r₀, s₀, c₀) `conv` (r₁, s₁, c₁)
    (NHComp r₀ s₀ k₀ u₀ tb₀, NHComp r₁ s₁ k₁ u₁ tb₁) -> (r₀, s₀, k₀, u₀, tb₀) `conv` (r₁, s₁, k₁, u₁, tb₁)
    -- TODO: NHCompSum :: VI -> VI -> VTy -> [VLabel] -> Neu -> VSys IntClosure -> Neu
    (NExtFun ws₀ k₀        , NExtFun ws₁ k₁        ) -> (ws₀, k₀) `conv` (ws₁, k₁)
    (NSplit f₀ _ k₀        , NSplit f₁ _ k₁        ) -> (f₀, k₀) `conv` (f₁, k₁)
    (k₀                    , k₁                    ) -> Left $ ConvErrorTm (readBack k₀) (readBack k₁)

instance Conv a => Conv (VSys a) where
  conv :: Conv a => AtStage (VSys a -> VSys a -> Either ConvError ())
  conv EmptySys            EmptySys   = pure ()
  conv (VSys ((phi,a):bs)) (VSys bs') = case extractWith (===) phi bs' of
    Just (a', bs'') -> (a, VSys bs) `conv` (a', VSys bs'')
    Nothing         -> Left $ ConvErrorString "Systems have different cofibrations!"
  conv _                   _          = Left $ ConvErrorString "Systems have different size!" 


---- plumbing instances

instance Conv a => Conv [a] where
  conv :: AtStage ([a] -> [a] -> Either ConvError ())
  xs `conv` ys | length xs == length ys = zipWithM_ conv xs ys

instance (Conv a, Conv b) => Conv (a, b) where
  conv :: AtStage ((a, b) -> (a, b) -> Either ConvError ())
  (a₀, b₀) `conv` (a₁, b₁) = (a₀ `conv` a₁) *> (b₀ `conv` b₁)

instance (Conv a, Conv b, Conv c) => Conv (a, b, c) where
  conv :: AtStage ((a, b, c) -> (a, b, c) -> Either ConvError ())
  (a₀, b₀, c₀) `conv` (a₁, b₁, c₁) = ((a₀, b₀) `conv` (a₁, b₁)) *> (c₀ `conv` c₁)

instance (Conv a, Conv b, Conv c, Conv d) => Conv (a, b, c, d) where
  conv :: AtStage ((a, b, c, d) -> (a, b, c, d) -> Either ConvError ())
  (a₀, b₀, c₀, d₀) `conv` (a₁, b₁, c₁, d₁) = 
    ((a₀, b₀, c₀) `conv` (a₁, b₁, c₁)) *> (d₀ `conv` d₁)

instance (Conv a, Conv b, Conv c, Conv d, Conv e) => Conv (a, b, c, d, e) where
  conv :: AtStage ((a, b, c, d, e) -> (a, b, c, d, e) -> Either ConvError ())
  (a₀, b₀, c₀, d₀, e₀) `conv` (a₁, b₁, c₁, d₁, e₁) = 
    ((a₀, b₀, c₀, d₀) `conv` (a₁, b₁, c₁, d₁)) *> (e₀ `conv` e₁)
