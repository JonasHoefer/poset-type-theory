module PosTT.Frontend.PreTerms where

import PosTT.Common (Name, SrcSpan)

-- | PreTerms
--
-- We expect these terms to be scoped checked, and free of shadowing.
-- The type includes `App` which can either be application of a fibrant or an interval variable.
-- Furthermore, it includes PApp and PLam which denote explicitly annotated path application and
-- abstraction.
data PTm where
  U :: SrcSpan -> PTy
  Var :: SrcSpan -> Name -> PTm
  Let :: SrcSpan -> Name -> PTm -> PTy -> PTm -> PTm
  -- ^ let x = u : A in v

  Pi :: SrcSpan -> Name -> PTy -> PTy -> PTy
  -- ^ (x : A) -> B
  Lam :: SrcSpan -> Name -> Maybe PTy -> PTm -> PTm
  App :: SrcSpan -> PTm -> PTm -> PTm

  Sigma :: SrcSpan -> Name -> PTy -> PTy -> PTy
  -- ^ (x : A) * B
  Pair :: SrcSpan -> PTm -> PTm -> PTm
  Pr1 :: SrcSpan -> PTm -> PTm
  Pr2 :: SrcSpan -> PTm -> PTm

  Path :: SrcSpan -> PTy -> PTm -> PTm -> PTm
  PLam :: SrcSpan -> Name -> PTm -> PTm -> PTm -> PTm
  -- ^ λᵢ.u from a₀ to a₁
  PApp :: SrcSpan -> PTm -> PTm -> PTm -> ITm -> PTm
  -- ^ u @ʳˢ v

  -- ^ Path A u v
  I :: SrcSpan -> PTy
  Zero :: SrcSpan -> ITm
  One :: SrcSpan -> ITm
  Inf :: SrcSpan -> ITm -> ITm -> ITm
  Sup :: SrcSpan -> ITm -> ITm -> ITm

  Coe :: SrcSpan -> ITm -> ITm -> Name -> PTy -> PTm
  -- ^ coeʳ⃗ˢ (i.A)
  HComp :: SrcSpan -> ITm -> ITm -> PTy -> PTm -> Sys (Name, PTm) -> PTm
  -- ^ hcompʳ⃗ˢ A a₀ [ψᵢ ↪ j.uᵢ]

  Ext :: SrcSpan -> PTy -> Sys (PTy, PTm, PTm) -> PTm
  -- ^ Ext A [ψᵢ ↪ (Bᵢ, eᵢ, pᵢ)]
  ExtElm :: SrcSpan -> PTm -> [PTm] -> PTm
  -- ^ ExtElem a [ψᵢ ↪ bᵢ]
  ExtFun :: SrcSpan -> PTm -> PTm
  -- ^ ExtFun [ψᵢ ↪ e] u


  Sum :: SrcSpan -> Name -> [Label] -> PTm
  -- ^ A (recursive) labeled sum type
  Con :: SrcSpan -> Name -> [PTm] -> PTm
  -- ^ A constructorfor a (recursive) labeled sum type with all its arguments
  Split :: SrcSpan -> Name -> [Branch] -> PTm


  HSum :: SrcSpan -> Name -> [HLabel] -> PTm
  HCon :: SrcSpan -> Name -> [PTm] -> PTm
deriving instance Show PTm

type PTy = PTm
type ITm = PTm

-- | A telescope of types
type Tel = [(SrcSpan, Name, PTy)]

-- | An alternative in a labeled sum, i.e.,
--   a named constructor and its arguments.
data Label = Label SrcSpan Name Tel deriving Show

-- | An alternative in a higher labeled sum, i.e.,
--   a named HIT constructor and its arguments.
data HLabel = HLabel SrcSpan Name Tel [Name] (Sys PTm) deriving Show


labelName :: Label -> Name
labelName (Label _ c _) = c

data Branch = Branch SrcSpan Name [Name] PTm deriving Show

branchConstructor :: Branch -> Name
branchConstructor (Branch _ c _ _) = c

data Sys a = Sys SrcSpan [([(ITm, ITm)], a)] deriving Show

data Decl = Decl SrcSpan Name PTm PTy

app :: SrcSpan -> PTm -> PTm -> PTm
app _  (Con ss c as) v = Con ss c (as ++ [v])
app ss u             v = App ss u v

srcSpan :: PTm -> SrcSpan
srcSpan = \case
  U ss               -> ss
  Var ss _           -> ss
  Let ss _ _ _ _     -> ss
  Pi ss _ _ _        -> ss
  Lam ss _ _ _       -> ss
  App ss _ _         -> ss
  Sigma ss _ _ _     -> ss
  Pair ss _ _        -> ss
  Pr1 ss _           -> ss
  Pr2 ss _           -> ss
  Path ss _ _ _      -> ss
  I ss               -> ss
  Zero ss            -> ss
  One ss             -> ss
  Inf ss _ _         -> ss
  Sup ss _ _         -> ss
  Coe ss _ _ _ _     -> ss
  HComp ss _ _ _ _ _ -> ss
  Ext  ss _ _        -> ss
  ExtElm ss _ _      -> ss
  ExtFun ss _        -> ss
  Sum ss _ _         -> ss
  Con ss _ _         -> ss
  Split ss _ _       -> ss