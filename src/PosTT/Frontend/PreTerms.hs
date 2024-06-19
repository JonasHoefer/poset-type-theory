module PosTT.Frontend.PreTerms where

import PosTT.Common (Name, Gen, SrcSpan)

-- | PreTerms
--
-- We expect these terms to be scoped checked, and free of shadowing.
-- The type includes `App` which can either be application of a fibrant or an interval variable.
-- Furthermore, it includes PApp and PLam which denote explicitly annotated path application and
-- abstraction.
data PTm where
  U :: SrcSpan -> PTy
  Var :: SrcSpan -> Name -> PTm
  -- | let x = u : A in v
  Let :: SrcSpan -> Name -> PTm -> PTy -> PTm -> PTm

  -- | (x : A) -> B
  Pi :: SrcSpan -> Name -> PTy -> PTy -> PTy
  Lam :: SrcSpan -> Name -> Maybe PTy -> PTm -> PTm
  App :: SrcSpan -> PTm -> PTm -> PTm

  -- | (x : A) * B
  Sigma :: SrcSpan -> Name -> PTy -> PTy -> PTy
  Pair :: SrcSpan -> PTm -> PTm -> PTm
  Pr1 :: SrcSpan -> PTm -> PTm
  Pr2 :: SrcSpan -> PTm -> PTm

  -- | Path (z.A) u v
  Path :: SrcSpan -> Name -> PTy -> PTm -> PTm -> PTm
  -- | λᵢ.u from a₀ to a₁
  PLam :: SrcSpan -> Name -> PTm -> PTm -> PTm -> PTm
  -- | u @ʳˢ v
  PApp :: SrcSpan -> PTm -> PTm -> PTm -> ITm -> PTm

  I :: SrcSpan -> PTy
  Zero :: SrcSpan -> ITm
  One :: SrcSpan -> ITm
  Inf :: SrcSpan -> ITm -> ITm -> ITm
  Sup :: SrcSpan -> ITm -> ITm -> ITm

  -- | coeʳ⃗ˢ (i.A)
  Coe :: SrcSpan -> ITm -> ITm -> Name -> PTy -> PTm
  -- | hcompʳ⃗ˢ A a₀ [ψᵢ ↪ j.uᵢ]
  HComp :: SrcSpan -> ITm -> ITm -> PTy -> PTm -> Sys (Name, PTm) -> PTm

  -- | Ext A [ψᵢ ↪ (Bᵢ, eᵢ, pᵢ)]
  Ext :: SrcSpan -> PTy -> Sys (PTy, PTm, PTm) -> PTm
  -- | ExtElem a [ψᵢ ↪ bᵢ]
  ExtElm :: SrcSpan -> PTm -> [PTm] -> PTm
  -- | ExtFun [ψᵢ ↪ e] u
  ExtFun :: SrcSpan -> PTm -> PTm

  -- | A (recursive) labeled sum type
  Sum :: SrcSpan -> Name -> [Label] -> PTm
  HSum :: SrcSpan -> Name -> [HLabel] -> PTm

  -- | A constructorfor a (recursive) labeled sum type or HIT with all its arguments
  Con :: SrcSpan -> Name -> [PTm] -> PTm
  Split :: SrcSpan -> Name -> [Branch] -> PTm

deriving instance Show PTm

type PTy = PTm
type ITm = PTm

-- | A telescope of types
type Tel = [(SrcSpan, Name, PTy)]

-- | An alternative in a labeled sum, i.e.,
--   a named constructor and its arguments.
--
-- > C (t : T)
data Label = Label SrcSpan Name Tel deriving Show

labelName :: Label -> Name
labelName (Label _ c _) = c

data Branch = Branch SrcSpan Name [Name] PTm deriving Show

branchConstructor :: Branch -> Name
branchConstructor (Branch _ c _ _) = c

-- | An alternative in a higher labeled sum, i.e.,
--   a named HIT constructor and its arguments.
--
-- > C (t : T) (i₁ … iₙ : I) [ φ ↪ u ]
data HLabel = HLabel SrcSpan Name Tel [Gen] (Sys PTm) deriving Show

data Sys a = Sys SrcSpan [([(ITm, ITm)], a)] deriving Show

data Decl = Decl SrcSpan Name PTm PTy | DeclLock SrcSpan [Name] | DeclUnlock SrcSpan [Name]

app :: SrcSpan -> PTm -> PTm -> PTm
app _  (Con ss c as)  v = Con ss c (as ++ [v])
app ss u              v = App ss u v

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
  Path ss _ _ _ _    -> ss
  PLam ss _ _ _ _    -> ss
  PApp ss _ _ _ _    -> ss
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
  HSum ss _ _        -> ss
