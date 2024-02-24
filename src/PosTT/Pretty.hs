module PosTT.Pretty where

import Data.String (IsString(..))

import Prettyprinter (Pretty(..), (<+>), defaultLayoutOptions, layoutPretty)
import Prettyprinter.Render.String (renderShowS)

import PosTT.Terms

--------------------------------------------------------------------------------
---- Pretty Printing

instance Pretty Tm where
  pretty = \case
    U            -> "U"
    Var x        -> pretty x
    -- Let d t ty s -> eval (EnvDef rho d t ty) s -- no ext name, right? The invariant is different: Free Names are in stage!

    -- Pi a b  -> VPi (eval rho a) (eval rho b)
    Lam t   -> "\\" <> pretty t
    App s t -> "(" <> pretty s <+> pretty t <> ")"

    Sigma a (Binder x b) -> "(" <> pretty x <+> ":" <+> pretty a <> ")" <+> "->" <+> pretty b
    Pair s t             -> "(" <> pretty s <> "," <+> pretty t <> ")"
    Pr1 t                -> pretty t <> ".1"
    Pr2 t                -> pretty t <> ".2"

    Path a s t   -> "Path" <+> pretty a <+> pretty s <+> pretty t
    PLam t _ _   -> "\\" <> pretty t
    PApp t _ _ r -> "(" <> pretty t <+> pretty r <> ")"

instance Pretty a => Pretty (Binder a) where
  pretty (Binder x a) = pretty x <> "." <+> pretty a

instance Pretty a => Pretty (IntBinder a) where
  pretty (IntBinder z t) = pretty z <> "." <+> pretty t

instance Pretty Name where
  pretty = fromString . unName

instance Pretty Gen where
  pretty = fromString . unGen

instance Pretty I where
  pretty = \case
    IVar i  -> pretty i
    Sup r s -> "(" <> pretty r <+> "\\/" <+> pretty s <> ")"
    Inf r s -> "(" <> pretty r <+> "/\\" <+> pretty s <> ")"
    I0      -> "0"
    I1      -> "1"

instance Show Tm where
  showsPrec _ = renderShowS . layoutPretty defaultLayoutOptions . pretty
