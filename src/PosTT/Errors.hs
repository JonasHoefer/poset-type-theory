module PosTT.Errors where

import PosTT.Terms

data ConvError = ConvErrorTm Tm Tm | ConvErrorString String