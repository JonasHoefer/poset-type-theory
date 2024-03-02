# Poset Type Theory

Experimental Haskell implementation of a version of cubical type theory with a model in fibrant presheaves over finite, non-empty posets.


## Install

The project is built using [cabal][software/cabal].
To install the type checker and evaluator, clone the repository and run `cabal install --overwrite-policy=alway`.
This will install an executable called `postt` in `~/.cabal/bin/` (and potentially, remove old versions).


## Versions

- [ghc 9.4.8][software/ghc]
- [cabal 3.10.2.1][software/cabal]


[software/ghc]:
  https://www.haskell.org/ghc/
  "The Glasgow Haskell Compiler"

[software/cabal]:
  https://www.haskell.org/cabal/
  "Common Architecture for Building Applications and Libraries"