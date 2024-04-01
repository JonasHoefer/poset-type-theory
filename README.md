# Poset Type Theory

Experimental Haskell implementation of a version of cubical type theory with a model in presheaves over finite, non-empty posets.
Some additional information can be found in the file located in [`doc`][path/doc], a PDF version of which can be found [here][doc].


## Setup

The project is built using [cabal][software/cabal].
To install the type checker and evaluator, clone the repository and run `cabal install --overwrite-policy=always`.
This will install an executable called `postt` in `~/.cabal/bin/` (and potentially remove old versions).


## Usage

To see all options use `postt --help`.
To type check all definitions in a file, and evaluate the last one use `postt eval <path>`.
To start a read-eval-print-loop (repl) use `postt repl`.
In the repl, use `:help` to see all available commands.

## References

This implementation is inspired by [cctt][software/cctt] by András Kovács and [cubicaltt][software/cubicaltt] by Cyril Cohen, Thierry Coquand, Simon Huber, and Anders Mörtberg.


## Versions

- [ghc 9.4.8][software/ghc]
- [cabal 3.10.2.1][software/cabal]


[doc]:
  https://jonashoefer.github.io/poset-type-theory/poset.pdf
  "Documentation PDF"

[path/doc]:
  https://github.com/JonasHoefer/poset-type-theory/tree/main/doc
  "Poset Type Theory — Documentation"

[software/ghc]:
  https://www.haskell.org/ghc/
  "The Glasgow Haskell Compiler"

[software/cabal]:
  https://www.haskell.org/cabal/
  "Common Architecture for Building Applications and Libraries"

[software/cctt]:
  https://github.com/AndrasKovacs/cctt/
  "cctt —  high-performance cubical evaluation"

[software/cubicaltt]:
  https://github.com/mortberg/cubicaltt/
  "cubicaltt — Experimental implementation of Cubical Type Theory"
