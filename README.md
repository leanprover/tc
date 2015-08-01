# Lean reference type-checker

This project will eventually be a reference type checker for the Lean theorem prover: a simple and small program that can type check fully elaborated Lean terms, exported in the following low-level format:

https://github.com/leanprover/lean/blob/master/doc/export_format.md

The main Lean repository can be found at:

https://github.com/leanprover/lean

The code follows the design of the Lean kernel closely, except can be made simpler since it does not need to integrate with parsing and elaboration, and because it need not be as performant.

### Todo

1. Setup cabal
2. Control module exports
3. Setup haddock for building documentation
4. Write many more tests
5. Write extensive tutorial-level comments (possibly in Literate Haskell)
