# Lean reference type-checker

This project will eventually be a reference type checker for the Lean theorem prover: a simple and small program that can type check fully elaborated Lean terms, exported in the following low-level format:

    https://github.com/leanprover/lean/blob/master/doc/export_format.md

The main Lean repository can be found at:

    https://github.com/leanprover/lean

The code follows the design of the Lean kernel closely, except can be made simpler since it does not need to integrate with parsing and elaboration, and because it need not be as performant.

### Todo

1. Start using a mature test framework (HTF)
2. Either write a battery of tests, or support a Lua interface so the existing tests for Lean can run on this project.
3. Setup cabal
4. Add support for inductive types
5. Add support for quotients
6. Write extensive tutorial-level comments in Literate Haskell
7. Parse the export files
8. Optimize until performance is adequate
