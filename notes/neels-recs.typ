= Neel's Recs

== MVP Thesis

- We want to do more complex transforms

  - Instead of syntactic values; I want to use an effect system for "value-like things" involving variables

    - Two special cases:

      - Constants -- "values"

      - Variables -- "renaming"

      - What about "z ==> x + y"? -- _algebra_

      - Distinguish between _pure_ and _impure_ expressions
        -- work with a _lattice_ of effects because same difficulty

        - Sets up branch language as effect-preserving; can use this in acyclic chapter if written

    - Narrative idea: CONTRIBUTION (#1): what _is_ imperative programming

      - Set up equational theory

      - I want to give a denotational semantics -- the standard way is Moggi-style with monads

        - Pure things correspond to `'a -> 'b`

        - Everything else is `'a -> m 'b` -- effects become _submonads_ of `m`

        - Introduce the Elgot monad here as an Elgot category -- gives intuition

      - We want: soundness + completeness. The above gives soundness -- for completeness, we need some kind of free model.

        - Approach #1: free model of imperative computation -- interaction trees, study more (conjecture: _rational_ interaction trees are initial too)

        - Approach #2: _syntactic_ model of imperative computation -- (!NEW!) -- this needs a _categorical_ semantics; strict generalization

        - Introduce categorical semantics and background

        - Interaction trees: take signature of effects, construct free monad

    - Narrative idea: CONTRIBUTION (#2): what _is_ SSA

      - Here's an inductive presentation of SSA -- _parametrized by an expression language_

        - Here we can define _operations_: two dialects: SSA with iter and SSA with operations

        - Here's how you go back and forth with the regular presentation

      - Here's a type system for SSA

        - LATER: we'll give a type system for the regular presentation and show it's preserved by above

      - We can show how to:

        - SSA[op] injects into SSA[iter]; all of below are on SSA[iter]

        - Compile SSA[op] to SSA[iter]

        - Compile SSA[iter] to lambda iter

        - Compile lambda iter to SSA[op] -- all diagrams commute

        - Compile SSA to categories -- all diagrams still commute

      - Conclusion: lambda iter is imperative programming iff SSA is imperative programming

         "Consilience"

    - CONTRIBUTION (#3): interesting models

== Extension 0

- Simple type system for regular SSA; proof of equivalence

- ^ this type system works for RTL as well!

== Extension 1

- Substructural lambda iter

- Substructural SSA

== Extension 2

- Study RTL itself, lowering RTL to SSA

- Study stack machines ==> WASM ("WASM is imperative programming")
