#import "/lib/prelude.typ": *
#show: chapter.with(title: "Introduction")

/* Take 1: */

The fundamental question of this thesis is:
_what does a computer program mean?_

We can approach this in two ways: from the bottom-up or the top-down.

The former tends to be more natural for computer scientists.

A computer is a machine for following instructions
--
a program is a sequence of instructions for it to follow.

In particular, a computer has an _instruction set_
--
a finite set of _operations_ which it can perform,
which read from and write to its _state_
--
that is, the current state of the registers, program counters,
memory, interrupts, and all the other bits which make a modern CPU tick.

Which is a _lot_.

/* Take 2: */

This thesis is about the _denotational semantics_ of the _static single assignment_ -- or _SSA_ -- compiler _intermediate representation_ -- or _IR_. 

I want to start by justifying this choice of topic.

- _Why_ do we need a semantics for a _compiler IR_?

  Because high-level languages have too many features to effectively study _or_ to lower in one pass.

  Because low-level languages are designed to be _executed_ efficiently -- making them difficult both to reason about or to lower in one pass.

- _Why_ should we use _SSA_ as our compiler IR?

  Practically: most modern compilers use it.

  Theoretically: it's right at the intersection of functional and imperative programming
  --
  letting us use it as a _thin waist_ to develop the _isomorphism_
  between the two.

- _Why_ should we give a _denotational_ semantics?

  Because we want to reason about programs _algebraically_
  --
  and to do so in a _compositional_ manner.


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
