#import "/lib/prelude.typ": *

/*
Current status:
- Trying to figure out narrative
- Just going to start by copying + retyping material from _The Denotational Semantics of SSA_ -- can refine and reorder later
*/

/*
Basic structure for this file:
- What we want to do:
  - Give a formal presentation of type-theoretic SSA
    -- specifically, all the different IRs in the introduction
    - lambda-SSA
      - + scopes 
      - + expressions
    - lambda-iter -- by starting with lambda-expr and adding
      - +let-bindings (including destructure)
      - +case statements
      - +tail-controlled loops
- For each language, we want to:
  - Define the language:
    - Define what's _syntactically_ well-formed -- give a grammar
    - Define what's _semantically_ well-formed -- give a typing relation
      - We need to introduce the concept of a _type system_
      - We need to _justify_ the concept of a type system
        -- as concretely as possible, we'll abstract later!
      - We also need to come up with a good distinction between
        syntactic well-formedness and semantic well-formedness
        -- I "just know it when I see it" at this point
  - Now that we know what _has_ a meaning 
    (in Church semantics 
    -- the _syntax_ has a meaning in Curry semantics
    -- discuss, might help with the above questions)
    _what_ is that meaning
    - To figure out "what what means" we want to
      figure out _why_ we want to give programs a meaning
    - Reason #1: I want to reason about a program's _correctness_
      - Reason #1A: Once I provide all a program's arguments, I want to know what it's outputs are -- I don't care how we get them
        - This is _operational semantics_ -- big step, specifically
        - We might want a notion of _values_ separate from programs
          -- but we can also have programs in _normal form_
        - We also want to track _side-effects_
          - Something like printing is "in addition to" the value
          - But divergence means "no value" (or a garbage value -- but that's uglier)
          - Special forms of divergence: exception, trap, UB
          - And nondeterminism means _many_ values
          - So we probably want a big-step _relation_, and to return
            an effect along with the value
      - Reason #1B: I want to know how the program _runs_:
        - We can also have _small-step_ operational semantics, each step -- in a virtual machine
        - So we can count steps, and talk about complexity -- each small-step should correspond to O(1) work in the real machine
        - Likewise for space -- handles side-effects like memory more naturality
        - Divergence? We never reach a normal form!
        - Nondeterminism? We could reach many normal forms -- naturally handles nondeterministic divergence, too
        - More naturally handles _refinement_; can be more compositional
    - Reason #2: I want to compile a program
      - Reason #2A: I want to optimize my program -- getting another IR program which is faster/better/etc -- but is a refinement of the first
        - So I need a relation which tells me which programs are
        semantically equivalent/is a refinement
        - I could use _rules_ I can apply to determine when this
          relation holds
        - _Axiomatic semantics_ is: the semantics of a program is
          the set of programs it is equivalent to
        - The rules could also be _refinements_ -- program A has less behaviours than B
        - _Axiomatically_ -- this is a _partial order on programs_
      - Reason #2B: I want to compile my program to another language
        - I could map programs (in both languages!) to some mathematical object
        - Two programs are the same if they represent the same object
        - One program refines another if the two objects they map to are related somehow -- a _partial order_ on those objects, for example
    - So we're going to show, for each language, how to give all four kinds of semantics
    - And we're going to show that they're _all the same_
      - Small-step opsem ==> Big-step opsem [Finite]
      - Big--step opsem ==> Axiomatic semantics [Finite]
      - Axiomatic semantics ==> Denotational semantics [Finite]
      - Denotational semantics ==> Axiomatic semantics [Infinite]
      - Axiomatic semantics ==> Big-step opsem [Infinite??]
      - Big-step opsem ==> Small-step opsem [Infinite??]
    - The above is a big picture -- but we want to start with denotational \approx axiomatic -- this is _The Denotational Semantics of SSA_ and we want to stick to that for now
    - But we want the connection to operational semantics -- and to introduce _simulation_ -- later, if time permits
      - It makes our ideas a lot more applicable
      - It will help us connect things to WASM and stack machines
      - It makes things a lot easier to explain
  - What's natural for SSA:
    - Grammar
    - Type system
    - Op-sem (small) -- we can implement scopes with a shadowing-stack
      - For RTL -- we don't need the stack!
      - Likewise -- if all variables are fresh -- the SSA property -- no stack needed
      - To compare, we need to introduce _simulation_/_bisimulation_
    - Axiomatic-semantics
      - We want to _justify_ these by operational semantics
      - But... we can also justify it by denotational semantics
        - Level 1: to make it easier to prove opsem
        - Level 2: the rules on their own are _complete_ for densem -- and allow other, non-operational models
    - What's natural for _expressions_
      - Grammar
      - Type system
      - Den-sem (as algebraic expressions!)
      - Axiomatic-semantics
        - We want to _justify_ these by denotational semantics
        - Turns out they're _equivalent_ (soundness + completeness)
      - Operational-semantics
        - How to _evaulate_ expressions


  - The plan:
    - Figure out what we're going to do?
      - Expressions -- build up, then SSA?
        - Pros:
          - Build up categorical semantics for each kind of expression:
            - #1: Cartesian (app + tuple)
            - #2: Freyd (let-bindings -- start with Cartesian)
            - #3: Distributive (case statements)
            - #4: Elgot (loops)
      - SSA directly
        - Still need rules for expressions -- so it's embedded
        - Then we need to build up expressions
        - Or we start with just single-op SSA 
          -- versus SSA parametrized by expression language

*/

/*

Start of _part_: high level overview of each chapter/section in this part:

*/

We now want to give a formal account of the type-theoretic presentation of SSA we sketched in the introduction.
/*
First attempt:
- Need to make it flow better, 
  but at least it works as a TODO list for what we need to write
*/
In particular, for each of the intermediate representations we wish to study, we need to provide:

- A _grammar_, to enumerate the syntactically well-formed terms in our language -- we've already provided this in the introduction for most of our intermediate representations.

- A _typing relation_, which allows us to determine whether a program is _semantically_ well-formed.

In particular, we'll need a _type system_ to construct our typing relation with respect to 
-- later, we'll be able to relate different intermediate representations 
by giving them different typing relations over
the same type system.
/*
Potential structure/material for next attempt:
- We've _already_ provided a grammar
- These show us which terms are _syntactically_ well-formed
  -- so we don't need to bother assigning a meaning to nonsense
  terms like `+=<<j =^i3` or `C++`
- But this doesn't take into account the _semantics_ of terms:
  - Level 1: variable scoping
    - This _can_ be dealt with at the grammar level via de-Bruijn indices...
  - Level 2: _type correctness_/_well-typedness_
    - Much harder to deal with at the grammar level (possible in some cases -- e.g. production-per-type)
    - Give a good example _why_ we'd want to do this
    - We don't necessarily lose generality -- "just scoping" is just a _unityped_ system
      - (But in our system, we will, since we distinguish tuple types from non-tuple types -- discuss other options later!)
*/

/*
First pass at structure -- *can change*

- _Expressions_, building up to λ-iter

  - Start with: base types + n-inputs --> _expression calculus_

    - QUESTION: where do we add let-bindings?

      - Before _any_ semantics? 
      
        Probably not -- makes big-step a _bit_ more complex!
  
    - QUESTION: where do we put the grammar of _operations_?

      - Probably while _factoring_ the big-step semantics!

      - Similarly -- want grammar of _values_ -- variables + constants!

      - Separate constants nice for grammar of operations
        (or are they?)

        --

        _But_ 0-ary operations are just constants, too!

    - "Small-step semantics": evaluate the functions _at constants_
      --
      works naturally with partiality/divergence/nondeterminism 
      -- we can also study:
      
      - more general side effects:
        - special divergence: exceptions, traps, UB
        - add a _log_
        - add a _store_
        - combine effects w/ the product
        - more complex structures allow us to model concurrency, etc.

      - complexity -- count the steps!

      - observational equivalence
        --
        often, we "just" want to evaluate the function,
        not caring _how_ it's computed
        --
        doing this naively gives us a:

    - "Big-step semantics": "just" evaluate the functions
      Not too difficult to study:
      - partiality/divergence
      - nondeterminism
      - _slightly_ more annoying: 
        "special forms" of divergence: exceptions, traps, UB

    - Issues: _not compositional_!

    - "Axiomatic semantics":
      - congruence + small-step semantics
      - Interesting, right? Nothing else!
      - Can also add _known properties_ from big-step/small-step
        -- addition is assoc + comm, etc.
        -- but dangerous in the presence of side-effects!

        How can we know when reasoning in the presence of side-effects
        is _safe_?

        We need:
        - A _semantic_ justification
        - A _way_ to identify side-effectful vs. pure expressions

    - Think more about _side effects_ -- "denotational semantics":
      basically the big-step semantics but in a _monad_
      --
      so we can reason about partiality in a more principled way.

      - _Fixes an evaluation order_ -- we choose left-to-right

        - No evaluation order _iff_ our monad is _commutative_

      - So obviously "not every program can be written!"
        --
        quite limited, we'll _build up_ this intuition into
        _completeness_ later

      - We want to give semantics to "a whole arrow"
        --
        maybe point to Haskell's "Arrow" typeclass
        --
        which might not be just a function A -> M B,
        for various reasons:

        - Function properties -- that is, functions which _respect structure_
          (
          
          rewrite this backwards 
          -- we (usually!) *need* to fix a structure to talk about properties!
          
          but this opens the door to Fancy Types -- lots of structures on the
          same set!

          what do we need?

          - property on products from property on components!

          - property on identity!

          - property on composition!

          )

          - Continuous/differentiable/monotone/measurable functions
            -- 
            _not_ in general a submonad, but might be
            closed under composition + Cartesian products

          - Functions constructible from a given set of generators:

            - Polynomials

            - Terms in an SMT theory -- e.g. QF-UFLIA

            - Elementary functions

            - Primitive-recursive functions

            - Neural networks
              --
              including in a specific framework, e.g.
              ONNX and StableHLO

          - Complexity:

            - Functions in a given computational complexity class
            -- e.g. polynomial-time computable functions

              --

              of course, this depends on what we mean by "polynomial"
              given the signature!

            - Computable functions

            - Functions at a point in the arithmetical hierarchy

            - Functions at a point in the analytical hierarchy

          - Why can't we just use monads?

            - If we already fix, for every set ⟦A⟧, the appropriate structure:

              - Topology / manifold structure; measure

              - Order structure

              - Complexity structure

              Then can do denotational semantics w/ monads
              + proof _about_ denotational semantics

            - But we might want to handle, for computational complexity, e.g.:

              - Parameter with "size" == bits = log(# of states)
                (standard!)

              - Parameter with "size" == "# of states"
                (e.g. number of items for knapsack problem)

            - Otherwise, possible but a bit more unwieldy:

              - Fix a set ⟦A⟧

              - Fix a _structure_ Struct(A) on ⟦A⟧

                -- 
                
                prove function respects Struct(A);
                usually via composition + identity + products

              - Can have different structures but same ⟦A⟧

              Would like a _framework_ for defining things like:

              - What _is_ a Struct(A)?

              - f ∈ Respects(⟦A⟧, Struct(A), ⟦B⟧, Struct(B))?

        - Event handling:

          - Event A gives one event B -- functional!

          - Event A gives 0..N events B -- functional to option/list/etc

          - 0..N events A give one event B?

            - Not natural to write as pure functions

            - But very natural to write as expressions -- pipes!
              ```
              cat | grep "foo" | sort | uniq -c
              ```
              becomes
              ```
              (uniq "-c" (sort (grep "foo" cat)))
              ```
              
              Multiple arguments becomes _redirection_:
              ```
              grep "foo" <(program1) <(program2)
              ```
              becomes
              ```
              (grep "foo" program1 program2)
              ```

    - "Categorical semantics": 
      in a CC: basically the big-step semantics

      Works the same as above -- handles cases like:

      - fixed generators

      - continuous/differentiable/monotone/measurable functions

      - complexity; computational and otherwise!

      - "timeless" models of piping -- forward to next section
        for the proof via Freyd categories

      The "structure" thing we discussed is a
      _concretely cartesian category_!

      Handles *some* side-effects: partiality, etc.

      What about nondeterminism?
      
      We can use Rel -- but we get our first Weird Model (TM).

      But doesn't handle:
      - _non-discardable_ side-effects (give counterexample!)
      - _non-duplicable_ side-effects (give counterexample!)
      - _non-commutative_ side-effects (give counterexample!)

      Note: hard to write without "let" 
      -- 
      but for example shows with (+)!

    - Option 1: _generalize the proof strategy_:

      - Introduce _Freyd categories_; string diagrams
        (informally done before via Unix piping)

      - 

    - Option 1: _categorical monads_.

      This works -- basically same as above!

      Now have Deep Generality (TM)

      _But_...

    - Option 2: _Freyd categories_.


  - Same type system + let-bindings --> _cartesian expression calculus_
  
  - Add: tuples + destructures --> _Freyd expression calculus_
    
    - NOTE: could _also_:

      - Add multiple-returns _instead_ for symmetry w/ multiple-inputs
        --
        _but_ we want to make it easy to reason about tuples.

        - Prior art: MLIR

      - _Remove_ multiple inputs for symmetry w/ single-output
        --
        _but_, pedagogically, multiple inputs is easier since:
        - Tuples can be viewed as a special operator w/ multiple inputs
        - The grammar for operations can be simple: just `op(v1,...,vn)`
          for `v ::= x | const` 
          -- otherwise we'd need to allow nested tuples to get parity.

          We still _do_ want to allow nested tuples _in general_ --
          but the variant without nested tuples is "closer to assembly"

        - Prior art: functional programming convention, 
          mathematical convention `f(a, b)`

      - We'll want to

        - _Mention_ these

        - Later show how our framework allows us to do proofs of equivalence

        - A particularly important equivalence: _named_ tuples and _newtypes_

      - Prior art for us:

        - These are _literally_ S-expressions at first

          --

          but the n-ary kind vs. the binary kind!

        - Tuple is just quote

        - QUESTION:
          
          Let is "sort of define" -- likewise what is "destructure"?
          
          [Build Your Own Lisp](https://www.buildyourownlisp.com/) 
          was a _long_ time ago.

  - 

- _SSA_, parametrized by expression language
  -- we'll just always do SSA + scopes
*/

#pagebreak()

= S-Expressions

#include "s-expressions/main.typ"

#pagebreak()

= Sequencing

#pagebreak()

= Branching

#pagebreak()

= Loops

#pagebreak()

= Unstructured Control-Flow

#pagebreak()