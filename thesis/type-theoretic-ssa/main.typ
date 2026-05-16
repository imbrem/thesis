#import "/lib/prelude.typ": *
#show: part

The goal of this thesis is to study the formal semantics of SSA
--
rather than do this "all at once,"
we will instead take a page from the "nanopass" school of compiler development
and study various intermediate languages $L$,
along with the _relationships_ between them.

That means that the first few chapters of this thesis are going to be a bit repetitive: 
for each language $L$ that we introduce, 
after we've given some informal intuition and examples
and situated it in our hierarchy of intermediate representations,
we're going to need to give a formal description of the language 
so that we can make precise and prove our claims.

Usually, this means a variant of the following narrative:

- We give $L$ a formal syntax
  -- usually parametrized by abstract sets of operations and constants

- We'll then often formalize $L$'s "expected" behaviour by 
  equipping it with a simple _operational semantics_
  --
  typically, we will "build up" to a full semantics for $L$,
  by starting with a simple rewriting-based semantics and then
  adding features like _state_ and _nondeterminism_ in stages. 

- Then, we define _type theory_ for $L$, consisting of:

  - A _type system_
    -- which defines the types a term can have 
    and the contexts in which they are interpreted.
    Usually, this will be parametrized by an abstract set of _base types_.

    Often, we will study many different languages 
    using the same type system.

  - A _typing relation_
    -- this typically consists of _typing rules_
    which tell us which terms are well-typed in a given context.

  - An _equational theory_ 
    -- this gives us a notion of which terms may be considered _equivalent_
    within a given context

At this point, we've got a formal specification for a programming language:

- How to tell whether a term is _grammatical_
  -- like "$x * (y + z)$"
  -- or nonsense
  -- like "$C++$"

- A collection of ways we can _interpret_ a given term
  (natural number, string, graph, tensor, neural network...) 
  -- that is, a set of _types_ $A, B, C$

- A description of the _contexts_ in which we can interpret term
  -- and a relation which tells us
  in which contexts a given term can be interpreted in a given way.

  Concretely: 
  we might be able to interpret $x + x$ as an integer in the context $x : ℤ$,
  or as a string in the context $x : #`str`$
  -- but $x + x$ doesn't make sense for $x : #`POBox`$.

- An _operational semantics_ which describes an _abstract machine_
  and tells us how to _execute_ our programs on it

- An _equational theory_ which tells us when two terms are "the same" 
  in a particular context
  -- for example, we might have $x + y ≡ y + x$ in the context $x : ℤ, y : ℤ$,
  but not in the context $x : #`str`, y : #`str`$.

  This can let us reason about programs, but also _optimize_ them
  -- for example, we might rewrite
  #rwopt(
    $(x + 5, x + 5, x + 5)$,
    $lexp(y, x + 5, 3 * y)$
  )

Once we _have_ such a specification, however, the question remains as to whether it's any _good_:

- How do we know our equational theory is _correct_
  -- especially in the presence of subtle _potential_ "gotchas" like
  the following optimization, which introduces UB _if_ `n == 0` is possible:
  #rwopt(
    ```cpp
    for(int i = 0; i < n; i++) {
      int t = k / n;
      acc += t * arr[i];
    }
    ```,
    ```cpp
    int t = k / n;
    for(int i = 0; i < n; i++) {
      acc += t * arr[i];
    }
    ```
  )

- 

  In fact 
  -- how do we even _define_ two programs to be equivalent,
  in the presence of side-effects?

#todo[
  denotational semantics -- do we pull the operational semantics _down_? 
  
  do we even want it at all -- 
  - it's not part of the MVP...
  - but it really helps justify our denotational semantics as correct
    -- otherwise completeness seems particularly abstract
]

#pagebreak()

= S-Expressions

#todo[This include should shift heading levels down by 1]

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