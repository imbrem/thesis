#import "/lib/prelude.typ": *
#show: part.with(title: "Type-Theoretic SSA")

#quote(block: true, attribution: "Donald Knuth")[
  Premature optimization is the root of all evil.
]

The goal of this chapter is to give a formal presentation of SSA
--  
fully specifying its _syntax_, _type theory_, and _semantics_.
Rather than do this all at once, 
we're instead going to "build up to" SSA
by studying a sequence of increasingly complex languages,
each of which embeds into the next.

In particular, we'll begin by introducing:

1. The language of simple arithmetic expressions, #larith,
   which we'll extend to:

2. The language of _effectful_ expressions, #lexpr,
   which we'll restrict to:

3. The language of _operations_, #lop
   -- a single effectful expression which depends on variables and constants.
   This will allow us to define

4. The language of _basic blocks_, #lbb,
   -- straight-line sequences of operations
   -- which we'll show _equivalent_ to
   the language of effectful expressions with _let-bindings_.
   By adding conditional branches, we can then recover

5. The language of _acyclic regions_, #lareg,
   -- single-entry, single-exit _acyclic_ 
   control-flow graphs of basic blocks
   -- which we'll show _equivalent_ to
   the language of effectful expressions with _case-expressions_

Finally, we'll drop the acyclicity restriction to get to our final type-theoretic presentation of SSA:

6. The language of _regions_, #lreg,
   -- single-entry, multiple-exit control-flow graphs of basic blocks
   -- which we'll show _equivalent_ to
   the language of effectful expressions with _iteration_

Our goal is to give a precise mathematical description of each of these languages
--
consequently, each language's section will follow a somewhat repetitive pattern,
where we specify:

- A _syntax_, which specifies how to tell whether a term is _grammatical_
  -- like "$x * (y + z)$"
  -- or nonsense
  -- like "$C++$".

- A _type system_, which consists of:

  - A collection of ways we can _interpret_ a given term
    (natural number, string, graph, tensor, neural network...) 
    -- that is, a set of _types_ $A, B, C$

  - A description of the _contexts_ in which we can interpret terms

  - A _typing relation_
    -- which tells us
    in which contexts a given term can be interpreted in a given way.

    Concretely: 
    we might be able to interpret $x + x$ as an integer in the context $x : ℤ$,
    or as a string in the context $x : #`str`$
    -- but $x + x$ doesn't make sense for $x : #`POBox`$.

Normally, a _type theory_ consists of a type system together with
an _equational theory_: 
a relation which tells us when two terms are "the same"  in a particular context
-- for example, we might have $x + y ≡ y + x$ in the context $x : ℤ, y : ℤ$,
but not in the context $x : #`str`, y : #`str`$.

This can let us reason about programs, but also _optimize_ them
-- for example, we might rewrite
#rwopt(
  $(x + 5) + (x + 5) + (x + 5)$,
  $lexp(y, x + 5, 3 · y)$
)

Since our main focus will be the study of compiler optimizations, 
we will hence generalize equationa theories to _refinement theories_:
where a refinement theory is
a relation which tells us that replacing a term $t$ with another term $t'$
is always sound, i.e., that $t'$ _refines_ $t$ -- written $t rfn t'$.

We can recover 
an equational theory by saying that $t$ and $t'$
are _equivalent_
--
written $t eqv t'$
--
whenever $t rfn t'$ and $t' rfn t$.
Likewise, every equational theory induces a refinement theory by
simply defining $(t rfn t') := (t eqv t')$.

As a concrete example,
let's assume that the result of $x slash 0$ is _implementation-defined_
-- and, in particular, may return a different result each time it's evaluated.

Then it's sound to rewrite
#rwopt(
  $(x slash y) + (x slash y)$,
  $lexp(z, x slash y, z + z)$
)
since, whether or not $y = 0$, 
every valid result for the original program 
is also a valid result for the rewritten program.

On the other hand, for $x, y : ℤ$, the rewrite
#rwbad(
  $lexp(z, x slash y, 2 · z)$,
  $(x slash y) + (x slash y)$
)
would be unsound, since every valid result for the left-hand side is _even_
(since it can be written $2 · z$ for some $z$)
but the right-hand side can be _odd_
-- for example, if $y = 0$, we could have the reduction sequence
#red-seq(
  $(x slash y) + (x slash y)$,
  $1 + (x slash y)$,
  $1 + 0$,
  $1$
)

Just like equations, refinements can be _context-dependent_ 
-- for example, depending on our semantics, we may have that
#rwopt(
  $lexp(z, x slash y, 2 · z)$,
  $(x slash y) + (x slash y)$
)
is a perfectly valid optimization for $x, y : ℝ$.

At this point, we've got a _theory_ for our programming language:

- A _syntax_, which sets the domain of discourse

- A _type theory_, 
  which tells us what rules we can use to reason about 
  sentences in our syntax

What we now need to confirm is whether this theory is a _good_ one 
-- that is, whether it captures our intuitions about how programs should behave.

To do this, we need to give our theory a _semantics_.
There are two primary approaches we might take:

- We can provide an _operational semantics_:
  a relation which specifies the behaviour of a program 
  by describing how it would be executed by an _abstract machine_.

  Our semantics is then _sound_ if 
  $t rfn t'$,
  implies that 
  valid execution of $t'$ is a valid execution of $t$.

  Alternatively,

- We can provide a _denotational semantics_:
  a mapping from well-formed terms in our syntax
  to mathematical objects.

  _Soundness_ 
  in this case means that every sentence which is true according to our type theory
  is true when interpreted as a statement about the semantics.

  For example, if we interpret programs like $x slash (y + z)$ 
  as functions from _valuations_ $ms("Var") → ℤ$
  to sets of possible results $cal(P)(ℤ)$,
  then we might say our type theory is _sound_ if, for all well-formed $t, t'$,
  $
  t rfn t' ==> ⟦t⟧ ⊆ ⟦t'⟧ #h(2em) text("(pointwise)")
  $

The standard approach for reasoning about SSA
--
e.g. in #todo[VELVVM, etc]
--
is operational.
One of the primary contributions of this thesis 
is to give a _compositional_ denotational semantics for SSA
--
that is, a denotational semantics in which the semantics of a
program as a whole is a function of the semantics of its parts.
In particular, this will be enabled by _categorical semantics_:
where types and contexts are intepreted as _objects_ in a _category_.

While the resulting semantics enables compositional reasoning about SSA programs,
it is also quite abstract
--
hence, to validate that it is in fact the "right" semantics, we'll show that:

- It is _complete_ with respect to our refinement theory:
  that is, $t rfn t'$ if and only if $⟦t⟧_cal(M) ≤ ⟦t'⟧_cal(M)$
  for every model $cal(M)$

- Our refinement theory is _sound_ with respect to a reasonable operational semantics
  --
  and hence our categorical semantics at least _abstracts_ the operational semantics.

Let's get started!

#include "s-expressions/main.typ"