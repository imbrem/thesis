#import "/lib/prelude.typ": *
#show: chapter

= Evaluating Arithmetic Expressions

#todo[
  Can pull this bit up into the intro, replacing the old text?
]

#todo[
  "a traditional pattern" ==> "the traditional pattern of operational semantics"

  Our contributions:

  - Denotational instead
    (complete w.r.t. operational -- need to prove!)

  - Completeness of equational theory w.r.t. denotational semantics

  - Treatment of effects

  - _Refinement_ theory
    -- completeness of _refinement_ w.r.t. denotational semantics
]

#todo[
  Think about rewriting the below without any operational semantics at all
  --
  explain the shared bit of the pattern as
  "most/many/the first few of the chapters start out..."

  -- "the first few" is a decent idea, 
  since _later_ we introduce effects, refinement, and friends

  Then the typical thing is: 
  - opsem 
  - progress&preservation w.r.t. typing relation
  - soundness w.r.t. _observational equivalence_

  great people prove _completeness_/_abstraction_/_full abstraction_ 
  in this world

  What we do instead is:

  - densem
  - soundness w.r.t. densem
  - _completeness_ w.r.t. densem
  - but opsem is subsumed by densem via interaction trees and friends!

  Or alternatively -- follow embedded todos?
]

Much of this thesis consists of variations on 
a traditional pattern in the PL literature:

- We introduce a language $L$, 
  along with some informal intuition and motivation

- We give $L$ a formal syntax
  -- usually parametrized by abstract sets of operations and constants

- We then formalize $L$'s "expected" behaviour by 
  equipping it with a simple _operational semantics_
  #todo[cut below?]
  --
  typically, we will "build up" to a full semantics for $L$,
  starting with a simple rewriting-based semantics and then
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

    #todo[pull this down? or leave here]
    We usually then want to prove _progress_
    -- that is, 
    that every step in our operational semantics preserves well-typedness.
    
  - An _equational theory_ 
    -- this gives us a notion of which terms may be considered _equivalent_
    within a given context

    #todo[
      can pull this down 
      -- "we then want to prove soundness, but this is _hard_ since observational equivalence is hard 
      -- need "equivalent in every context" and that is pain"
    
      we _care_ about equivalence because we're writing a _compiler_
    ]
    We usually then want to prove _soundness_ 
    -- that is, programs which our equational theory identifies as equivalent
    are "indistinguishable" according to some notion of _observational equivalence_.

#todo[
  denotational semantics -- do we pull the operational semantics _down_? 
  
  do we even want it at all -- 
  - it's not part of the MVP...
  - but it really helps justify our denotational semantics as correct
    -- otherwise completeness seems particularly abstract
]

We'll start by giving a formal account of the simplest practical language
-- that of _first-order_ arithmetic expressions, 
like $x + y$ and $a + (5 · b) + sin(3)$.

Rather than complicate our language by introducing 
binary operators (like $x + y$),
unary operators (like $-x$),
and $n$-ary function applications (like $f(x, y, z)$),
we can instead normalize everything to _S-expressions_ 
-- or _sexprs_ -- 
of the form $sexp(f, e_1, ..., e_n)$.
We can then uniformly write:

- binary operations like $x + y$ as binary sexprs $sexp(sadd, x, y)$,

- unary operations $-x$ as unary sexprs $sexp(sneg, x)$,

- function appplications $f(x, y, z)$ as $n$-ary sexprs $sexp(f, x, y, z)$.

In particular, the _operator_ $f$ always comes first,
and there is no order-of-operations -- all bracketing is explicit.
//
Restricting ourselves to _first-order_ sexprs means that 
we always require operators $f$ to be atomic symbols drawn from a fixed set $ops$
--
in particular, we don't support _partial application_, 
like $sexp(sexp(ms("add"), 2), 3)$,
since that would require $f = sexp(ms("add"), 2)$ to be a compound expression.

Formally, we define our _syntax_ as follows:

#definition("First-order S-expressions")[
  fixing
  - a set of _variables_ $x ∈ vars$
  - a set of _operations_ $f ∈ ops$
  - a set of _constants_ $c ∈ vals$
  we define the set of _first-order S-expressions_
  $e ∈ sexp1(ops, vars: vars)$ 
  to be given by the grammar

  $
    e ::= x | c | sexp(f, e^*)
  $
]

We say a sexpr is _closed_ if it contains no free variables
--
otherwise, it is _open_
-- 
where the _free variables_ $fv(e)$ of a sexpr $e$ are defined as follows:

#def-set(
  $fv(x) = {x}$,
  $fv(c) = {}$,
  $fv(sexp(f, e_1, ..., e_n)) = ⋃_i fv(e_i)$
)

We'll write the set of closed sexprs as $csexp1(ops)$.

It's easy enough, in the language of simple arithmetic,
to define what a closed sexpr "means",
since we can just _evaluate_ it to find out.

For example, we might have been taught to evaluate expressions from the
"inside out", like so:
$
  sexp(sadd, 5, sexp(smul, 3, 7)) = sexp(sadd, 5, 21) = 26
$

We can formalize this intuition in terms of a _small-step operational semantics_:
given, for each operation $f ∈ ops$, a (partial) function $evop(f) : V^* ssto V$
telling us what value it returns when called with arguments $c_1, ..., c_n$,
we may define a _reduction relation_ $e ssto e'$ on sexprs
as follows:

#let step = rule(
  label: "step",
  [$evop(f)(c_1, ..., c_n) = c$],
  [$sexp(f, c_1, ..., c_n) ssto c$]
)

#let arg = rule(
  label: "arg",
  [$c_1,...,c_n ∈ vals$],
  [$e_1 ssto e'_1$],
  [$sexp(f, c_1, ..., c_n, e_1, ..., e_m) ssto sexp(f, c_1, ..., c_n, e'_1, ..., e_m)$]
)

$
  \
  #rule-set(
    prooftree(step),
    prooftree(arg),
  )
  \
$

Partiality here means that we don't need to assign a meaning 
to ill-defined expressions like $sexp(sdiv, 1, 0)$ or $sexp(sadd)$
(when forced, $0$ is a decent choice for both of these)
-- we can simply leave them as undefined.

Notice that we've fixed the _evaluation order_ of sexprs to be left-to-right
-- that is; 
we have to finish evaluating all terms to the _left_ of a given term
before we can get to reducing it.

We say a term $e$ _evaluates_ to a constant $c$ 
-- written $e bsto c$ --
if there exists a finite sequence of reductions
$
  e ssto e_1 ssto ... ssto e_n ssto c
$
i.e., if $e sred c$ -- where $R^*$ denotes the 
_reflexive, transitive closure_ of a relation $R$.

We call a relation $e bsto c$ a _big-step operational semantics_
--
as our original intuition for evaluation would suggest,
$c$ is a pretty good candidate for the "meaning" of a program $e bsto c$.

In particular, we may define a partial function $stev(e)$ on closed terms by induction as follows:

#def-set(
  $stev(c) = c$,
  $stev(sexp(f, e_1, ..., e_n)) = evop(f)(stev(e_1), ..., stev(e_n))$,
)

It is straightforward to show that $e bsto stev(e)$ if and only if $stev(e)$ is defined.

#todo[
  Consider alternate example:
  $sexp(smul, sexp(sadd, 1, 1), x)$

  - Reduces to $sexp(smul, 2, x)$ -- so these should be "the same"

  - Intuitively the same as $sexp(sadd, x, x)$

  - Intuitively different from $sexp(smul, 3, x)$
]

We still, however, don't know what an _open_ term means:
if we try to evaluate
$
  sexp(sadd, sexp(sadd, 3, 2), sexp(smul, x, 0))
  ssto
  sexp(sadd, 5, sexp(smul, x, 0))
  ssto
  op(med ???)
$
the first time we encounter a variable,
the relation defined above becomes _stuck_
--
that is, we reach a term $e$ which is not a constant,
and yet does not reduce to anything
--
so, according to our current conventions, 
is ill-defined like $sexp(sdiv, 1, 0)$.

If we fire up a Python REPL and try it, it seems to agree:

```python
>>> 5 + (x * 0)
```
```
Traceback (most recent call last):
  File "<stdin>", line 1, in <module>
    5 + (x * 0)
         ^
NameError: name 'x' is not defined
```

On the other hand, if $x$ is in context 
-- say $x = 7$
-- this evaluates to 5 as we'd expect:
```python
>>> x = 7
>>> 5 + (0 * x)
5
```

What this hints at is that the operational semantics of an open term $e$ depends on the context in which it is evaluated -- here, on the values of its free variables.

We can model this by defining a _contextual reduction relation_ 
$γ ⊢ e ssto e'$ parametrized by an _evaulation context_ $γ$
-- 
a finitely supported function $γ : vars pto vals$
assigning a values to variables
--
as follows:

#let cvar = rule(
  label: "var",
  [$γ(x) = c$],
  [$γ ⊢ x ssto c$]
)

#let cstep = rule(
  label: "step",
  [$evop(f)(c_1, ..., c_n) = c$],
  [$γ ⊢ sexp(f, c_1, ..., c_n) ssto c$]
)

#let carg = rule(
  label: "arg",
  [$c_1,...,c_n ∈ vals$],
  [$γ ⊢ e_1 ssto e'_1$],
  [$γ ⊢ sexp(f, c_1, ..., c_n, e_1, ..., e_m) ssto sexp(f, c_1, ..., c_n, e'_1, ..., e_m)$]
)

$
  \
  #rule-set(
    prooftree(cvar),
    prooftree(cstep),
    prooftree(carg),
  )
  \
$

We can then evaluate

$
  (x ↦ 7) ⊢
  sexp(sadd, sexp(sadd, 3, 2), sexp(smul, x, 0))
  ssto
  sexp(sadd, 5, sexp(smul, x, 0))
  ssto
  sexp(sadd, 5, sexp(smul, 7, 0))
  ssto
  sexp(sadd, 5, 0)
  ssto 
  5
$

#todo[substitution maps open terms to closed terms]

#todo[
  discuss:
  - algebra: "equivalence under substitution"
  - programming: "observational equivalence"
]

Given a set of _types_ $A ∈ types$, we'll define a 
_stack-typing relation_ on $ops$ to be any relation

$
  stty([A_1,...,A_m], f, [B_1,...,B_n])
$

where

- $A_1,...,A_m ∈ types$ are types -- $m$ is called the _input arity_ or _arity_ of $f$.

- $B_1,...,B_n ∈ types$ are types -- $n$ is called the _output arity_ of $f$.

For now, we'll only consider operations with an output 
arity of $1$.

We define a _(typing) context_ $Γ ∈ ctx(types, vars: vars)$ to be given by
a list of _bindings_
$
  x_1 : A_1, ..., x_n : A_n
$

We can define a simple type system for S-expressions by giving a typing relation $Γ ⊢ e : A$ that says "under the assumptions of $Γ$, the S-expression $e$ has type $A$". The rules are:

#let var-head = rule(
  label: "var-head",
  [#hasty($Γ, x : A$, $x$, $A$)]
)

#let var-tail = rule(
  label: "var-tail",
  [#hasty($Γ$, $y$, $B$), $x ≠ y$],
  [#hasty($Γ, x : A$, $y$, $B$)]
)

#let app = rule(
  label: "app",
  [#stty($[A_1,..., A_n]$, $f$, $[B]$)],
  [$∀ i . hasty(Γ, a_i, A_i)$],
  [$hasty(Γ, sexp(f, a_1, ..., a_n), B)$]
)

#todo[Typing rules for constants -- as distinct from nullary ops]

$
\
#rule-set(
  prooftree(var-head),
  prooftree(var-tail),
  prooftree(app)
)
\
$

#todo[_Soundness_ of typing: preservation of typing]

#todo[_Completeness_ of typing: in the presence of _simple types_]

#todo[Church vs. Curry -- we will only consider _well-typed_ terms]

#todo[Doesn't lose generality -- unityping works in this framework due to multi-arity]

#todo[_Substitution_ and _observational equivalence_ -- typing rules for substitution -- two open programs are equivalent iff equivalent under every substitution -- this is usually where _metavariables_ come in]

#todo[_Purity_ -- required for substitution to preserve equivalence -- typing rules for purity]

#todo[Denotational semantics of S-expressions: partial functions]

#todo[Denotational semantics of S-expressions: _soundness_ and _completeness_]

#todo[Equational theory of S-expressions: _purity_ -- as otherwise you can't _introduce_ divisions]

#todo[Equational theory of S-expressions: _soundness_ and _completeness_]

= State

#todo[Operational semantics of S-expressions -- _state_]

#todo[_Observational equivalence_ in the presence of state]

#todo[Denotational semantics of S-expressions -- the partial state monad]

#todo[Denotational semantics of S-expressions: _soundness_ and _completeness_]

#todo[Equational theory of S-expressions: _purity_]

#todo[Equational theory of S-expressions: _soundness_ and _completeness_]
