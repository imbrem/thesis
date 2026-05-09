#import "/lib/prelude.typ": *
#show: chapter

= Language

We'll start by giving a formal account of the simplest practical language
-- that of _first-order_ arithmetic expressions and function calls, 
like $x + y$ and $a + (5 * b) + sin(3)$.

Rather than complicate our language by introducing 
binary operators (like $x + y$),
unary operators (like $-x$),
and $n$-ary function applications (like $f(x, y, z)$),
we can instead normalize everything to _S-expressions_ 
-- or _sexprs_ -- 
of the form $(f med e_1 med ... med e_n)$.
We can then uniformly write: 

- binary operations like $x + y$ as binary sexprs $(+ med x med y)$,

- unary operations $-x$ as unary sexprs $(- med x)$, 

- function appplications $f(x, y, z)$ as $n$-ary sexprs $(f med x med y med z)$. 

In particular, the _operator_ $f$ always comes first,
and there is no order-of-operations -- all bracketing is explicit.
//
Restricting ourselves to _first-order_ sexprs means that 
we always require operators $f$ to be atomic symbols drawn from a fixed set $ops$
--
in particular, we don't support _partial application_, 
like $((ms("add") med 2) med 3)$,
since that would require $f = (ms("add") med 2)$ to be a compound expression.

Formally, we define our _syntax_ as follows:

#definition("First-order S-expressions")[
  fixing
  - a set of _variables_ $x ∈ vars$
  - a set of _operations_ $f ∈ ops$
  - a set of _constants_ $c ∈ vals$
  we define the set of _first-order S-expressions_
  $e ∈ sexp1(ops, vars: vars)$ to be given by the grammar

  $
    e ::= x | c | (f med e^*)
  $
]

// ...

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
  [$hasty(Γ, (f med a_1 med ... med a_n), B)$]
)

$
\
#rule-set(
  prooftree(var-head),
  prooftree(var-tail),
  prooftree(app)
)
\
$
