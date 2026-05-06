#import "/lib/prelude.typ": *

= Language

We'll start by giving a formal account of the simplest practical language
-- that of _first-order_ expressions like $x + y$ and $a + (5 * b) + sin(3)$.

By _first-order_, 
we mean that expressions can't return functions for further application
-- for example, we can't write $ms("add")(1)(2)$ 
to mean "apply the function $λ x . (x + 1)$ to $2$"
-- instead, we've got to stick 
with the simple function applications and arithmetic expressions
most familiar to grade-schoolers and imperative programmers.

Rather than complicate our language by introducing 
binary operators (like $x + y$),
unary operators (like $-x$),
and $n$-ary function applications (like $f(x, y, z)$),
we can instead normalize everything to _S-expressions_ 
-- or _sexprs_ -- 
of the form $(f med e_1 med ... med e_n)$.

We can then uniformly write binary operations like $x + y$ 
as binary sexprs 
$(+ med x med y)$,
unary operations $-x$ as unary sexprs 
$(- med x)$, 
and function appplications $f(x, y, z)$ as $n$-ary sexprs 
$(f med x med y med z)$. 
In particular, the _operator_ $f$ always comes first,
and there is no order-of-operations -- all bracketing is explicit.

Restricting ourselves to _first-order_ sexprs means that we always require operators $f$ to be atomic symbols drawn from a fixed set $ops$
--
in particular, $f$ can't be a compound expression itself
(like in $((ms("add") med 1) med 2)$).


More formally: 

// #definition(First-order S-expressions)[
  Fixing
  - A set of _variables_ $x ∈ vars$
  - A set of _operations_ $f ∈ ops$
  - A set of _constants_ $c ∈ vals$

  we define the set of _first-order S-expressions_ 
  $e ∈ sexp1(ops, vars: vars)$ to be given by the grammar

  $
    e ::= x | c | (f med e^*)
  $
// ]

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
