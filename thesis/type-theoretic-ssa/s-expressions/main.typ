#import "/lib/prelude.typ": *

= Language

We'll start by giving a formal account of the simplest practical language
-- that of expressions like $x + y$ and $a + (5 * b) + sin(3)$


Fix
- A set of _variables_ $x ∈ vars$
- A set of _operations_ $f ∈ ops$

We define the set of _S-expressions_ $e ∈ sexp(ops, vars: vars)$ to be given by the grammar

$
  e ::= x | (f med e^*)
$

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

#rule-set(
  prooftree(var-head),
  prooftree(var-tail),
  prooftree(app)
)
