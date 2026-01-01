#import "../../syntax.typ": *
#import "../../todos.typ": *

#show: show-syntax

#context if (thesis-state.get)().is-standalone {
  set document(title: "Conventions and Notation")
  title()
}

#quote(attribution: [Abraham Lincoln (up to natural transformation)])[
  Give me six hours to chop down a tree and I will spend the first four sharpening the axe.
]

We begin with an overview of the conventions, notation, and definitions
we will use throughout this thesis.

We work in (informal) Grothendieck-Tarski set theory. In particular,
- We assume _Tarski's axiom_: every set is an element of some Grothendieck universe $cal(U)_ℓ$.
- In particular, this implies an infinite hierarchy of Grothendieck universes $cal(U)_ℓ$
  for $ℓ = 0, 1, 2...$
- We call an element of $cal(U)_ℓ$ _ℓ-small_

In general, we ignore size issues, with definitions taken to be implicitly $ℓ$-polymorphic

= Sets, Functions, and Relations

As is standard, we write $X -> Y$ for the set of functions from a set $X$ to a set $Y$.

We write $X pfn Y$ for the set of _partial functions_ from $X$ to $Y$
; we treat the _total_ functions $X -> Y$ as a _subset_ of the partial functions $X pfn Y$.

We will often define (partial) functions inline using _$λ$-abstraction_, writing
$
  λ x : X . E(x) "(where" E(x) "stands for an arbitrary expression involving" x ")"
$
to mean the function mapping $x$ to $E(x)$ whenever $E(x)$ is defined. 
We may omit the type annotation "$: X$" when it is clear from context.

For example, we write the _identity function_ on a set $X$ as
$
  id_X := λ x : X . x : X -> X
$

Composition of partial functions $f : X pfn Y$, $g : Y pfn Z$ is defined pointwise as
$
  (f cc g)(x) := (g ∘ f)(x) := g(f(x)) "where" f(x), g(f(x)) "are defined"
$
Or, using $λ$-abstraction,
$
  f cc g := g ∘ f := λ x . g(f(x)) : X pfn Z
$

We note that, if $f : X -> Y$, $g : Y -> Z$ are total, then $f cc g$ is total as well.

If $f: X pfn Y$ is an injection, we define its _(partial) inverse_ $f^(-1) : Y pfn X$ to be given by
$
  f^(-1)(y) := x "if" f(x) = y
$
We note that $f: X -> Y$ is a bijection iff its inverse $f^(-1) : Y → X$ is total.

We introduce the notation $X rfn Y$ for the set of _relations_ from a set $X$ to a set $Y$.
Relations are _extensional_:
given $R, S : X rfn Y$, $R = S$
if and only if $brel(R, x, y) <==> brel(S, x, y)$ for all $x ∈ X$, $y ∈ Y$.

We write:
- $id_X : X rfn X$ for the _identity relation_ on $X$, given by
  $
    brel(id_X, x, y) <==> x = y
  $
- $R cc S : X rfn Z$ for the _composition_ of relations $R : X rfn Y$, $S : Y rfn Z$, given by
  $
    brel((R cc S), x, z) <==> ∃ y ∈ Y qd brel(R, x, y) ∧ brel(S, y, z)
  $
- $R^† : Y rfn X$ for the _transpose_ of a relation $R : X rfn Y$, given by
  $
    brel(R^†, y, x) <==> brel(R, x, y)
  $
- $R(x) := {y | brel(R, x, y)}$ for the _image_ of $x$ under $R$.
  Dually, we write $R^†(y) = {x | brel(R, y, x)}$ for the _preimage_ of $y$ under $R$.

  Given sets $A, B$, we write:
  - $R(A) := ⋃_(a ∈ A) R(a)$ for the image of $A$ under $R$
  - $R^†(B) := ⋃_(b ∈ B) R^†(b)$ for the preimage of $B$ under $R$.
  - $fibs(R) := {R(x) | x ∈ X}$ for the _fibers_ of $R$

- $grof(f) : X rfn Y$ for the _graph_ of a (partial) function $f : X pfn Y$, given by
  $
    brel(grof(f), x, y) <==> f(x) = y
  $
  We will often identify a (partial) function with its graph.

  In particular, we note that relations and (partial) functions are compatible w.r.t.
  composition and identity (i.e., $grof(·)$ is _functorial_):
  #eqn-set(
    $grof(f) cc grof(g) = grof(f cc g)$,
    $grof(id_X) = id_X$,
  )
  Likewise, we will often write $f(A)$ to mean $grof(f)(A)$.

  On the other hand, given $x ∈ X$, 
  $f(x)$, if defined, is a _point_ in $Y$, 
  while $grof(f)(x) ⊆ Y$ is a _set_ (and always defined).

  In general, where confusion is unlikely, we abuse notation and implicitly treat:
  - $R(a) = {b}$ as $b$
  - $R(a) = ∅$ as "undefined"

  In particular,
  noting that, _when $f^(-1)$ exists_, $f^(-1)(b) = a <==> grof(f)^†(b) = {a}$,
  we will write
  $
    f^(-1)(b) & := grof(f)^†(b) = {a ∈ A | f(a) = b} \
    f^(-1)(B) & := grof(f)^†(B) = {a ∈ A | f(a) ∈ B}
  $
  even when $f$ is not injective.

Identifying relations with $R, S : A rfn B$ with sets of related pairs $R, S ⊆ A × B$,
wse may lift the basic operations on sets to relations in the usual manner:
$
  R ⊆ S := & ∀ a, b qd brel(R, a, b) ==> brel(S, a, b) \
  R ∪ S := & {(a, b) | brel(R, a, b) ∨ brel(S, a, b)} \
  R ∩ S := & {(a, b) | brel(R, a, b) ∧ brel(S, a, b)} \
    R^c := & {(a, b) | ¬ brel(R, a, b)}
$
Likewise, we write
$∅ : A rfn B$ for the _empty relation_
and $⊤ : A rfn B := {(a, b) | a ∈ A, b ∈ B}$ for the _full_ relation.

#definition(name: "Binary Relation")[
  A _binary relation_ on a set $X$ is a relation $R : X rfn X$.
  We say $R$ is:
  - _reflexive_ if $∀ x ∈ X . brel(R, x, x)$ 
    -- i.e., $id_X ⊆ R$
  - _symmetric_ if $∀ x, y ∈ X . brel(R, x, y) <==> brel(R, y, x)$ 
    -- i.e., $R^† = R$
  - _transitive_ if $∀ x, y, z ∈ X . brel(R, x, y) ==> brel(R, y, z) ==> brel(R, x, z)$
    -- i.e., $R cc R ⊆ R$
  - _antisymmetric_ if $∀ x, y ∈ X . brel(R, x, y) ==> brel(R, y, x) ==> x = y$
    -- i.e., $R ∩ R^† ⊆ id_X$

  /*
  Given a binary relation $≈$, we say:
  - $≈$ is a _partial equivalence relation_ or _PER_ if it is symmetric and transitive
  - $≈$ is an _equivalence relation_ if it is reflexive, symmetric, and transitive
  - $≤$ is a _preorder_ if it is reflexive and transitive
  - $≤$ is a _partial order_ if it is reflexive, transitive, and antisymmetric
  */
]

We borrow notation from regular expressions to represent iterates of binary relations $R : X rfn X$:

- We define $R^0 := id_X$ -- "apply $R$ zero times"
- We may now define $R^(n + 1) := R^n cc R = R cc R^n$ by induction
- We write $rfc(R) := R^0 ∪ R^1$ for "apply $R$ at most once"
  -- this is the _reflexive closure_ of $R$, the smallest reflexive relation containing $R$
- We write $trc(R) := ⋃_(n ≥ 1) R^n$ for "apply $R$ at least once"
  -- this is the _transitive closure_ of $R$, the smallest transitive relation containing $R$
- We write $rtc(R) := ⋃_(n) R^n$ for "apply $R$ any number of times"
  -- this is the _reflexive-transitive closure_ of $R$, 
     the smallest reflexive and transitive relation containing $R$

= Order and Equivalence

#definition(name: "(Partial) Equivalence Relation")[
  We call a binary relation $≈$ on a set $X$ a 
  _partial equivalence relation_ or _PER_ if it is _symmetric_ and _transitive_.
  If $≈$ is also _reflexive_, we call it an _equivalence relation_. 

  We say $x$ and $y$ are _equivalent_ (w.r.t. $≈$) if $x ≈ y$.
  
  A set with a distinguished equivalence relation is called a _setoid_.
]

We note that, 
for any PER $≈$, $(rtc(≈)) = (rfc(≈))$ is the smallest equivalence relation containing $≈$

#definition(name: "Equivalence Class")[
  In a PER, 
  - We say an element $x$ is _defined_ if $x ≈ x$ -- i.e., if $x ∈ peri(≈, X)$.
  
  - If $x$ is defined, we define its _equivalence class_ to be
    $
      [x]_≈ := {y ∈ X | x ≈ y}
    $
    This induces a partial function $[-]_≈ : X pfn [X]_≈$ with support $peri(≈, X)$.

    Where clear from context, we drop the subscript $≈$.
  
  We say that $A$ is an _equivalence class_ if $∃ x . A = [x]_≈$. 
  We say $A$ is a _partial equivalence class_ if
  $A = ∅$ or $A$ is an equivalence class; 
  or, equivalently, $∀ x, y ∈ A . x ≈ y$.
]

#definition(name: "Extensional function")[
  Given PERs $X, Y$, we say: 
  - A relation $R : X rfn Y$ is a _PER relation_, or _extensional_, if
    $
      ∀ x_1 ≈ x_2 ∈ X qd
      ∀ y_1 ≈ y_2 ∈ Y qd
      brel(R, x_1, y_1) ==> brel(R, x_2, y_2)
    $
  - A partial function $f : X pfn Y$ is _extensional_ if its graph is a PER relation
  - An extensional partial function $f : X pfn Y$ is a _PER morphism_ if, for all $x ≈ x$, 
    $f(x)$ is defined.

    That is, $x_1 ≈ x_2 <==> f(x_1) ≈ f(x_2)$.
]

#definition(name: "Preorder, Partial Order")[
  A _preorder_ on a set $X$ is a binary relation $≤$ which is reflexive and transitive.

  Every preorder $≤$ induces an equivalence relation on $X$ given by $x ≈ y := x ≤ y ∧ y ≤ x$.

  We call $≤$ a _partial order_ if it is also _antisymmetric_ --
  i.e. if $x ≈ y <==> x = y$. In particular, this holds if and only if
  $∀ x ∈ X . [x]_≈ = {x}$.

  If a partial order $≤$ is also _total_ 
  -- i.e., $∀ x , y ∈ X . x ≤ y ∨ y ≤ x$ -- we call it a _total order_.

  We call a set $X$ equipped with a distinguished partial order a
  _partially ordered set_ or _poset_.
]

#definition(name: "Upper Set, Lower Set")[
  We say a set $U ⊆ X$ in a preorder $X$ is an _upper set_ or is _upward closed_ if
  $x ∈ U$ and $x ≤ y$ implies $y ∈ U$.
  Dually, we say a set $L ⊆ X$ in a preorder $X$ is a _lower set_ or is _downward closed_ if
  $y ∈ L$ and $x ≤ y$ implies $x ∈ L$.

  We write the set of upward closed subsets of $X$ as $ups(X)$,
  and the set of downward closed subsets of $X$ as $lows(X)$.

  We say that
  - $x$ is an _upper bound_ of $A$ if $∀ a ∈ A . a ≤ x$;
    we write the set of upper bounds of $A$ as $ubs(A)$
  - $x$ is a _lower bound_ of $A$ if $∀ a ∈ A . x ≤ a$;
    we write the set of lower bounds of $A$ as $lbs(A)$
  - $x$ is a _greatest element_ of $A$ if $x ∈ A$ and $x$ is an upper bound of $A$
    -- i.e. if $x ∈ maxs(A) := ubs(A) ∩ A$
  - $x$ is a _least element_ of $A$ if $x ∈ A$ and $x$ is a lower bound of $A$;
    -- i.e. if $x ∈ mins(A) := lbs(A) ∩ A$

  Where there is no risk of confusion, we write $ubs(a) := ubs({a})$, $lbs(a) := lbs({a})$,
  $maxs(A)$, $mins(A)$ for $a ∈ X$.

  For arbitrary $A$, greatest and least elements, if they exist, are unique up to equivalence;
  we may hence, up to equivalence,
  equip any preorder with a distinguished greatest $max A$ and least $min A$ element for each
  subset $A ⊆ X$ where one exists.
]

#definition(name: "Monotone")[
  A partial function $f : X pfn Y$ between preorders $X, Y$ is _monotone_ if
  $
  ∀ x_1, x_2 qd x_1 ≤ x_2 ==> f(x_1) ≤ f(x_2) "where" f(x_1), f(x_2) "are defined"
  $
  
  Dually, $f$ is _antitone_ if
  $
  ∀ x_1, x_2 qd x_1 ≤ x_2 ==> f(x_2) ≤ f(x_1) "where" f(x_1), f(x_2) "are defined"
  $
]

We note in particular that the identity function is both monotone and antitone; moreover, both
monotone and antitone functions are closed under composition (i.e. they form a _subcategory_).
Moreover:
- If $f$ is monotone, 
  - $f(ubs(A)) ⊆ ubs(f(A))$ and $f(lbs(A)) ⊆ lbs(f(A))$
  - If $f (max A)$ is defined, then $max f(A) ≈ f (max A)$ is as well
  - If $f (min A)$ is defined, then $min f(A) ≈ f (min A)$ is as well
- Dually, if $f$ is antitone, 
  - $f(ubs(A)) ⊆ lbs(f(A))$ and $f(lbs(A)) ⊆ ubs(f(A))$
  - If $f (max A)$ is defined, then $min f(A) ≈ f (max A)$ is as well
  - If $f (min A)$ is defined, then $max f(A) ≈ f (min A)$ is as well

#definition(name: "Profunctor")[
  A relation $R : X rfn Y$ between preorders $X, Y$ is a _profunctor_ if
  $
  ∀ x_1 ≤ x_2 ∈ X qd ∀ y_1 ≤ y_2 ∈ Y qd brel(R, x_2, y_1) ==> brel(R, x_1, y_2)
  $
  Equivalently, we require that:
  - For all $x ∈ X$, $R(x) ⊆ Y$ is upward-closed, and
  - $R$ interpreted as a function $X → ups(Y)$ is _antitone_:
    $∀ x_1, x_2 qd x_1 ≤ x_2 ==> R(x_2) ⊆ R(x_1)$

  We write the set of profunctors from $X$ to $Y$ as $X prfn Y ⊆ X rfn Y$.
]

We note that:
- The identity relation $id_X : X prfn X$ is a profunctor
- The composition of profunctors $R : X prfn Y, S : Y prfn Z$ 
  is itself a profunctor $(R ; S) : X prfn Z$

#definition(name: "Meet, Join")[
  Given a preorder $X$ and a subset $A ⊆ X$, we say
  - $x$ is a _meet_ of $A$ if it is a _greatest lower bound_, i.e., a greatest element of $lbs(A)$
  - $x$ is a _join_ of $A$ if it is a _least upper bound_, i.e., a least element of $ubs(A)$

  For arbitrary $A$, meets and joins, if they exist, are unique up to equivalence;
  in particular, this implies that they are unique if $X$ is a poset.

  We may hence, up to equivalence, 
  equip any preorder with a distinguished meet $⨅ A$ and join $⨆ A$ for each
  subset $A ⊆ X$ where one exists.

  Where they exist, we write
  - $⊥ := ⨆ ∅$; in this case, we say $X$ is _bounded below_
  - $⊤ := ⨅ ∅$; in this case, we say $X$ is _bounded above_
  - $a ⊔ b := ⨆{a, b}$; if all binary joins exist, we say $X$ _has binary joins_
  - $a ⊓ b := ⨅{a, b}$; if all binary meets exist, we say $X$ _has binary meets_

  If both $⊥$ and $⊤$ exist, we say $X$ is _bounded_

  In general, we say that:
  - $X$ _has joins_ if every nonempty $A ⊆ X$ has a join
  - $X$ _has meets_ if every nonempty $A ⊆ X$ has a meet
  - $X$ _has finite/countable joins_ if every finite/countable $A ⊆ X$ has a join
  - $X$ _has finite/countable meets_ if every finite/countable $A ⊆ X$ has a meet
]

We note in particular that $X$ has finite joins iff it is bounded below and has binary joins;
dually, $X$ has finite meets iff it is bounded above and has binary meets.

#definition(name: "Lattice")[
  We say that:
  - $X$ is a _prelattice_ if it has both binary joins and meets
  - $X$ is a _join-semilattice_ if it is a poset with binary joins
  - $X$ is a _meet-semilattice_ if it is a poset with binary meets
  - $X$ is a _lattice_ if it is a join-semilattice and a meet-semilattice
]

#definition(name: "Complete Lattice")[
  - $X$ is a _complete prelattice_ if every subset $A ⊆ X$ has both a meet and a join.
    It suffices to show that every subset $A ⊆ X$ has a join,
    or alternatively that every subset $A ⊆ X$ has a meet.
  - $X$ is a _complete lattice_ if it is a poset and a complete prelattice
]


Every subset $A ⊆ X$ of a preorder $X$ inherits a preorder from $X$ by restriction.
/*
; we may therefore
ask whether $A$ has meets or joins; 
even when they exist, however, they might be different from meets and joins in $X$.
For example:
- The join of $2, 3$ in $ℕ$ under the divisiblity order is 6
- The join of $2, 3$ in ${2, 3, 12} ⊆ ℕ$ under the divisiblity order is $12$
*/

We say:
- $A$ is _closed under joins_ if, for every nonempty subset $B ⊆ A$,
  if $x$ is a join of $B$ in $X$ then $x ∈ A$.
- $A$ is _closed under binary/finite/countable_ joins if, 
  for every binary/finite/countable subset $B ⊆ A$,
  if $x$ is a join of $B$ in $X$ then $x ∈ A$.

We define closure under (binary/finite/countable) meets dually.

We note that:
- If $A$ is a lower-set, it is closed under meets; 
  dually, if $A$ is an upper-set, it is closed under joins

- $ubs(X)$ and $lbs(X)$ are both closed under joins and meets as subsets of $cal(P)$

- If $X$ is a complete lattice and $A ⊆ X$ is a lower set, then $A$ itself is a complete lattice
  iff it has a maximum. In this case, it inherits meets (but _not_, in general, joins) from $X$.

  Dually, if $A ⊆ X$ is an upper set, then $A$ itself is a complete lattice iff it has a minimum.
  In this case, it inherits joins (but _not_, in general, meets) from $X$.

- For any $X$, $cal(P)(X)$ forms a complete lattice under unions and intersections

We are often interested in the case where any elements without a join can be treated like they have
a join "at infinity," or dually, any elements without a meet can be treated like they have
a meet "at negative infinity." To do so, we introduce the following definition:

#definition(name: "Near-Lattice, Conditionally-Complete Lattice")[
  Given a preorder $X$,
  - $X$ _has binary upper joins_ if any two elements with a common upper bound have a join,
    or, equivalently, every non-empty finite $A ⊆ X$ has a join iff it has an upper bound
  - $X$ _has binary lower meets_ if any two elements with a common lower bound have a meet,
    or, equivalently, every non-empty finite $A ⊆ X$ has a meet iff it has a lower bound
  - $X$ is a _near-prelattice_ if it has binary upper joins and binary lower meets
  - $X$ _has upper joins_ if every non-empty $A ⊆ X$ has a join
    whenever it has an upper bound
  - $X$ _has lower meets_ if every non-empty $A ⊆ X$ has a meet
    whenever it has a lower bound
  - $X$ is a _conditionally complete prelattice_ if it has both upper joins and lower meets

  If $X$ is a poset,
  - $X$ is an _upper-semilattice_ when it has finite upper joins
  - $X$ is a _lower-semilattice_ when it has finite lower meets
  - $X$ is a _near-lattice_ when it is a near-prelattice
  - $X$ is a _conditionally-complete join-semilattice_ when it has upper joins
  - $X$ is a _conditionally-complete meet-semilattice_ when it has lower meets
  - $X$ is a _conditionally-complete lattice_ when it is a conditionally-complete prelattice
]

#definition(name: "Prime, Coprime")[
  Given a preorder $X$, we say
  - An element $p ∈ X$ is _prime_ if, for all $x, y ∈ X$, if the meet $x ⊓ y$ exists, then
    $
      x ⊓ y ≤ p ==> x ≤ p ∨ y ≤ p
    $
  - An element $p ∈ X$ is _coprime_ or _dual-primte_
    if, for all $x, y ∈ X$, if the join $x ⊔ y$ exists, then
    $
      p ≤ x ⊔ y ==> p ≤ x ∨ p ≤ y
    $
]

#definition(name: "Ideal, Filter")[
  A subset $A ⊆ X$ of a preorder $X$ is
  - _directed_ if every pair $a, b ∈ A$ has an upper bound in $A$
  - _filtered_ if every pair $a, b ∈ A$ has a lower bound in $A$
  - an _ideal_ if it is a downward-closed directed set;
    we write the set of ideals of $X$ as $idls(X)$
  - a _filter_ if it is an upward-closed filtered set;
    we write the set of filters of $X$ as $fils(X)$

  We note that the subset of an ideal/filter is itself an ideal/filter; 
  hence, $idls(X), fils(X) ⊆ cal(P)(X)$ are lower sets 
  and therefore complete lattices closed under meets.

  As $X$ is always both an ideal and a filter,
  we may hence write $genidl(A)$ for the smallest ideal containing $A$
  and $genfil(A)$ for the smallest filter containing $A$.

  Given an ideal $I ⊆ X$, we say
  - $I$ is _principal_ if there exists $a$ s.t. $I = lbs(a)$
  - $I$ is _subprincipal_ if $I$ is principal or $I = ∅$
  - $I$ is _proper_ if $I ≠ X$
  - $I$ is _maximal_ if it is proper and $ubs(I) = {X, I}$
  - $I$ is _prime_ if, for all ideals $J, K$, $J ∩ K ⊆ I ==> J ⊆ I ∨ K ⊆ I$
    i.e. $I$ is prime in $idls(X)$.

  Likewise, given a filter $F ⊆ X$, we say
  - $F$ is _proper_ if $F ≠ X$
  - $F$ is _principal_ if there exists $a$ s.t. $F = ubs(a)$
  - $F$ is _subprincipal_ if $F$ is principal or $F = ∅$
  - $F$ is _maximal_ if it is proper and $ubs(F) = {X, F}$
  - $F$ is _prime_ if, for all filters $J, K$, $J ∩ K ⊆ F ==> J ⊆ F ∨ K ⊆ F$
    i.e. $F$ is prime in $fils(X)$.
]

We note that:
- The complement $X sdiff I$ of an ideal $I$ is a filter;
  likewise, the complement $X sdiff F$ of a filter $F$ is an ideal
- An ideal $I$ is proper/principal/maximal/prime
  iff its complement is a proper/principal/maximal/prime filter
- $I$ is principal iff $⨆ I ∈ I$; in which case $I$ contains all joins

We note in particular that:
- If $X$ has binary joins, 
  a set $A$ is an ideal iff it is downward-closed and closed under binary joins
- If $X$ has binary meets, 
  a set $A$ is a filter iff it is upward-closed and closed under binary meets

#definition(name: [dcpo, $ω$cpo])[
  Given a preorder $X$,
  - $X$ has _(nonempty) directed joins_ if every (nonempty) directed subset $A ⊆ X$ has a join
  - A subset $A ⊆ X$ is a _pointed, or nonempty, ω-chain_
    if we can write it as an infinite nondecreasing sequence
    $
      a_0 ≤ a_1 ≤ a_2 ≤ a_3 ≤ ...
    $
    -- i.e.,
    there exists a function $a : ℕ → X$ s.t.
    $∀ n . a(n) ≤ a(n + 1)$ and $a(ℕ) = A$.

    We say $A$ is an $ω$-chain if $A = ∅$ or $A$ is a pointed $ω$-chain.

  - $X$ has _(nonempty) $ω$-joins_ if every (nonempty) ω-chain $A$ has a join

  If $X$ is a partial order
  #footnote[
    By our convention, directed sets and $ω$-chains may be empty. Hence, we only need to state
    "has directed joins" and "has $ω$-joins," which implicitly implies the existence of a bottom
    element (the join of the empty set).
  ],
  - We say $X$ is a _directed complete partial order_ or _dcpo_ if it has directed joins
  - We say $X$ is an _$ω$-complete partial order_ or _$ω$cpo_ if it has $ω$-joins
]

= Families, Sequences, Lists, and Streams

Our primitive data structure will be the indexed family, which we define as follows:

#definition(name: "Indexed Family")[
  An _($I$-indexed) family_ @nlab:family $icol(a) := (i ↦ a_i | i ∈ I)$, consists of of

  - An _index set_ $I$, whose elements are the _indices_ of the family.
    We will sometimes write $cix(icol(a)) := I$.

  - For each index $i ∈ I$, an _element_ $a_i$.
    We will sometimes write this as a function application $icol(a) med i$.

  Families are considered equal when they have the same index set and agree pointwise.
]

We write $A^I$ for the set of indexed families with index set $I$ and elements of type $A$.
We say $icol(a) ∈ A^I$ is _finite_ if $I$ is finite;
we write the set of finite families of $A$ as $sffam(A)$.

We introduce notation:
- $(a_i | i ∈ I) := (i ↦ a_i | i ∈ I)$; where $I$ is clear from context, we write $(a_i)_i$
- $(t_i ↦ a_i | i ∈ I) := (t ↦ a_(f^(-1)(i)) | t ∈ f(I))$
  where $f(i) := t_i$ is an injection

Where the indexing set $I$ is clear from context,
we will write $(a_i | i ∈ I)$ or $(a_i)_i$ as shorthand for $(i ↦ a_i | i ∈ I)$.
For $I$ finite, we write $(i_0 ↦ a_(i_0),...,i_(n-1) ↦ a_(n-1))$.
In particular, we write the empty indexed family as $()$.

Given indexed families $icol(a) = (a_i | i ∈ I)$, $icol(b) = (b_j | j ∈ J)$,
we define their _override_ as follows:
$
  icol(a) ovrd icol(b) = [λ k . site(k ∈ I, a_k, b_k) | k ∈ I ∪ J]
$

By convention, $ovrd$ is left-biased: when both families define an index, the left value is chosen.

We note that $ovrd$ is a monoid with identity $()$ -- i.e.
$() ovrd icol(a) = icol(a) ovrd () = icol(a)$ and
$icol(a) ovrd (icol(b) ovrd icol(c)) = (icol(a) ovrd icol(b)) ovrd icol(c)$

We say
- $icol(a), icol(b)$ are _compatible_, written $icol(a) cmpfam icol(b)$,
  if $∀ i ∈ cix(icol(a)) ∩ cix(icol(b)) . a_i = b_i$
- $icol(a), icol(b)$ are _disjoint_, written $icol(a) aprtfam icol(b)$,
  if $cix(icol(a)) ∩ cix(icol(b)) = ∅$
- $icol(a)$ is a _subfamily_ of $icol(b)$, written $icol(a) ⊆ icol(b)$,
  if $cix(icol(a)) ⊆ cix(icol(b))$ and $icol(a) cmpfam icol(b)$

The relation $icol(a) ⊆ icol(b)$ induces an upper meet-semilattice on families, with
- bottom element $()$
- meet $icol(a) ∩ icol(b) := (a_i | i ∈ cix(icol(a)) ∩ cix(icol(b)) ∧ a_i = b_i)$
- join $icol(a) ∪ icol(b) := icol(a) ovrd icol(b) = icol(b) ovrd icol(a)$
  defined whenever $icol(a) cmpfam icol(b)$

/*
We define some basic structural operations on indexed families as follows:
- We define the _selection_ of $J ⊆ I$ from an indexed family $icol(a) = (a_i | i ∈ I)$
  as follows:
  $
    csel(icol(a), J) = (a_i | i ∈ I ∩ J)
  $

- We define the _removal_ of $J ⊆ I$ from an indexed family $icol(a) = (a_i | i ∈ I)$
  as follows:
  $
    crem(icol(a), J) = (a_i | i ∈ I sdiff J)
  $

  We note that
  $csel(icol(a), J) ⊔ (crem(icol(a), J)) = (crem(icol(a), J)) ⊔ csel(icol(a), J) = icol(a)$.
*/

#todo[_ordered_ indexed families]

#todo[square bracket notation $[]$ means ordered family]

#todo[lift of $⊆$ ignores order]

#todo[new $⊑$ respects order]

As in Lua @ierusalimschy-06-lua (which uses tables), we define lists, sequences, and streams in
terms of (ordered) indexed families, allowing us to re-use definitions and operations. 

In particular,

#definition(name: "Sequence, List, Stream")[
  A _sequence_ $icol(a) = [a_i | i ∈ I]$ is an indexed family $(a_i | i ∈ I)$ where
  - $I = fin(n)$ for some $n ∈ ℕ$, in which case we call $icol(a)$ a _list_ or _$n$-tuple_, or
  - $I = ℕ$ , in which case we call $icol(a)$ a _stream_

  We write:
  - the set of lists of length $n$ as $A^n$
  - the set of all lists as $A^* := ⋃_(n ∈ ℕ) A^n$;
    the set of nonempty lists as $A^+ := ⋃_(n ≥ 1) A^n$
  - the set of streams as $A^ω$
    ; the set of sequences as $A^(≤ω) := A^ω ∪ A^*$

  In general, we will reserve square brackets $[ - ]$ for sequences
  (rather than general indexed families), writing

  - $lnil := ()$ for the empty list
  - $[a_0,...,a_(n - 1)]$ for a list of length $n$
  - $[a_0, a_1, a_2, ...]$ for a stream
  - _Comprehensions_ $[f(a) | a ∈ icol(a)] := [f(a_i) | i ∈ I]$ for $I = ℕ$ or $I = fin(n)$.

  Note that, following the convention in computer science, our sequences are _zero-indexed_.
]

The basic operations on lists and sequences can then be given either inductively or functionally
in terms of indexed families:

- Given an arbitrary sequence $icol(a)$, we can append an element $x$ to the front of $icol(a)$
  to form a new sequence $x :: icol(a)$ (pronounced "$x$ _cons_ $icol(a)$") as follows:
  $
    x :: icol(a)
    := [λ | 0 => x | i + 1 => icol(a) med i]
    = [x, a_0, a_1, ...]
  $

  If $icol(a)$ is in fact finite, we may append an element $x$ to the back,
  forming a new sequence $icol(a) lsnoc x$ (pronounced "$icol(a)$ _snoc_ $x$") analogously:
  $
    icol(a) lsnoc x
    := [λ i . site(i < |icol(a)|, icol(a) med i, x)]
    = [a_0, a_1, ..., a_(n - 1), x]
  $

- We define the _concatenation_ of a list $icol(a)$ to a sequence $icol(b)$,
  written $icol(a) lcat icol(b)$, by induction on $icol(a)$ as follows:
  #eqn-set(
    $lnil lcat icol(b) = icol(b)$,
    $(x :: icol(a)) lcat icol(b) = x :: (icol(a) lcat icol(b))$,
  )

  For $icol(a)$ of length $n$, we can show by induction that
  $
    icol(a) lcat icol(b)
    = [a_0,...,a_(n - 1),b_0, b_1, ...]
    = [λ i . site(i < n, a_i, b_(i - n))]
  $

  In particular, we note that
  #eqn-set(
    $lnil lcat icol(a) = icol(a) lcat lnil = icol(a)$,
    $[a] lcat icol(a) = a :: icol(a)$,
    $icol(a) lcat [b] = icol(a) lsnoc b$,
    $icol(a) lcat (icol(b) lcat icol(c)) = (icol(a) lcat icol(b)) lcat icol(c)$,
  )

- We define the _repetition_ of a list $icol(a)$, written $n · icol(a)$, by induction as follows:
  #eqn-set(
    $0 · icol(a) = lnil$,
    $(n + 1) · icol(a) = icol(a) lcat n · icol(a)$,
  )

- We define the _flattening_ of a list of lists $icol(a)$, written $lflat(icol(a))$,
  by induction as follows:
  #eqn-set(
    $lflat(lnil) := lnil$,
    $lflat((x :: icol(a))) := x lcat lflat(icol(a))$,
  )
  We note in particular that
  #eqn-set(
    $lflat(icol(a) lsnoc x) = lflat(icol(a)) lcat x$,
    $lflat(icol(a) lcat icol(b)) = lflat(icol(a)) lcat lflat(icol(b))$,
  )

= Products, Coproducts, and Reindexing

Given a family of sets $icol(A) = (A_i | i ∈ I)$, we define their _product_ $Π icol(A)$ and
_coproduct_ $Σ icol(A)$ as follows:
#eqn-set(
  $Π icol(A) := {icol(a) := (a_i | i ∈ I) | ∀ i . a_i ∈ A_i}$,
  $Σ icol(A) := {(i, a) | i ∈ I, a ∈ A_i}$,
)
These are equipped with the usual projection and injection functions
#eqn-set(
  $π_i : Π icol(A) -> A_i := λ icol(a) . a_i$,
  $ι_i : A_i -> Σ icol(A) := λ a . (i, a)$,
)

We will transparently identify binary products and coproducts $A × B$, $A + B$ with the
product and coproduct of $(kwl ↦ A, kwr ↦ B)$, respectively.

We note the existence of canonical isomorphisms
- $(A × B) × C ≈ A × (B × C)$ and $(A + B) + C ≈ A + (B + C)$ (the _associators_)
- $A × tunit ≈ tunit × A ≈ A$ and $A + tzero ≈ tzero + A ≈ A$ (the _unitors_),
  where we define $tunit := Π() = {()}$ and $tzero := Σ() = ∅$
- $Π (icol(A) lcat icol(B)) ≈ Π icol(A) × Π icol(B)$ and
  $Σ (icol(A) lcat icol(B)) ≈ Σ icol(A) + Σ icol(B)$
- $Π (i ↦ A) ≈ A$ and $Σ (i ↦ A) ≈ A$ for singleton index sets

In general, we write $α^×$ for arbitrary compositions of these isomorphisms for products,
and likewise $α^+$ for coproducts.
This is unambiguous, since any two such composites define the same canonical isomorphism.

Similarly, we have canonical isomorphisms
- $σ^× : A × B ≈ B × A$, $σ^+ : A + B ≈ B + A$ (the _symmetry_)
- $δ_kwl : Σ (A × icol(B)) ≈ A × Σ icol(B)$,
  $δ_kwr : Σ (icol(A) × B) ≈ Σ icol(A) × B$ (the _distributors_)
where
#eqn-set(
  $A × (B_i | i ∈ I) := (i ↦ A × B_i | i ∈ I)$,
  $(A_i | i ∈ I) × B := (i ↦ A_i × B | i ∈ I)$,
)
are defined pointwise.

We can extend the product and coproduct to _families_ of functions
$icol(f) = (f_i : A_i -> B_i | i ∈ I)$ pointwise:
#eqn-set(
  $Π icol(f) : Π icol(A) -> Π icol(B) := λ icol(a). (f_i med a_i | i ∈ I)$,
  $Σ icol(f) : Σ icol(A) -> Σ icol(B) := λ (i, a) . (i, f_i med a)$,
)
In particular, this yields the usual
$f × g : A_kwl × A_kwr → B_kwl × B_kwr$ and
$f + g : A_kwl + A_kwr → B_kwl + B_kwr$.

As a notational convenience, we will write $A × f := id_A × f$, $f × A := f × id_A$.

We may likewise
- Given a family of functions $icol(f) := (f_i : A -> B_i)$, define the product _constructor_
  $
    ⟨icol(f)⟩ : A → Π icol(B) := λ a . (f_i med a | i ∈ I)
  $
- Given a family of functions $icol(f) := (f_i : A_i -> B)$, define the coproduct _eliminator_
  $
    [icol(f)] : Σ icol(A) → B := λ (i, a) . f_i med a
  $

As a notational convenience, we will often write:
- $⟨f_i | i ∈ I⟩$ to mean $⟨(f_i | i ∈ I)⟩$
- $⟨f_0,...,f_(n - 1)⟩$ to mean $⟨[f_0,...,f_(n - 1)]⟩$ or, in the case of $n = 1$,
  $⟨(kwl ↦ f_0, kwr ↦ f_1)⟩$

and likewise for products.

#definition(name: "Reindexing")[
  Given families $icol(a) = (a_i | i ∈ I)$, $icol(b) = (b_j | j ∈ J)$,
  we define the _reindexings_ from $icol(b)$ into $icol(a)$:
  $
    hfam(icol(a), icol(b)) := { ρ : J → I | ∀ j ∈ J . a_(ρ med j) = b_j }
  $
  We note that
  - We always have $id_cix(icol(a)) : hfam(icol(a), icol(a))$

  - If $ρ_1 : hfam(icol(a), icol(b))$ and $ρ_2 : hfam(icol(b), icol(c))$,
    then $ρ_1 ∘ ρ_2 : hfam(icol(a), icol(c))$ (_not_ $ρ_1 cc ρ_2$, which is $ρ_2 ∘ ρ_1$!)

    For clarity, we will write this as $ρ_1 famcomp ρ_2$ to emphasize that $ρ_1$ is a reindexing.

  In particular, this makes the reindexings into a _category_ with objects indexed families and
  morphisms reindexings.
]

Given families of sets $icol(A), icol(B)$, a reindexing $ρ: hfam(icol(A), icol(B))$ induces maps
#eqn-set(
  $ρ^* : Π icol(A) -> Π icol(B) := λ icol(a), (a_(ρ med j) | j ∈ J)$,
  $ρ_* : Σ icol(B) -> Σ icol(A) := λ (j, b) . (ρ med j, b)$,
)

These operations are functorial:
#eqn-set(
  $id_(cix(icol(A)))^* = id_(Π icol(A))$,
  $id_(cix(icol(A))*) = id_(Σ icol(A))$,
  $(ρ_1 famcomp ρ_2)^* = ρ_1^* cc ρ_2^*$,
  $(ρ_1 famcomp ρ_2)_* = ρ_(2*) cc ρ_(1*)$,
)

#definition(name: "Thinning, Permutation")[
  An injective reindexing is called a _thinning_,
  while a bijective reindexing is called a _permutation_.
  We denote the sets of such reindexings as
  $
    hthin(icol(a), icol(b)) & := { ρ ∈ hfam(icol(a), icol(b)) | ρ "is injective" } \
    hperm(icol(a), icol(b)) & := { ρ ∈ hthin(icol(a), icol(b)) | ρ "is bijective" } \
  $
]

Thinnings model dropping indices, while permutations model reordering. In particular,

- If $ρ : hthin(icol(A), icol(B))$, $ρ^*$ is surjective and $ρ_*$ is injective
- If $ρ : hperm(icol(A), icol(B))$, both $ρ^*$ and $ρ_*$ are isomorphisms

Both these subsets contain the identity reindexing and are closed under (reverse) composition
(i.e., are wide subcategories of the category of reindexings).
Furthermore, the set of permutations is closed under inverses (which always exist):
$
  ∀ ρ ∈ hperm(icol(a), icol(b)), ρ^(-1) ∈ hperm(icol(b), icol(a))
$
That is, the permutations are in fact a _groupoid_.

= Families of Relations

#definition(name: "Family of relations")[
  Given families of sets
  $icol(A) = (A_i | i ∈ I)$,
  $icol(B) = (B_i | i ∈ I)$,
  we define a _family of relations_ $icol(R) : icol(A) rfn icol(B)$ to be a family
  $icol(R) = (R_i : A_i rfn B_i | i ∈ I)$.

  We generalize the definition of the identity, composition, and transpose of relations pointwise:
  #eqn-set(
    $id_(icol(A)) := (id_(A_i) | i ∈ I)$,
    $icol(R) cc icol(S) := (R_i cc S_i | i ∈ I)$,
    $icol(R)^† := (R_i^† | i ∈ I)$,
  )

  We can likewise define the graph of a family of functions
  $icol(f): icol(A) -> icol(B)$ pointwise:
  $
    grof(icol(f)) = (grof(f_i) | i ∈ I)
  $
]

#definition(name: "Tensor product of relations")[
  Given a family of relations $icol(R) : icol(A) rfn icol(B)$, we define its _tensor product_
  pointwise as follows
  $
    tcol icol(R) : Π icol(A) rfn Π icol(B)
    := stor({(icol(a), icol(b)) | ∀ i . brel(R_i, a_i, b_i)})
  $

  This readily specializes to the binary tensor product of relations
  $R : A_kwl rfn B_kwl$, $S : A_kwr rfn B_kwr$:
  $
    R ⊗ S : A_kwl × A_kwr rfn B_kwl × B_kwr
    := {((a_kwl, a_kwr), (b_kwl, b_kwr)) | brel(R, a_kwl, b_kwl) ∧ brel(S, a_kwr, b_kwr)}
  $
]

We note that the tensor product is also functorial and transpose-preserving:
#eqn-set(
  $tcol id_icol(A) = id_(Π icol(A))$,
  $tcol (icol(R) cc icol(S)) = tcol icol(R) cc tcol icol(S)$,
  $tcol icol(R)^† = (tcol icol(R))^†$,
)
and, in particular,
#eqn-set(
  $id_A ⊗ id_B = id_(A × B)$,
  $(R_kwl ⊗ R_kwr) cc (S_kwl ⊗ S_kwr) = (R_kwl cc R_kwl) ⊗ (S_kwl cc S_kwr)$,
)

As a syntactic convenience
(and for consistency with our later notation of premonoidal categories),
we will define notation
- $A ⊗ R := id_A ⊗ R$ and $R ⊗ A := R ⊗ id_A$ for sets $A$.
- Associator isomorphisms $α^⊗ := α^×_*$
- Symmetry isomorphism $σ^⊗ := σ^×_*$
- Distributor isomorphisms $δ^⊗_kwl := δ^×_(kwl*)$, $δ^⊗_kwr := δ^×_(kwr*)$

Where there is no risk of confusion, we will drop the superscript.

We say that a binary operation $m: A × A -> A$ is
- _commutative_ if $∀ a, b . m(a, b) = m(b, a)$
- _associative_ if $∀ a, b, c . m(m(a, b), c) = m(a, m(b, c))$

Written in point-free style, these become
- _commutative_: $σ^× cc m = m$
- _associative_: $m ⊗ A cc m = α^× cc A ⊗ m cc m$

We can directly generalize these definitions to relations: a relation $R : A × A rfn A$ is
- _commutative_ if $σ^⊗ cc R = R$, or, pointwise,
  $
    brel(R, (a, b), c) <==> brel(R, (b, a), c)
  $
- _associative_ if $R ⊗ A cc R = α^⊗ cc A ⊗ R cc R$, or, pointwise,
  $
    (∃ a_(12) . brel(R, (a_1, a_2), a_(12)) ∧ brel(R, (a_(12), a_3), a_(123)))
    <==>
    (∃ a_(23) . brel(R, (a_2, a_3), a_(23)) ∧ brel(R, (a_1, a_(23)), a_(123)))
  $

Transposing these, we say a relation $R : A rfn A × A$ is
- _cocommutative_ if $R^†$ is commutative -- i.e., $R cc σ^⊗ = R$, or, pointwise,
  $
    brel(R, a, (b, c)) <==> brel(R, a, (c, b))
  $
- _coassociative_ if $R^†$ is associative -- i.e., $R cc R ⊗ A = R cc A ⊗ R cc α^⊗$, or, pointwise,
  $
    (∃ a_(12) . brel(R, a_(123), (a_(12), a_3)) ∧ brel(R, a_(12), (a_1, a_2)))
    <==>
    (∃ a_(23) . brel(R, a_(123), (a_1, a_(23))) ∧ brel(R, a_(23), (a_2, a_3)))
  $

Given a relation $R : A rfn A^ms("fin")$ we define:
- Its _components_ $R_n : A rfn A^n ⊆ R$ to be its restriction to target $A^n$ for each $n ∈ ℕ$.

  We note in particular that any relation $S : A rfn A^n$, and in particular $R_n$,
  may be considered a relation $S: A rfn A^ms("fin")$
  by transport along the inclusion $A^n ⊆ A^ms("fin")$.

- Its _bag lifting_ $baglift(R) : A rfn A^ms("fin")$ to be the least relation closed under the
  following rules:
  $
    #rule-set(
      prooftree(rule(name: "base", $brel(R, a, icol(a))$, $brel(baglift(R), a, icol(a))$)),
      prooftree(rule(name: "unit", $brel(baglift(R), a, (i ↦ a))$)),
      prooftree(rule(
        name: "split",
        $I "finite"$,
        $brel(baglift(R), a, (b_i | i ∈ I))$,
        $∀ i . brel(baglift(R), b_i, icol(c)_i)$,
        $∀ i, j . cix(icol(c)_i) ∩ cix(icol(c)_j) = ∅$,
        $brel(baglift(R), a, (⨆_(i ∈ I) icol(c)_i))$,
      )),
    )
  $

We note that:
- $R ⊆ baglift(R) = baglift((baglift(R)))$; $R ⊆ S ==> baglift(R) ⊆ baglift(S)$
- If $R : A rfn A × A$ is cocommutative and coassociative, then $baglift(R)_2 = R$

In general, we call a relation $R : A rfn A^ms("fin")$ _Segal_ if there exists $S : A rfn A × A$
s.t. $R = baglift(S)$; in which case $S = R_2$.

#definition(name: "Diagonal, codiagonal, discard")[
  Given a set $A$, we define
  - the _discard relation_
    $dropm_A : A rfn tunit := ⟨{(a, ()) | a ∈ A}⟩$
  - the _diagonal relation_
    $Δ^(⊗I)_A : A rfn A^I := ⟨{(a, (i ↦ a | i ∈ I)) | a ∈ A}⟩$
  - the _codiagonal relation_
    $∇^(⊗I)_A : A^I rfn A := (Δ^⊗_(I, A))^† = ⟨{((i ↦ a | i ∈ I), a) | a ∈ A}⟩$

  Where there is no risk of confusion, we will drop the subscript $A$.

  Likewise, we will often drop the index set annotation $I$,
  and, when it is not implied by the context, assume $I = {kwl, kwr}$ by default,
  i.e., the usual binary diagonal and codiagonal relations.
]

We note in particular that:
- $Δ^⊗$ is coassociative and cocommutative, and has _unit_ $dropm$:
  $Δ^⊗ cc ! ⊗ A = id cc α^⊗$
- $Δ^(⊗ ms("fin")) := ⋃_(|I| < ω)Δ^(⊗ I)$ and $Δ^(⊗ ms("fin")+) := ⋃_(1 ≤ |I| < ω)Δ^(⊗ I)$
  are Segal,
  with $baglift((Δ^⊗ ∪ dropm)) = Δ^(⊗ ms("fin"))$, and $baglift((Δ^⊗)) = Δ^(⊗ ms("fin")+)$
  respectively.

= Cofinite Quantification

#definition(name: "Cofinite Quantifiers")[
  Given a set $X$, we write the set of finite subsets of $X$ as $fset(X)$.

  We define _cofinite quantifiers_ as follows:
  #eqn-set(
    $ucof x ∈ X . φ := ∃ L ∈ fset(X) . ∀ x ∉ L . φ$,
    $ecof x ∈ X . φ := ∀ L ∈ fset(X) . ∃ x ∉ L . φ$,
  )

  Equivalently,
  #eqn-set(
    $
      ucof x ∈ X . φ <==> { x ∈ X | ¬ φ } "finite"
    $,
    $
      ecof x ∈ X . φ <==> { x ∈ X | φ } "infinite"
    $,
  )

  When clear from context, we omit the set $X$ being quantified over, writing simply
  $ucof x . φ$ and $ecof x . φ$.

  If $ucof x . φ$, we say $φ$ _holds cofinitely_ or _holds modulo a finite set_.

  In particular,
  - $f, g : A -> B$ are _finitely different_ or _cofinitely equal_, written $f fdiff g$,
    if $ucof a . f med a = g med a$
  - $f : A -> B$ is _cofinitely constant_ or _constant modulo a finite set_ if
    it is finitely different from a constant function, i.e.
    $∃ b . ucof a . f med a = b$
]

#align(center, table(
  columns: 2,
  stroke: none,
  inset: 1em,
  [Example], [Explanation],
  $ucof x ∈ ℕ . x > 2$, [Only finitely many natural numbers ${0, 1, 2}$ are not $> 2$],
  $¬ (ucof x ∈ ℕ . x "prime")$, [There are infinitely many non-prime numbers],
  $¬ (ucof x ∈ ℕ . x = 1)$, [There are infinitely many numbers $≠ 1$],
  $ecof x ∈ ℕ . x > 2$, [There are infinitely many numbers $> 2$],
  $ecof x ∈ ℕ . x "prime"$, [There are infinitely many prime numbers],
  $¬ (ecof x ∈ ℕ . x = 1)$, [There are only finitely many numbers $= 1$],
))

#eqn-set(
  $¬ (ucof x ∈ X . φ) <==> ecof x ∈ X . ¬ φ$,
  $¬ (ecof x ∈ X . φ) <==> ucof x ∈ X . ¬ φ$,
)

$
  #diagram($
    //
      & ∀ x ∈ X . φ edge("dl", =>) edge("dr", X "infinite", =>) //
                    &                               \
    ucof x ∈ X . φ edge("dr", X ≠ ∅, =>, label-side: #right)
    edge("rr", X "infinite", "=>", label-side: #right)
    //
      &             & ecof x ∈ X . φ edge("dl", =>) \
      & ∃ x ∈ X . φ
  $)
$

/*

// IF we have time to add locally-nameless and describe the formalization in detail

#todo[STLC example]

#todo[Quotienting by $α$]

#todo[de-Bruijn indices]

#todo[Substitution]

#todo[Locally-nameless de-Bruijn indices, _locally closed_ terms]

#todo[Opening and closing]

#todo[Cofinite quantification in locally-nameless rule for lambda abstraction]

#todo[What we write and what we mean]

*/

#context if (thesis-state.get)().is-standalone {
  the-bibliography
}
