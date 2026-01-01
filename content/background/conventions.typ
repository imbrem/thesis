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

We write function composition for $f: X → Y$, $g: Y → Z$ as
$
  f cc g := g ∘ f := λ x . g(f(x)) : X → Z
$

We write $X pfn Y$ for the set of _partial functions_ from $X$ to $Y$; we take $X → Y ⊆ X pfn Y$.
Composition of partial functions is defined pointwise as for total functions, with
$
  (f cc g)(x) := (g ∘ f)(x) := g(f(x)) "where" f(x), g(f(x)) "are defined"
$

If $f: X pfn Y$ is an injection, we define its _(partial) inverse_ $f^(-1) : Y pfn X$ to be given by
$
  f^(-1)(y) := x "if" f(x) = y
$
We note that $f: X -> Y$ is a bijection iff its inverse $f^(-1) : Y → X$ is total.

We introduce the notation $A rfn B$ for the set of _relations_ from a set $A$ to a set $B$.
Relations are _extensional_: 
given $R, S : A rfn B$, $R = S$ 
if and only if $brel(R, a, b) <==> brel(S, a, b)$ for all $a ∈ A$, $b ∈ B$.

We write:
- $id_A : A rfn A$ for the _identity relation_ on $A$, given by
  $
    brel(id_A, a, b) <==> a = b
  $
- $R cc S : A rfn C$ for the _composition_ of relations $R : A rfn B$, $S : B rfn C$, given by
  $
    brel((R cc S), a, c) <==> ∃ b ∈ B qd brel(R, a, b) ∧ brel(S, b, c)
  $
- $R^† : B rfn A$ for the _transpose_ of a relation $R : A rfn B$, given by
  $
    brel(R^†, b, a) <==> brel(R, a, b)
  $
- $R(a) := {b | brel(R, a, b)}$ for the _image_ of $a$ under $R$. 
  Dually, we write $R^†(b) = {a | brel(R, b, a)}$ for the _preimage_ of $b$ under $R$.

  Where the meaning is unambiguous, we write
  $R(A) := ⋃_(a ∈ A) R(a)$ for the image of $A$ under $R$
  and
  $R^†(B) := ⋃_(b ∈ B) R^†(b)$ for the preimage of $B$ under $R$.

- $grof(f) : A rfn B$ for the _graph_ of a (partial) function $f : A pfn B$, given by
  $
    brel(grof(f), a, b) <==> f(a) = b
  $
  We will often identify a (partial) function with its graph.
  
  In particular, we note that relations and (partial) functions are compatible w.r.t. 
  composition and identity (i.e., $grof(·)$ is _functorial_):
  #eqn-set(
    $grof(f) cc grof(g) = grof(f cc g)$,
    $grof(id_A) = id_A$
  )
  On the other hand, $f(a)$, if defined, is a _point_, while $grof(f)(a) = {f(a)}$ is a _set_;
  where confusion is unlikely we implicitly coerce the result as necessary.

  In particular, 
  noting that, _when $f^(-1)$ exists_, $f^(-1)(b) = a <==> grof(f)^†(b) = {a}$, 
  we will often write
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
  R^c   := & {(a, b) | ¬ brel(R, a, b)}
$
Likewise, we write
$∅ : A rfn B$ for the _empty relation_ 
and $⊤ : A rfn B := {(a, b) | a ∈ A, b ∈ B}$ for the _full_ relation.

= Order Theory

#definition(name: "Equivalence Relation, Setoid")[
  A relation $≈$ on a set $X$ is an _equivalence relation_ if it is
  - _reflexive_: $∀ x ∈ X . x ≈ x$
  - _symmetric_: $∀ x, y ∈ X . x ≈ y ==> y ≈ x$
  - _transitive_: $∀ x, y, z ∈ X . x ≈ y ==> y ≈ z ==> x ≈ z$

  A set equipped with a distinguished equivalence relation is called a _setoid_.
]

#definition(name: "Preorder, Partial Order")[
  A _preorder_ on a set $X$ is a binary relation $≤$ which is
  - _reflexive_: $∀ x ∈ X . x ≤ x$
  - _transitive_: $∀ x, y, z ∈ X . x ≤ y ==> y ≤ z ==> x ≤ z$

  Every preorder $≤$ induces an equivalence relation $x ≈ y := x ≤ y ∧ y ≤ x$ on $X$. We say
  $x, y ∈ X$ are _equivalent_ (w.r.t. $≤$) if $x ≈ y$.

  Where $X$ has a distinguished preorder $≤$, we will often simply say "the preorder $X$."

  We call $≤$ a _partial order_ if it is _antisymmetric_ --
  i.e., $∀ x, y ∈ X . x ≤ y ==> y ≤ x ==> x = y$.

  If $≤$ is also _total_ -- i.e., $∀ x , y ∈ X . x ≤ y ∨ y ≤ x$, we call it a _total order_.

  We call a set $X$ equipped with a distinguished partial order a
  _partially ordered set_ or _poset_.
]

#definition(name: "Upper Set, Lower Set")[
  We say a set $U ⊆ X$ in a preorder $X$ is an _upper set_ or is _upward closed_ if
  $x ∈ U$ and $x ≤ y$ implies $y ∈ U$.
  Dually, we say a set $L ⊆ X$ in a preorder $X$ is a _lower set_ or is _downward closed_ if
  $y ∈ L$ and $x ≤ y$ implies $x ∈ L$.

  We say that
  - $x$ is an _upper bound_ of $A$ if $∀ a ∈ A . a ≤ x$
  - $x$ is a _lower bound_ of $A$ if $∀ a ∈ A . x ≤ a$
  - $x$ is a _maximum_ of $A$ if $x ∈ A$ is an upper bound of $A$
  - $x$ is a _minimum_ of $A$ if $x ∈ A$ is a lower bound of $A$

  For arbitrary $A$, maxima and minima, if they exist, are unique up to equivalence;
  in particular, this implies that they are unique if $X$ is a poset.

  We may hence equip a preorder with a distinguished maximum $max A$ and minimum $min A$ for each
  subset $A ⊆ X$ where one exists.
  /*
  Without loss of generality, we may always take $max{a}, min{a} := a$.
  */

  We denote the set of upper bounds of $A$ as $ubs(A)$,
  and the set of lower bounds of $A$ as $lbs(A)$.

  Where there is no risk of confusion, we write $ubs(a) := ubs({a})$ and $lbs(a) := lbs({a})$
  for $a ∈ X$.
]

#definition(name: "Meet, Join, Lattice")[
  Given a preorder $X$ and a subset $A ⊆ X$, we say
  - $x$ is a _meet_ of $A$ if it is a _greatest lower bound_, i.e., a maximum of $lbs(A)$
  - $x$ is a _join_ of $A$ if it is a _least upper bound_, i.e., a minimum of $ubs(A)$

  For arbitrary $A$, meets and joins, if they exist, are unique up to equivalence;
  in particular, this implies that they are unique if $X$ is a poset.

  We may hence equip a preorder with a distinguished meet $⨅ A$ and join $⨆ A$ for each
  subset $A ⊆ X$ where one exists.
  /*
  Without loss of generality, we may always take $⨆{a}, ⨅{a} := a$.
  #footnote[
    While we could define $⨆ A := min(ubs(A))$ and $⨅ A := max(lbs(A))$ when they exist,
    we would not be able to satisfy the condition $∀ a . ⨆{a}, ⨅{a} := a$ unless $X$ is a poset,
    as all equivalent elements $a ≈ b$ have the same set of upper and lower bounds.
  ]
  */

  Where they exist, we write
  - $⊥ := ⨆ ∅$; in this case, we say $X$ is _bounded below_
  - $⊤ := ⨅ ∅$; in this case, we say $X$ is _bounded above_
    If both $⊥$ and $⊤$ exist, we say $X$ is _bounded_
  - $a ⊔ b := ⨆{a, b}$; if all binary joins exist, we say $X$ _has binary joins_
  - If $X$ is bounded below and has binary joins, we say $X$ _has finite joins_
  - $a ⊓ b := ⨅{a, b}$; if all binary meets exist, we say $X$ _has binary meets_
  - If $X$ is bounded above and has binary meets, we say $X$ _has finite meets_

  We say that:
  - $X$ is a _prelattice_ if it has both binary joins and meets
  - $X$ is a _join-semilattice_ if it is a poset with binary joins
  - $X$ is a _meet-semilattice_ if it is a poset with binary meets
  - $X$ is a _lattice_ if it is a join-semilattice and a meet-semilattice
  - $X$ is a _complete prelattice_ if every subset $A ⊆ X$ has both a meet and a join.
    It suffices to show that every subset $A ⊆ X$ has a join,
    or alternatively that every subset $A ⊆ X$ has a meet.
  - $X$ is a _complete lattice_ if it is a poset and a complete prelattice

  Note that we restrict the term semilattice to posets;
  for preorders, we simply say "has binary joins" or "has binary meets."
]

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

  We note that $idls(X), fils(X) ⊆ cal(P)(X)$ form a complete lattice.
  In particular, meets $⋀_i A_i$ are just set intersections $⋂_i A_i$, but joins do _not_ generally
  coincide with unions.

  As $X$ is always both an ideal and a filter,
  we may hence write $genidl(A)$ for the smallest ideal containing $A$
  and $genfil(A)$ for the smallest filter containing $A$.

  Given an ideal $I ⊆ X$, we say
  - $I$ is _principal_ if there exists $a$ s.t. $I = lbs(a)$
  - $I$ is _proper_ if $I ≠ X$
  - $I$ is _maximal_ if it is proper and $ubs(I) = {X, I}$
  - $I$ is _prime_ if, for all ideals $J, K$, $J ∩ K ⊆ I ==> J ⊆ I ∨ K ⊆ I$
    i.e. $I$ is prime in $idls(X)$.

  Likewise, given a filter $F ⊆ X$, we say
  - $F$ is _proper_ if $F ≠ X$
  - $F$ is _principal_ if there exists $a$ s.t. $F = ubs(a)$\
  - $F$ is _maximal_ if it is proper and $ubs(F) = {X, F}$
  - $F$ is _prime_ if, for all filters $J, K$, $J ∩ K ⊆ F ==> J ⊆ F ∨ K ⊆ F$
    i.e. $F$ is prime in $fils(X)$.
]

We note that:
- The complement $X sdiff I$ of an ideal $I$ is a filter;
  likewise, the complement $X sdiff F$ of a filter $F$ is an ideal
- An ideal $I$ is proper/principal/maximal/prime
  iff its complement is a proper/principal/maximal/prime filter

Every subset $A ⊆ X$ of a preorder $X$ inherits a preorder from $X$ by restriction; we may therefore
ask whether $A$ has meets or joins; these in general may be different from meets and joins in $X$.
For example:
- The join of $2, 3$ in $ℕ$ under the divisiblity order is 6
- The join of $2, 3$ in ${2, 3, 12} ⊆ ℕ$ under the divisiblity order is $12$

If (binary) joins/meets in $A$ and $X$ in fact coincide,
we say that $A$ is _closed under (binary) joins/meets_.

We note in particular that:
- If $X$ has joins, a set $A$ is an ideal iff it is downward-closed and closed under binary joins
- If $X$ has meets, a set $A$ is a filter iff it is upward-closed and closed under binary meets

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

Our primitive data structure will be the
_($I$-indexed) family_ @nlab:family $icol(a) := (i ↦ a_i | i ∈ I)$, consisting of

- An _index set_ $I$, whose elements are the _indices_ of the family.
  We will sometimes write $cix(icol(a)) := I$.

- For each index $i ∈ I$, an _element_ $a_i$.
  We will sometimes write this as a function application $icol(a) med i$.

Families are considered equal when they have the same index set and agree pointwise.

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
terms of indexed families, allowing us to re-use definitions and operations. In particular,

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

= Relational Algebra

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
      prooftree(rule(name: "split", $I "finite"$, $brel(baglift(R), a, (b_i | i ∈ I))$, $∀ i . brel(baglift(R), b_i, icol(c)_i)$, $∀ i, j . cix(icol(c)_i) ∩ cix(icol(c)_j) = ∅$, $brel(baglift(R), a, (⨆_(i ∈ I) icol(c)_i))$)),
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
