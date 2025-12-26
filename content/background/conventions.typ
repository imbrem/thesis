#import "../../syntax.typ": *
#import "../../todos.typ": *

#show: show-syntax

#context if (thesis-state.get)().is-standalone {
  set document(title: "Conventions and Notation")
  title()
}


In this chapter, we briefly cover the basic definitions, mathematical conventions, and
notation used throughout this thesis.

We work in (informal) Grothendieck-Tarski set theory. In particular,
- We assume _Tarski's axiom_: every set is an element of some Grothendieck universe $cal(U)$.
- In particular, we postulate an infinite hierarchy of Grothendieck universes $cal(U)_ℓ$
- We call an element of $cal(U)_ℓ$ _ℓ-small_

In general, definitions are implicitly $ℓ$-polymorphic unless stated otherwise.
For example, when we define a category, we really mean an $ℓ$-category with $ℓ$-small hom-sets.
We hence for the most part ignore size issues.

= Families, Sequences, Lists, and Streams

An _($I$-indexed) family_ @nlab:family $icol(a) := (a_i | i ∈ I)$ consists of

- An _index set_ $I$, whose elements are the _indices_ of the family.
  We will sometimes write $cix(icol(a)) := I$.

- For each index $i ∈ I$, an _element_ $a_i$.
  We will sometimes write this as a function application $icol(a) med i$.

Families are considered equal when they have the same index set and agree pointwise.

We will often write an indexed family as $(i ↦ a_i)_(i ∈ I)$ or $(a_i)_(i ∈ I)$,
or even $(i_1 ↦ a_(i_1),...,i_n ↦ a_(i_n))$ for $I = {i_1,...,i_n}$ finite.
In general, we will omit $I$ when clear from context.

We write the empty indexed family as $()$.

We say $icol(a)$ is a _subfamily_ of $icol(b)$, written $icol(a) ⊆ icol(b)$, if
$cix(icol(a)) ⊆ cix(icol(b))$
and
$∀ i ∈ cix(icol(a)), a_i = b_i$.

Given families $icol(a) = (a_i | i ∈ I)$, $icol(b) = (b_j | j ∈ J)$,
we define the _reindexings_ from $icol(b)$ into $icol(a)$ as follows:
$
  hfam(icol(a), icol(b)) := { f : J → I | ∀ j ∈ J . a_(f(j)) = b_j }
$

We note that

- We always have $id_I : hfam(icol(a), icol(a))$

- If $f : hfam(icol(a), icol(b))$ and $g : hfam(icol(b), icol(c))$,
  then $f ∘ g : hfam(icol(a), icol(c))$ (_not_ $g ∘ f$!)

  For clarity, we will write this as $f famcomp g$ to emphasize that $f$ is a reindexing.

This makes the reindexings into a _category_ with objects indexed families and morphisms 
reindexings.

An injective reindexing is called a _thinning_,
while a bijective reindexing is called a _permutation_.
We denote the sets of such reindexings as
$
  hthin(icol(a), icol(b)) & := { f ∈ hfam(icol(a), icol(b)) | f "is injective" } \
  hperm(icol(a), icol(b)) & := { f ∈ hthin(icol(a), icol(b)) | f "is bijective" } \
$

Thinnings model dropping indices, while permutations model reordering.

Both these subsets contain the identity reindexing and are closed under (reverse) composition
(i.e., are wide subcategories of the category of reindexings).
Furthermore, the set of permutations is closed under inverses (which always exist):
$
  ∀ f ∈ hperm(icol(a), icol(b)), f^(-1) ∈ hperm(icol(b), icol(a))
$
That is, the permutations are in fact a _groupoid_.

We define some of the basic operations on indexed families as follows:

- Given indexed families $icol(a) = (a_i | i ∈ I)$, $icol(b) = (b_i | j ∈ J)$,
  we define their _override_ as follows:
  $
    icol(a) ovrd icol(b) = [λ k . site(k ∈ I, a_k, b_k) | k ∈ I ∪ J]
  $

  We note that
  - $() ovrd icol(a) = icol(a) ovrd () = icol(a)$
  - $icol(a) ovrd (icol(b) ovrd icol(c)) = (icol(a) ovrd icol(b)) ovrd icol(c)$

  That is, indexed families form a monoid with the empty family $()$ as identity.
  In particular:

  - $icol(a) ovrd icol(b) = icol(b) ovrd icol(a) <==> ∀ i ∈ I ∩ J . a_i = b_i$
    in which case we write $icol(a) ∪ icol(b)$.

    If $icol(a)$ and $icol(b)$ are in fact disjoint, we write $icol(a) ⊔ icol(b)$.

  When there is no risk of confusion, we will write the override $icol(a) ovrd icol(b)$ as the 
  juxtaposition of families $icol(a) icol(b)$; this admits the familiar notation for
  single-point updates $(x ↦ a)icol(b)$.

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

/*
- We may define the _coproduct_ of two indexed families
  $icol(a) = (a_i | i ∈ I)$,
  $icol(b) = (b_j | j ∈ J)$ using the pointwise map as follows:
  $
    icol(a) + icol(b)
    = (linj i ↦ a_i | i ∈ I) ⊔ (rinj j ↦ b_j | j ∈ J)
  $

  This has projection thinnings
  $
    lthin(icol(a), icol(b)) := (λ i . linj i) : hthin(icol(a) + icol(b), icol(a)) quad quad
    rthin(icol(a), icol(b)) := (λ j . rinj j) : hthin(icol(a) + icol(b), icol(b))
  $

- Likewise, we may define the _product_ of two indexed families
  $icol(a) = (a_i | i ∈ I)$,
  $icol(b) = (b_j | j ∈ J)$ as follows:
  $
    icol(a) × icol(b) = ((i, j) ↦ (a, b) | (i, j) ∈ I × J)
  $
*/

- A _sequence_ $icol(a) = [a_i | i ∈ I]$ is an indexed family $(a_i | i ∈ I)$ where
  - $I = ℕ$ , in which case we call $icol(a)$ a _stream_, or
  - $I = fin(n)$ for some $n ∈ ℕ$, in which case we call $icol(a)$ a _list_ or _$n$-tuple_.

  In general, we will reserve square brackets $[ - ]$ for lists
  (rather than general indexed families), writing

  - $lnil := ()$ for the empty list
  - $[a_0,...,a_(n - 1)]$ for a list of length $n$
  - $[a_0, a_1, a_2, ...]$ for a stream
  - _Comprehensions_ $[f(a) | a ∈ icol(a)] := [f(a_i) | i ∈ I]$

    In general, we will often interpret $ℕ$ and $fin(n)$ as a stream and a list.

  Note that, following the convention in computer science, our sequences are _zero-indexed_.

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
  $
    lnil lcat icol(b) = icol(b) quad quad quad
    (x :: icol(a)) lcat icol(b) = x :: (icol(a) lcat icol(b))
  $

  For $icol(a)$ of length $n$, we can show by induction that
  $
    icol(a) lcat icol(b)
    = [a_0,...,a_(n - 1),b_0, b_1, ...]
    = [λ i . site(i < n, a_i, b_(i - n))]
  $

  In particular, we note that
  $
    lnil lcat icol(a) = icol(a) lcat lnil = icol(a) quad quad quad
    [a] lcat icol(a) = a :: icol(a) quad quad quad
    icol(a) lcat [b] = icol(a) lsnoc b
  $
  $
    icol(a) lcat (icol(b) lcat icol(c)) = (icol(a) lcat icol(b)) lcat icol(c)
  $

- We define the _repetition_ of a list $icol(a)$, written $n · icol(a)$, by induction as follows:
  $
    0 · icol(a) = lnil quad quad quad (n + 1) · icol(a) = icol(a) lcat n · icol(a)
  $

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

  We call two elements in a preorder _equivalent_, written $x ≈ y$, if $x ≤ y$ and $y ≤ x$.

  Where $X$ has a distinguished preorder $≤$, we will often simply say "the preorder $X$."

  We call $≤$ a _partial order_ if all equivalent elements are equal -- i.e., we satisfy
  - _antisymmetry_: $∀ x, y ∈ X . x ≤ y ==> y ≤ x ==> x = y$

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
  Without loss of generality, we may always take $max{a}, min{a} := a$.

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
  Without loss of generality, we may always take $⨆{a}, ⨅{a} := a$.
  #footnote[
    While we could define $⨆ A := min(ubs(A))$ and $⨅ A := max(lbs(A))$ when they exist, 
    we would not be able to satisfy the condition $∀ a . ⨆{a}, ⨅{a} := a$ unless $X$ is a poset,
    as all equivalent elements $a ≈ b$ have the same set of upper and lower bounds.
  ]

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
  - $X$ is a _complete prelattice_ if every subset $A ⊆ X$ has both a meet and a join
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

#definition(name: [dcpo, $ω$cpo])[
  Given a preorder $X$,
  - A subset $A ⊆ X$ is _(upward) directed_  if every pair $a, b ∈ A$ has an upper bound in $A$
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

= Cofinite Quantification

#todo[Forall cofinite]

#todo[Exists cofinite]

#todo[Example: $ℕ$ even]

#todo[Example: $ℕ$ nonzero]

#todo[Example: $ℕ$ zero]

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
