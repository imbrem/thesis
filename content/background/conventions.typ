#import "../../syntax.typ": *
#import "../../todos.typ": *

= Foundations

We work in (informal) Grothendieck-Tarski set theory. In particular,
- We assume _Tarski's axiom_: every set is an element of some Grothendieck universe $cal(U)$.
- In particular, we postulate an infinite hierarchy of Grothendieck universes $cal(U)_ℓ$
- We call an element of $cal(U)_ℓ$ _ℓ-small_
- Definitions are implicitly $ℓ$-polymorphic unless stated otherwise.
  For example, when we define a category, we really mean an $ℓ$-category with $ℓ$-small hom-sets.

/*
=== Finite sets

We define the canonical _finite set with $n$ elements_ $fin(n)$
to consist of the first $n$ natural numbers:
$
  fin(n) := { i ∈ ℕ | i < n }
$
Note that, following the convention in computer science, we start counting from $0 ∈ ℕ$.

/*
We fix a canonical isomorphism
$
  fcanon(m, n) := (λ i . site(i < m, i, i - m))
  : fin((m + n)) ≅ fin(m) + fin(n)
$
*/
*/

= Families

An _($I$-indexed) family_ @nlab:family $icol(a) := (a_i | i ∈ I)$ consists of

- An _index set_ $I$, whose elements are the _indices_ of the family.
  We will sometimes write $cix(icol(a)) := I$.

- For each index $i ∈ I$, an _element_ $a_i$.
  We will sometimes write this as a function application $icol(a) med i$.

We will often write an indexed family as $(i ↦ a_i)_(i ∈ I)$ or $(a_i)_(i ∈ I)$,
or even $(i_1 ↦ a_(i_1),...,i_n ↦ a_(i_n))$ for $I = {i_1,...,i_n}$ finite.
In general, we will omit $I$ when clear from context.

We write the empty indexed family as $()$.

We say $icol(a)$ is a _subfamily_ of $icol(b)$, written $icol(a) ⊆ icol(b)$, if
$cix(icol(a)) ⊆ cix(icol(b))$
and
$∀ i ∈ cix(icol(a)), a_i = b_i$.

/*
Type-theoretically, an indexed collection $(i ↦ a_i)_(i ∈ I)$ is just a dependent function type
$Π i : I . A_i$; set-theoretically, we can model it as a set of pairs ${(i, a_i) | i ∈ I}$
forming the graph of a well-defined function.
*/

Given families $icol(a) = (a_i | i ∈ I)$, $icol(b) = (b_j | j ∈ J)$,
we define the _reindexings_ of $icol(a)$ _along_ $icol(b)$ as follows:
$
  hfam(icol(a), icol(b)) := { f : J → I | ∀ j ∈ J . a_(f(j)) = b_j }
$

We note that

- We always have $id_I : hfam(icol(a), icol(a))$

- If $f : hfam(icol(a), icol(b))$ and $g : hfam(icol(b), icol(c))$,
  then $f ∘ g : hfam(icol(a), icol(c))$ (_not_ $g ∘ f$!)

  For clarity, we will write this as $f famcomp g$ to emphasize that $f$ is a reindexing.

An injective reindexing is called a _thinning_,
while a bijective reindexing is called a _permutation_.
We denote the sets of such reindexings as
$
  hthin(icol(a), icol(b)) & := { f ∈ hfam(icol(a), icol(b)) | f "is injective" } \
  hperm(icol(a), icol(b)) & := { f ∈ hthin(icol(a), icol(b)) | f "is bijective" } \
$

Both these subsets contain the identity reindexing and are closed under (reverse) composition.
Furthermore, the set of permutations is closed under inverses (which always exist):
$
  ∀ f ∈ hperm(icol(a), icol(b)), f^(-1) ∈ hperm(icol(b), icol(a))
$

/*
TODO: separate _ordered_ collection section... or just list...

If $I$ and $J$ are equipped with a preorder, we say a reindexing $f : hfam(icol(a), icol(b))$ is
- _order-preserving_ or _monotone_ if $∀ j sle(J) j' . f(j) sle(I) f(j')$
- _order-reflecting_ if $∀ j, j' . f(j) sle(I) f(j') ⇒ j sle(J) j'$
- _order-embedding_ if it is both monotone and reflecting,
  i.e. if $∀ j, j' . j sle(J) j' <==> f(j) sle(I) f(j')$
*/

We define some of the basic operations on indexed families as follows:

- Given indexed families $icol(a) = (a_i | i ∈ I)$, $icol(b) = (b_i | j ∈ J)$,
  we define their _override_ as follows:
  $
    icol(a) ovrd icol(b) = [λ k . site(k ∈ I, a_k, b_k) | k ∈ I ∪ J]
  $

  We note that
  - $lnil ovrd icol(a) = icol(a) ovrd lnil = icol(a)$
  - $icol(a) ovrd (icol(b) ovrd icol(c)) = (icol(a) ovrd icol(b)) ovrd icol(c)$
  - $icol(a) ovrd icol(b) = icol(b) ovrd icol(a) <==> ∀ i ∈ I ∩ J . a_i = b_i$
    in which case we write $icol(a) ∪ icol(b)$.

    If $icol(a)$ and $icol(b)$ are in fact disjoint, we write $icol(a) ⊔ icol(b)$.


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
  $icol(a)[J] ⊔ (icol(a) sdiff J) = (icol(a) sdiff J) ⊔ icol(a)[J] = icol(a)$.

/*
- Given a function $f$, we define the pointwise map of a family $icol(a)$ to be given by
  $
    f cmap [a_i | i ∈ I] = [f med a_i | i ∈ I]
  $

  This satisfies the usual properties of a functor:

  - $id cmap icol(a) = icol(a)$
  - $(g ∘ f) cmap icol(a) = g cmap (f cmap icol(a))$

- Likewise, we define the _application_ of two families $icol(f), icol(a)$ as follows:
  $
    [f_i | i ∈ I] capp [a_j | j ∈ J] = [f_i med a_i | i ∈ I ∩ J]
  $

- And the _zip_ of two families $icol(a), icol(b)$ as follows:
  $
    [a_i | i ∈ I] czip [b_j | j ∈ J] = [(a_i, b_i) | i ∈ I ∩ J]
  $
*/

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

= Lists, Streams, and Sequences

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

#context if (thesis-state.get)().is-standalone {
  the-bibliography
}