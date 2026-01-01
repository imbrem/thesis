#import "../../syntax.typ": *
#import "../../todos.typ": *

#show: show-syntax

#context if (thesis-state.get)().is-standalone {
  set document(title: "Basic (Enriched) Category Theory")
  title()
}

#quote(attribution: [
  Gregory Moore, Nathan Seiberg. "Classical and quantum conformal field theory." @moore-89-conformal
])[
  We will need to use some very simple notions of category theory,
  an esoteric subject noted for its difficulty and irrelevance.
]

= Preliminaries

== Categories

We will begin with a brief overview of basic category theory, in which we will take the opportunity
to fix notations. Recall the definition of a category $cal(C)$:

#definition(name: "Category")[
  A category $cal(C)$ is given by:
  - A set of _objects_ $|cal(C)| ∈ cal(U)_ℓ$
    #footnote[
      A category with objects in $cal(U)_ℓ$ is called _$ℓ$-small_.
      For the rest of this paper, we will work polymorphically in $ℓ$,
      and hence leave it unspecified.
    ]
  - For each pair of objects $A, B in |cal(C)|$, a set of _morphisms_ $cal(C)(A, B)$.
    We call this set a _hom-set_.
  - For each object $A in |cal(C)|$, an _identity morphism_ $id_A : cal(C)(A, A)$
  - A binary operation, $- med cc -$,
    mapping each pair of morphisms $f : cal(C)(A, B)$ and $g : cal(C)(B, C)$
    to their _composition_ $f cc g : cal(C)(A, C)$

  Such that:
  - For all $A, B∈ |cal(C)|$, $id_A cc f = f cc id_B = f$
  - For all $f: cal(C)(A, B), g: cal(C)(B, C), h: cal(C)(C, D)$, $(f cc g) cc h = f cc (g cc h)$

  We will sometimes write the set $cal(C)(A, B)$ as $A ahm(cal(C)) B$ or,
  where $cal(C)$ is clear from context, $A -> B$.
]

We follow the convention in computer science and define composition "forwards" as $f cc g$.

/*
If we interpret objects $A, B$ as _states_
and morphisms $f: cal(C)(A, B), g : cal(C)(B, C)$ as _transformations between states_,
then their _sequential composition_
$
  #diagram(cell-size: 15mm, $ A edge(f, ->) & B edge(g, ->) & C $)
$
is precisely $f cc g : cal(C)(A, C)$: the composite path from $A$ to $C$ through $B$.

#todo[nicer introduction to commutative diagrams]

#todo[general principle: as fast as possible, change algebra to geometry!]

Viewing morphisms in a category as diagrams, the laws of a category become graphically obvious:
if the identity transformation from $A$ to $A$ is doing nothing, i.e. the null path, then the
axiom that
$
  id_A cc f = f cc id_B = f
$
becomes the (trivial) equation on diagrams
$
  #diagram(cell-size: 15mm, $ A edge(f, ->) & B $)
  quad = quad
  #diagram(cell-size: 15mm, $ A edge(f, ->) & B $)
  quad = quad
  #diagram(cell-size: 15mm, $ A edge(f, ->) & B $)
$
Likewise, the associativity axiom becomes the (trivial) equation
$
  #diagram(cell-size: 15mm, $ A edge(f, ->) & B edge(g, ->) & C edge(h, ->) & D $)
$
*/

#todo[
  Categories we've already defined:
  - $ms("Set")$
  - $ms("PFun")$
  - $ms("Rel")$
  - $ms("PreOrd")$
  - $ms("Poset")$
]

#definition(name: "Category of sets")[
  We define the category of sets to have
  objects sets $A$
  and morphisms $f : cset(A, B)$ functions $f : A → B$.

  Composition $f cc g$ is simply (pointwise) composition of functions $g ∘ f$.
]

#definition(name: "Category of preorders")[
  We define the category of preorders to have objects _preordered sets_ $A$
  (equipped with preorders $scripts(≤)_A$)
  and morphisms $f: cpreord(A, B)$ _monotone_ functions $f: A → B$; i.e. functions such that
  $
    ∀ a, b : A . a scripts(≤)_A b ==> f(a) scripts(≤)_B f(b)
  $
]

#definition(name: "Category of posets")[
  We define the category of posets to have objects _partially-ordered sets_ $A$
  (equipped with partial orders $scripts(≤)_A$)
  and morphisms $f: cposet(A, B)$ _monotone_ functions $f: A → B$; i.e. functions such that
  $
    ∀ a, b : A . a scripts(≤)_A b ==> f(a) scripts(≤)_B f(b)
  $
]

#todo[
  the category of posets is a _full subcategory_ of the category of preorders;
  versus a _wide_ subcategory
]

#todo[category of reindexings]

#todo[_subcategory_ of thinnings, permutations; this is a _wide_ subcategory]

#definition(name: "Isomorphism, Epimorphism, Monomorphism")[
  Given a morphism $f : cal(C)(A, B)$,

  - $f$ is an _isomorphism_ if there exists an _inverse morphism_ $g : cal(C)(B, A)$
    such that $f cc g = id_A$ and $g cc f = id_B$.
    //
    If such a morphism exists, it is unique, so we may write it as $f^(-1)$.

    Two objects $A, B ∈ |cal(C)|$ are _isomorphic_, written $A ≈ B$, if there exists
    an isomorphism $f : cal(C)(A, B)$.

  - $f$ is an _epimorphism_ if, for all parallel morphisms $g_1, g_2 : cal(C)(B, X)$,
    $f cc g_1 = f cc g_2$ implies $g_1 = g_2$.
    //
    In this case, we will say $f$ is _epic_.

  - $f$ is a _monomorphism_ if, for all parallel morphisms $h_1, h_2 : cal(C)(X, A)$,
    $h_1 cc f = h_2 cc f$ implies $h_1 = h_2$.
    //
    In this case, we will say $f$ is _monic_.
]

#todo[identification of isomorphic objects]

In $cset$, a function $f: A → B$ is
- an epimorphism iff it is _surjective_;
- a monomorphism iff it is _injective_;
- an isomorphism iff it is a _bijection_.

While in $cset$, any morphism which is both surjective and injective is in fact a bijection,
it is _not_ generally the case that a morphism which is both epic and monic is an isomorphism!

#todo[epis, monos, and isos are always subcategories]

== Functors and Natural Transformations

#todo[
  We want to relate categories to each other, and to themselves...

  How to explain why we would want operations like the tensor product in general to be functorial,
  since we haven't yet _defined_ tensor products?
]

#todo[
  We want to talk about "sets with extra structure":
  - Preorders
  - Partially ordered sets
  - Monoids
]

#definition(name: "Functor")[
  Given categories $cal(C), cal(D)$, a _functor_ $F : cal(C) → cal(D)$ consists of:
  - A mapping on objects $|F| ∈ |cal(C)| → |cal(D)|$. We often simply write $|F|(A)$ as $F A$.
  - A mapping from $cal(C)$-morphisms $f : cal(C)(A, B)$
    to $cal(D)$-morphisms $F f : cal(D)(F A, F B)$
  such that
  - $F$ preserves identities: $F id_A = id_(F A)$
  - $F$ preserves composition: $F (f cc g) = (F f) cc (F g)$
]

#todo[_forgetful functor_ from $cposet$ to $cset$]

#todo[_forgetful functor_ from $cfam$ to $cset$]

#todo[_forgetful functor_ from $cperm$ to $cthin$ to $cfam$]

#todo[define a full functor]

In general,
- We say a functor $F$ is _faithful_ if its action on morphisms is _injective_; i.e.,
  $
    ∀ f, g : cal(C)(A, B) . F f = F g <==> f = g
  $

#todo[full and faithful iff bijection on hom-sets]

- A functor $F : cal(V) → cal(V)$ is _identity on objects_ if $|F| = id_(|cal(V)|)$.

#todo[the first one is _full_, but _not_ faithful]

#todo[the other two are]

#todo[injections are sort of forgetful faithful functors]

#todo[functors can also _add_ structure: see, from $cset$ to $cposet$]

#todo[note: _this_ one is faithful]

#todo[in fact, these functors form an _adjunction_; but we'll talk about that later, maybe...]

Given functors $F : cal(C)_1 -> cal(C)_2$ and $G : cal(C)_2 -> cal(C)_3$, we may define their
_composition_ $F cc G$ as follows:
- $|F cc G| = |G| ∘ |F| : |cal(C)_1| → |cal(C)_3|$
- For all $f : cal(C)_1(A, B)$, $(F cc G) med f = G med (F f) : cal(C)_3(G med (F A), G med (F B))$

Furthermore, for an arbitrary category $cal(C)$, we may define the _identity functor_ $id_cal(C)$
as mapping objects and morphisms to themselves. In particular, this equips the set of categories
itself with the structure of a category, the _category of categories_ $ms("Cat")$, as follows:

#definition(name: "Category of categories")[
  The category of categories
  #footnote[
    Again, we actually define the category $ms("Cat")_ℓ$ of $ℓ$-small categories, with
    $ms("Cat")$ corresponding to the category of small categories $ms("Cat")_0$
  ]
  $ms("Cat")$ has
  - Objects $|ms("Cat")|$ categories
  - Morphisms $ms("Cat")(cal(C), cal(D))$ functors $F : cal(C) → cal(D)$
]

#definition(name: [Natural transformation])[
  Given functors $F, G : cal(C) → cal(D)$
  a _natural transformation_ $η : F => G$
  consists of a family of morphisms $η_A : cal(D)(F A, G A)$,
  indexed by objects $A ∈ |cal(C)|$, such that, //TODO: parenthetical?
  for each morphism $f : cal(C)(A, B)$, we have that
  $η_A cc (G med f) = (F med f) cc η_B$
  -- i.e. the following diagram commutes:
  $
    #diagram(cell-size: 15mm, $ F med A edge(η_A, ->) edge("d", F med f, ->) & G med A edge("d", G med f, ->, label-side: #left) \
       F med B edge(η_B, ->, label-side: #right) & G med B $)
  $
  We call a diagram of this form a _naturality square_.

  #todo[natural isomorphisms]
]

#todo[functor category]

#todo[equivalence of categories]

== Concrete Categories

#todo[
  A lot of categories are just "sets + structure"; we formalize this notion
]

#definition(name: "Concrete Category")[
  A _concrete category_ $cal(V)$ is a category equipped with a faithful functor
  $U : cal(V) → cset$, called the _underlying-set functor_.

  Given an object $A ∈ |cal(V)|$, we call $|A| := U med A$ the _underlying set_ or _carrier_ of $A$.

  Likewise, given a morphism $f : cal(V)(A, B)$, we call $|f| := U med f : |A| → |B|$ the
  _underlying function_ of $f$.
]

Where there is no risk of confusion,
we will freely identify $|A|$ with $A$ and $|f|$ with $f$,
allowing abuses of notation like
$(a ∈ A) := (a ∈ |A|)$
and
$f(a) := |f|(a) ∈ B$
for $f : cal(V)(A, B)$.

In particular, as $U$ is faithful, given $f, g : cal(V)(A, B)$, we have that $f = g <==> |f| = |g|$.
Equivalently, morphisms in a concrete category are determined by their action
on elements of the source carrier: $f = g$ if and only if
$∀ a ∈ A . f(a) = g(a)$.

#todo[Notion of a substructure; in general, translation between structures]

#definition(name: "Concrete Functor")[
  Given concrete categories $U_cal(V) : cal(V) → cset, U_cal(W) : cal(W) -> cset$,
  a _(strict) concrete functor_ is a functor $F : cal(V) → cal(W)$ such that the following
  diagram commutes#footnote[
    One could weaken this definition by requiring the square to commute only up to
    a natural isomorphism rather than strictly.  For simplicity, all concrete functors
    considered in this thesis will be assumed to be strict.
    #todo[General: _weak_ vs _strict_ concept]
  ]:
  $
    #diagram(
      cell-size: 15mm,
      $ cal(V) edge(F, ->) edge("dr", U_cal(V), ->, label-side: #right) //
        & cal(W) edge("d", U_cal(W), ->, label-side: #left) \
        & cset $,
    )
  $

  Equivalently,
  for all objects $A, B : |cal(V)|$ and morphisms $f : cal(V)(A, B)$,
  $|F A| = |A|$ and $|F f| = |f|$.
]

Note that, as the composition of two concrete functors is again a concrete functor,
we can form a category $cconc$ of concrete functors
with objects concrete categories $cal(V), cal(W)$
and morphisms $cconc(cal(V), cal(W))$ concrete functors $F: cal(V) → cal(W)$ between them.

== Products and Coproducts

#definition(name: "Terminal Object")[
  An object $X ∈ |cal(C)|$ is _terminal_ if for every object $A ∈ |cal(C)|$,
  there exists a _unique_ morphism $!_A : cal(C)(A, X)$.

  We note that terminal objects are unique up to _unique_ isomorphism:
  if $X$ and $X'$ are terminal objects, then $X ≈ X'$.
  //
  Hence, in any $cal(C)$ with a terminal object, we may choose a distinguished terminal object
  $tunit_cal(C) ∈ |cal(C)|$ without loss of generality; where there is no risk of confusion, we
  will often simply write $tunit ∈ |cal(C)|$.
]

#definition(name: "Product")[
  Given a family of objects $icol(A) = (A_i | i ∈ I)$ indexed by a set $I$,
  we say that an object $P∈ |cal(C)|$ is their _product_ if
  there exist morphisms $π_i^P : cal(C)(P, A_i)$ such that,
  for every object $X ∈ |cal(C)|$,
  given a family of morphisms $icol(f) = (f_i : cal(C)(X, A_i) | i ∈ I)$,
  there exists a _unique_ morphism $⟨icol(f)⟩^P : cal(C)(X, P)$
  (the _product_ of the $f_i$)
  such that
  $
    ∀ j : I . ⟨icol(f)⟩^P cc π_j = f_j
  $

  Equivalently, for arbitrary $g : cal(C)(X, P)$, we have that
  $
    (∀ j : I . g cc π_j = f_j) <==> g = ⟨icol(f)⟩^P
  $

  Where it is unambiguous from context, we omit the superscript $P$ and
  write $π_i : cal(C)(P, A_i)$ for the projections
  and $⟨icol(f)⟩$, $⟨f_i⟩_(i ∈ I)$, $⟨f_i⟩_i$, or $⟨f_1,...,f_n⟩$ for the product.

  We note that the product $P$ of a family of objects $A_i$ is unique up to isomorphism;
  that is, if $P$ and $P'$ are products of $A_i$, then $P ≈ P'$.

  In particular, for each family of objects $icol(A) = ( A_i | i ∈ I )$,
  we may choose a distinguished product  $Π icol(A)$ whenever one exists.
  //
  As for morphisms, we write $Π_(i ∈ I) A_i := Π (A_i | i ∈ I)$.

  Since an object is the product of the empty family if and only if it is terminal,
  if such a product exists, we may without loss of generality assume that $Π [] = tunit$.
]

In general, where the appropriate products exist, we write

- $A × B := Π (lb("l") ↦ A, lb("r") ↦ B)$

- For $n ∈ ℕ$, $A^n := Π (n · [A])$

- Given objects $icol(A) = (A_i | i ∈ I)$ , $icol(B) = (B_i | i ∈ I)$,
  and morphisms $icol(f) = (f_i : cal(C)(A_i, B_i) | i ∈ I)$,
  we define
  $
    Π mb(f) = Π_(i ∈ I)f_i := ⟨π_i^(Π icol(A)) cc f_i⟩_(i ∈ I) : cal(C)(Π icol(A), Π icol(B))
  $

- Likewise, given $f: A_1 → B_1$, $g : A_2 → B_2$, we define
  - $f × g := Π (lb("l") ↦ f, lb("r") ↦ g)$
  - $f × A_2 := f × id_(A_2)$
  - $A_1 × g := id_(A_1) × g$

#definition(name: "Natural Family")[
  Fix categories $cal(C), cal(D)$ and a set of _indices_ $I$.

  Given a family of $cal(D)$-objects $F_icol(A) ∈ |cal(D)|$
  indexed by $icol(A) := (A_i | i ∈ I)$ where each $A_i ∈ cal(C)$ is a $cal(C)$-object,
  we say $F$ is _functorial in $x ∈ I$_ if,
  for each choice of objects $hat(icol(A)) := (A_i | i ∈ I sdiff {x})$,
  and morphism $f : cal(C)(X, Y)$
  there exists a canonical morphism
  $F_(hat(icol(A)), x) med f : F_(hat(icol(A))[x := X]) → F_(hat(icol(A))[x := B])$
  such that $F_(hat(icol(A)), x): cal(C) → cal(D)$ is a functor; that is,
  - $F_(hat(icol(A)), x) id_(A_x) = id_(F_icol(A))$
  - $F_(hat(icol(A)), x) (f cc g) = F_(hat(icol(A)), x) f cc F_(hat(icol(A)), x) g$
    for $f : cal(C)(X, Y), g : cal(C)(Y, Z)$.

  Given a family of morphisms $η_icol(A) : cal(D)(F_icol(A), G_icol(A))$,
  for $F, G$ functorial in $x ∈ I$,
  we say $η$ is _natural_ in $x$ if,
  for each choice of objects $hat(icol(A)) := (A_i | i ∈ I sdiff {x})$,
  for each morphism $f : cal(C)(X, Y)$ in $cal(C)$,
  the expected naturality square commutes
  $
    #diagram(cell-size: 15mm, $ F_(hat(icol(A))[x := X]) edge(η_(hat(icol(A))[x := X]), ->) edge("d", F med f, ->)
    & G_(hat(icol(A))[x := X]) edge("d", G med f, ->, label-side: #left) \
    F_(hat(icol(A))[x := Y]) edge(η_(hat(icol(A))[x := Y]), ->, label-side: #right)
    & G_(hat(icol(A))[x := Y]) $)
  $

  Equivalently, the family
  $η_(hat(icol(A)), x, X) := η_(hat(icol(A))[x := X])$
  is a natural transformation $η_(hat(icol(A)), x) : F_(hat(icol(A)), x) => G_(hat(icol(A)), x)$.
]

#todo[every thinning induces a map on the product]

#todo[every permutation, an isomorphism]

#todo[Do we discuss naturality here? Note the thinning/permutation cases are also natural...]

There exist canonical isomorphisms:
- $A × B ≈ B × A$
- $A × tunit ≈ A ≈ tunit × A$
- $A × (B × C) ≈ Π [A, B, C] ≈ (A × B) × C$
- $Π (X :: icol(A)) ≈ X × Π icol(A)$ for a sequence $icol(A)$
- $Π (icol(A) lsnoc X) ≈ Π icol(A) × X$ for a list $icol(A)$
- $Π [A] ≈ A$
- $Π (icol(A) lcat icol(B)) ≈ Π icol(A) × Π icol(B)$
- $A^(m + n) ≈ A^m × A^n$

#definition(name: "Cartesian Category")[
  A category $cal(C)$ is _cartesian_ if it has all finite products;
  i.e. all products $Π icol(A)$ where $icol(A)$ is finite.

  Note that it suffices for $cal(C)$ to have
  a terminal object $tunit$
  and all binary products $A × B$.
]

#todo[$cset$ has the usual products...]

#todo[$cpreord$ and $cposet$ have the same products!]

#todo[as do monoids, lattices, etc...]

#todo[there's a pattern here:]

#definition(name: "Concretely Cartesian Category")[
  A concrete category $cal(V)$ is _(strict) concretely cartesian_
  if its underlying-set functor  $U : cal(V) -> cset$
  preserves finite products;
  i.e., we have
  $
    ∀ icol(A) "finite". |Π A_i| = Π_i|A_i|
  $
]

/*

A coproduct, then, is just the dual notion to a product:

#definition(name: "Coproduct")[
  Given a family of objects $A_i ∈ |cal(C)|$ for some indexing set $I$,
  we say that an object $C∈ |cal(C)|$ is their _coproduct_ if there exist:
  - Morphisms $ι_i : cal(C)(A_i, C)$ and
  - For each object $X ∈ |cal(C)|$,
    given a family of morphisms $f_i : cal(C)(A_i, X)$ for each $i ∈ I$,
    a _unique_ morphism $[f_i]_(i ∈ I) : cal(C)(C, X)$
    (the _coproduct_ of the $f_i$)
    such that
    $
      ∀ j : I . ι_j cc [f_i]_(i ∈ I) = f_j
    $

    That is, for arbitrary $g : cal(C)(C, X)$, we have that
    $
       (∀ j ∈ I . ι_j cc g = f_j) <==> g = [f_i]_(i ∈ I)
    $

  We note that the coproduct $C$ of a family of objects $A_i$ is unique up to isomorphism;
  that is, if $C$ and $C'$ are coproducts of $A_i$, then $C ≈ C'$.
  Furthermore, an object is the product of the empty family if and only if it is initial.

  We say a category $cal(C)$ is _cocartesian_ if it has _all finite coproducts_;
  i.e. if there exists a function
  $Σ : tlist(|cal(C)|) → |cal(C)|$ such that
  - For $L = [A_1,...,A_n]$, $Σ L$ is a coproduct of $A_i$, and, in particular,
  - $Σ []$ is equal to the initial object $tzero$

  In general, we write
  - $Σ_i A_i := Σ [A_1,...,A_n]$
  - $A + B := Σ [A, B]$
  - For $n ∈ ℕ$, $ntag(n, A) = Σ [A,...,A]$ ($n$ copies of $A$)
  - For morphisms $f_i : cal(C)(A_i, B_i)$ for arbitrary $i ∈ I$,
    - $Σ_i f_i = ⟨f_i cc ι_i⟩_i : Σ_i A_i → Σ_i B_i$, and, therefore, in particular
    - $Σ [f_1,...,f_n] = ⟨f_1 cc ι_1,..., f_n cc ι_n⟩ : Σ [A_1,...,A_n] → Σ [B_1,...,B_n]$
    - $f_1 + f_2 = ⟨f_1 cc ι_1 , f_2 cc ι_2⟩ : A_1 + A_2 → B_1 + B_2$
  - In particular, for $f : cal(C)(A, B)$ and objects $C$, we define
    - $f + C = f + id_C : A + C → B + C$, and
    - $C + f = id_C + f : C + A → C + B$
]

Similarly to products, coproducts satisfy some basic algebraic properties

- $A + B ≈ B + A$

- $A + tzero ≈ A$

- $A + Σ L ≈ Σ (A :: L)$

- $Σ [A] ≈ A$

- $Σ L + Σ L' ≈ Σ (L · L')$

- $A + (B + C) ≈ Σ [A, B, C] ≈ (A + B) + C$

- Likewise, $ntag(m, A) + ntag(n, A) ≈ ntag(m + n, A)$

*/

= Enriched Categories

#todo[
  Rework plan:
  - Our goal is a _categorical semantics of imperative programming_
  - Standard:
    - Program fragment: morphisms
    - Textual composition: composition of various kinds
      - Sequential $=>$ Vertical
      - Data $=>$ Horizontal
      - Control-flow $=>$ Coproducts + Iterativity
    - But, we don't just study equality, we study refinement
  - We need a way to compare refinements
  - $=>$ We need a partial order on refinements _compatible_ with our categorical structure
  - $cal(V)$-enrichment for $cal(V)$ concretely cartesian:
    how to equip hom-sets with structure compatible w/ category theory
    - categories: compatible with composition
    - other stuff: compatible with that stuff
    - give definition
    - can be more general than "sets with structure;" we won't
    - quickly: change-of-basis
  - Direct approach: enrich with $cal(V) = cposet$; get the _2-posets_
  - But we might be interested in other things too/instead
    - More restrictive than posets: e.g. _lattices_
    - Unrelated: e.g. _abelian groups_ (add quantum pointer here)
  - In general, want to _project out_ the structure we _need_
    - A $cal(V)$-category is _equipped with_ structure $cal(W)$
      if there's a canonical concretely cartesian functor s.t. the nice diagram commutes;
      note this _implies_ faithfulness!
    - Note, for a $cal(V)$-categort $cal(C)$:
      - $cal(C)$ is always equipped with $cal(V)$
      - $cal(C)$ is always $cset$ equipped; i.e. equipped with nothing
      - $cal(C)$ can _always_ be equipped with a partial order: the _discrete_ partial order
      - The equipment is treated as structure on $cal(C)$, _not_ structure on $cal(V)$ (!!!)
]

/*
For the rest of this thesis,
$cal(V)$ will range over concretely cartesian categories unless otherwise specified.
*/

#definition(name: [$cal(V)$-enriched category])[
  Given a concretely cartesian category $cal(V)$,
  a $cal(V)$-enriched category $cal(C)$, or _$cal(V)$-category_, consists of
  - An set of objects $|cal(C)|$
  - For each pair of objects $A, B ∈ |cal(C)|$, a _hom-object_ $cal(C)(A, B) ∈ |cal(V)|$
  - For each object $A ∈ |cal(C)|$, an _identity morphism_ $id_A : cal(C)(A, B)$
  - For each triple of objects $A, B, C ∈ |cal(C)|$, a _composition morphism_
    $
      (cc)_(A, B, C) : cal(V)(cal(C)(A, B) × cal(C)(B, C), cal(C)(A, C))
    $
]

#todo[add (foot)note about more general notion of $cal(V)$ enrichment for $cal(V)$ monoidal]

#todo[More generally, we can do change of basis w.r.t. any concart-functor]

We note that every $cal(V)$-category $cal(C)$ induces an ordinary category $U cal(C)$
with:
- The same set of objects $|U cal(C)| = |cal(C)|$
- Hom-sets $(U cal(C))(A, B) = U(cal(C)(A, B))$.

  In particular, as $U : cal(V) → cset$ is faithful, every $g ∈ (U cal(C))(A, B)$
  can be written in a unique way as an application $U f$ for $f : cal(C)(A, B)$.
- Composition given by
  $
    ∀ f : (U cal(C))(A, B), g : (U cal(C))(B, C) . f cc g = (U (cc)_(A, B, C)) (f, g)
  $

#todo[pull up concart-functor to background]

In fact, this construction can be generalized quite readily:

#definition(name: "Concretely Cartesian Functor")[
  Let $F : cal(V) → cal(W)$ be a functor between concretely cartesian categories
  $(cal(V), U_cal(V))$ and $(cal(W), U_cal(W))$. We say $F$ is _concretely cartesian_ if
  - $F$ preserves erasure: $F cc U_cal(W) = U_cal(V)$
  - $F$ preserves finite products: $∀ [A_1,...,A_n] . F (Π [A_1,...,A_n]) = Π [F A_1,...,F A_n]$

  Note in particular that the erasure $U : cal(V) → cset$
  is always a concretely cartesian functor.
]

#todo[
  Neel says ok for real definition _but_ we suppress notation and pretend everything is strict;
  and also most examples are actually strict this is really just for $cal(V) × cal(W)$
]

This allows us to define the _change of basis_ of a $cal(V)$-category along a
concretely cartesian functor as follows:

#definition(name: "Change of Basis")[
  Given a concretely cartesian functor $F : cal(V) → cal(W)$ and a $cal(V)$-category $cal(C)$,
  we define its _change of basis_ $F cal(C)$ to be the $cal(W)$-category with
  - Objects $|F cal(C)| = |cal(C)|$
  - Hom objects $F cal(C)(A, B) = F(cal(C)(A, B))$
  - Identity morphisms $id_A^(F cal(C)) = id_A^(cal(C))$
  - Composition morphisms
    $
      (cc)_(A, B, C)^(F cal(C)) = (F × F) cc (cc)_(A, B, C)^(cal(C))
    $
]

We will often consider two particularly important cases:

- A $cset$-category $cal(C)$ is precisely an ordinary category
- A $ms("Pos")$-category $cal(C)$, i.e. a _poset-enriched category_ or _2-poset_,
  is simply a category in which
  - Each hom-set $cal(C)(A, B)$ is equipped with a partial order
  - Composition respects this partial order, i.e.,
    for all $f_1, f_2 : cal(C)(A, B)$, $g_1, g_2 ∈ cal(C)(B, C)$,
    $
      f_1 ≤ f_2 ∧ g_1 ≤ g_2 => (f_1 cc g_1) ≤ (f_2 cc g_2)
    $

Throughout the rest of this section, we fix a concretely cartesian category $cal(V)$.

#definition(name: [$cal(V)$-functor])[
  Given $cal(V)$-categories $cal(C), cal(D)$, a $cal(V)$-functor consists of
  - A mapping on objects $|F| ∈ |cal(C)| → |cal(D)|$
  - For each pair of objects $A, B ∈ |cal(C)|$, a $cal(V)$-morphism
    $
      F_(A, B) : cal(V)(cal(C)(A, B), cal(D)(F A, F B))
    $
    inducing an action on morphisms $f : cal(C)(A, B)$ by $F f = F_(A, B) f$.
]

Similarly to before,
- A $cset$-functor $cal(C)$ is precisely an ordinary functor
- A $ms("Pos")$-functor $F : cal(C) → cal(D)$... #todo[this]

#todo[just as for regular functors, we can compose $cal(V)$-functors, and there's an identity...]

#definition(name: [Category of $cal(V)$-categories])[
  The category of $cal(V)$-categories $cal(V)ms("Cat")$ has
  - Objects $|cal(V)ms("Cat")|$ $cal(V)$-categories
  - Morphisms $cal(V)ms("Cat")(cal(C), cal(D))$ $cal(V)$-functors $F : cal(C) → cal(D)$
]

#todo[
  and in particular, change-of-basis $F : cal(V) → cal(W)$
  induces $F_* : cal(V)ms("Cat") → cal(W)ms("Cat")$
]

#todo[
  do this better...
]

In general, we can recover the standard category-theoretic definitions of a concept by taking $cal(V) = cset$.
Often, many definitions for $cal(V)$-categories are in fact identical;
in particular, 
the definitions for terminal objects, initial objects, products and coproducts are exactly the same,
so we will not repeat them.

#context if (thesis-state.get)().is-standalone {
  the-bibliography
}
