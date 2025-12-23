#import "../../syntax.typ": *
#import "../../todos.typ": *

#show: show-syntax

// TODO: should we put categorical notation up here?

= Categories

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
  - A binary operation, $- med ; -$, 
    mapping each pair of morphisms $f : cal(C)(A, B)$ and $g : cal(C)(B, C)$
    to their _composition_ $f ; g : cal(C)(A, C)$

  Such that:
  - For all $A, B∈ |cal(C)|$, $id_A ; f = f ; id_B = f$
  - For all $f: cal(C)(A, B), g: cal(C)(B, C), h: cal(C)(C, D)$, $(f ; g) ; h = f ; (g ; h)$

  We will sometimes write the set $cal(C)(A, B)$ as $A ahm(cal(C)) B$ or,
  where $cal(C)$ is clear from context, $A -> B$.
]

We follow the convention in computer science and define composition "forwards" as $f ; g$.

/*
If we interpret objects $A, B$ as _states_
and morphisms $f: cal(C)(A, B), g : cal(C)(B, C)$ as _transformations between states_,
then their _sequential composition_
$
  #diagram(cell-size: 15mm, $ A edge(f, ->) & B edge(g, ->) & C $)
$
is precisely $f ; g : cal(C)(A, C)$: the composite path from $A$ to $C$ through $B$.

#todo[nicer introduction to commutative diagrams]

#todo[general principle: as fast as possible, change algebra to geometry!]

Viewing morphisms in a category as diagrams, the laws of a category become graphically obvious:
if the identity transformation from $A$ to $A$ is doing nothing, i.e. the null path, then the
axiom that
$
  id_A ; f = f ; id_B = f
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

#definition(name: "Category of sets")[
  We define the category of sets to have
  objects sets $A$
  and morphisms $f : cset(A, B)$ functions $f : A → B$.

  Composition $f ; g$ is simply (pointwise) composition of functions $g ∘ f$.
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
    such that $f ; g = id_A$ and $g ; f = id_B$.
    //
    If such a morphism exists, it is unique, so we may write it as $f^(-1)$.

    Two objects $A, B ∈ |cal(C)|$ are _isomorphic_, written $A ≈ B$, if there exists
    an isomorphism $f : cal(C)(A, B)$.

  - $f$ is an _epimorphism_ if, for all parallel morphisms $g_1, g_2 : cal(C)(B, X)$,
    $f ; g_1 = f ; g_2$ implies $g_1 = g_2$.
    //
    In this case, we will say $f$ is _epic_.

  - $f$ is a _monomorphism_ if, for all parallel morphisms $h_1, h_2 : cal(C)(X, A)$,
    $h_1 ; f = h_2 ; f$ implies $h_1 = h_2$.
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

= Functors

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
  - $F$ preserves composition: $F (f ; g) = (F f) ; (F g)$
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
_composition_ $F ; G$ as follows:
- $|F ; G| = |G| ∘ |F| : |cal(C)_1| → |cal(C)_3|$
- For all $f : cal(C)_1(A, B)$, $(F ; G) med f = G med (F f) : cal(C)_3(G med (F A), G med (F B))$

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

#definition(name: "Concrete Functor")[
  Given concrete categories $U_cal(V) : cal(V) → cset, U_cal(W) : cal(W) -> cset$,
  a _(strict) concrete functor_ is a functor $F : cal(V) → cal(W)$ such that the following
  diagram commutes#footnote[
    One could weaken this definition by requiring the square to commute only up to
    a natural isomorphism rather than strictly.  For simplicity, all concrete functors
    considered in this thesis will be assumed to be strict.
  ]:
  $
    #diagram(cell-size: 15mm, $ cal(V) edge(F, ->) edge("dr", U_cal(V), ->, label-side: #right) & cal(W) edge("d", U_cal(W), ->, label-side: #left) \
                                                                    & cset $)
  $

  Equivalently,
  for all objects $A, B : |cal(V)|$ and morphisms $f : cal(V)(A, B)$,
  $|F A| = |A|$ and $|F f| = |f|$.
]

Note that, as the composition of two concrete functors is again a concrete functor,
we can form a category $cconc$ of concrete functors
with objects concrete categories $cal(V), cal(W)$
and morphisms $cconc(cal(V), cal(W))$ concrete functors $F: cal(V) → cal(W)$ between them.

= Products

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
    ∀ j : I . ⟨icol(f)⟩^P ; π_j = f_j
  $

  Equivalently, for arbitrary $g : cal(C)(X, P)$, we have that
  $
    (∀ j : I . g ; π_j = f_j) <==> g = ⟨icol(f)⟩^P
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
    Π mb(f) = Π_(i ∈ I)f_i := ⟨π_i^(Π icol(A)) ; f_i⟩_(i ∈ I) : cal(C)(Π icol(A), Π icol(B))
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
  - $F_(hat(icol(A)), x) (f ; g) = F_(hat(icol(A)), x) f ; F_(hat(icol(A)), x) g$
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

== Duality, Coproducts, and Initial Objects

#todo[do this]

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
      ∀ j : I . ι_j ; [f_i]_(i ∈ I) = f_j
    $

    That is, for arbitrary $g : cal(C)(C, X)$, we have that
    $
       (∀ j ∈ I . ι_j ; g = f_j) <==> g = [f_i]_(i ∈ I)
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
    - $Σ_i f_i = ⟨f_i ; ι_i⟩_i : Σ_i A_i → Σ_i B_i$, and, therefore, in particular
    - $Σ [f_1,...,f_n] = ⟨f_1 ; ι_1,..., f_n ; ι_n⟩ : Σ [A_1,...,A_n] → Σ [B_1,...,B_n]$
    - $f_1 + f_2 = ⟨f_1 ; ι_1 , f_2 ; ι_2⟩ : A_1 + A_2 → B_1 + B_2$
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

= Naturality

#definition(name: [Natural transformation])[
  Given functors $F, G : cal(C) → cal(D)$
  a _natural transformation_ $η : F => G$ 
  consists of a family of morphisms $η_A : cal(D)(F A, G A)$,
  indexed by objects $A ∈ |cal(C)|$, such that, //TODO: parenthetical?
  for each morphism $f : cal(C)(A, B)$, we have that
  $η_A ; (G med f) = (F med f) ; η_B$ 
  -- i.e. the following diagram commutes:
  $
    #diagram(cell-size: 15mm, $ 
      F med A edge(η_A, ->) edge("d", F med f, ->) 
      & G med A edge("d", G med f, ->, label-side: #left) 
      \ F med B edge(η_B, ->, label-side: #right) 
      & G med B $)
  $
  We call a diagram of this form a _naturality square_.
]

/*
== Monads and Kliesli Categories

#todo[have this as an example of a premonoidal category]

#todo[
  - Introduce the concept of _strength_ via a strong monad
    (later will have strong Elgot structure so this builds intuition)
    - Every monad over $cset$ is strong, so this is often overlooked
  - define a commutative monad; show monoidal $<=>$ commutative
  - notice the subcategory of pure things; think about it
    - return should be monic or it's not faithful; @moggi-89-monad calls this a
      _computational monad_
    - but this is not necessary for our Freyd case
]
*/

#context if (thesis-state.get)().is-standalone {
  the-bibliography
}