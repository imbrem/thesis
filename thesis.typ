#import "@preview/wordometer:0.1.5": word-count
#show: word-count.with(exclude: (<no-wc>, <appendix>))

#let production = false;

#import "thesis-template.typ": *
#import "todos.typ": *

#import "syntax.typ": *

#show: show-syntax

#show ref: it => {
  let el = it.element
  if el == none or el.func() != figure {
    it
  } else {
    link(el.location(), el.supplement)
  }
}

// TODO: think of a better way to go fix ∅...
// #show math.equation: set text(font: "STIX Two Math")

#set text(lang: "en")

#set heading(numbering: "1.")

#show heading.where(level: 0): set heading(supplement: [Chapter])

#set document(
  title: [
    Categorical imperative programming
    //: type theory, refinement, and semantics for SSA
  ],
  author: "Jad-Elkhaleq Ghalayini",
  date: datetime(day: 12, month: 1, year: 2026),
)

#align(center + horizon)[
  #title()

  *Type theory, refinement, and semantics for SSA*

  \

  \

  #context document.author.at(0)

  \

  \

  #context document.date.display("[month repr:long] [year]")

  \

  \


  #image("ucam-cs-colour.svg", width: 15em)

  \

  \

  \

  #stats-box(production)
]

#pagebreak()

#statement-of-originality

#todo[

  We should factor this template, and have a global TODOs list, maybe outside the document...

  What's the right way to format this?

  Do we put the acknowledgements here or after the abstract?

]

#todo[go make a proper listing function for code...]

#todo[go follow the outline I came up with with Neel...]

#pagebreak()

#align(center + horizon)[
  Is _this_ abstract enough?
  #todo[Actually write an abstract]
]

#pagebreak()

#outline()

#pagebreak()

#(thesis-state.update)(body-state)

= Introduction

#todo[
  TFW I need a thesis statement
]

= Static Single Assignment (SSA) <chap-ssa>

#[
  #set heading(offset: 1)
  #include "content/static-single-assignment.typ"
]

= Conventions and Notation

#[
  #set heading(offset: 1)
  #include "content/background/conventions.typ"
]

= Type-Theoretic SSA <ssa-type>

== Typing Rules

=== Types and Contexts

#import "content/rules/types.typ": *

#todo[introduce _cartesian_ types]

#fig-ty-grammar

#todo[introduce _weakening_ of types]

#fig-r-twk

#todo[$sle(ms("X"))$ is always a near-prelattice]

#lemma[
  If $sle(ms("X"))$ is a near-lattice, so is $tyle(ms("X"))$
]

/*
#todo[Has joins when $ms("X")$ has _bounded_ joins]

#todo[Has meets when $ms("X")$ has _bounded_ meets]

#fig-ty-lattice
*/

#todo[Grammar for (label) contexts]

#todo[Should we repeat the rules and such here?]

#todo[
  Contexts over $sty(ms("X"))$ of the form $Γ, ms("L")$ are isomorphic to $lb("T"), lb("L")$;
  "concepts with attitude"
]

#todo[
  not quite the same as distinguishing $lb("T"), lb("L")$, since _these_ have different variance
]

#fig-r-cwk

=== Expressions

#todo[introduce concept of a function space]

#todo[fix notation for function space judgement]

#todo[IMPORTANT: while $Π$-types are unordered, tuples $(E)$ are _ordered_ left-to-right!]

#import "content/rules/hasty.typ": *

#fig-r-hasty

#todo[explain #op-calc(ms("F")), #case-calc(ms("F")) as sublanguages of #iter-calc(ms("F"))]

=== Regions

#todo[introduce concept of an _expression space_]

#todo[fix notation for expression space judgement]

#import "content/rules/haslb.typ": *

#fig-haslb-br

#todo[introduce concept of a _region space_]

#fig-haslb-ssa

#todo[SSA is just a region-space too... hence gSSA]

#todo[_slightly_ adjust grammar; this allows for custom terminators, which is always fun!]

#fig-gssa-grammar

#fig-haslb-gssa

=== Metatheory

#todo[Weakening; connection to thinning]

#todo[Label weakening]

#todo[Type weakening]

#todo[Implies a lattice of types]

#todo[Typed weakening]

#todo[Implies a lattice of contexts]

#todo[Typed label weakening]

#todo[Implies a lattice of label-contexts]

#todo[Substitution]

== Expressions

#todo[introduce the concept of an _equational theory_ $req$]

#todo[begin with globally valid rewrites?]

#todo[note: 
  _all_ rewrites are globally valid _except_ for:
  - $β$, which needs $ε$ to be:
    - relevant + affine. _intuitionistic_?
    - central w.r.t. $η$
  - 
]

#todo[_elas_ ; we need effects for $β$ and $η$ rules! I always forget $η$ is green...]

#todo[discuss _refinement_ via effects]

=== Effects

#todo[
  introduce the concept of an _effect system_ $cal("E")$;
  for simplicity, want a _bounded partial order_ of effects.

  Effect systems are _always_ linear, because why not?
]

#todo[
  - 
]

#todo[effects and nontermination; introduce the concept of an _iterative_ effect system]

#todo[introduce notion of _direct_ effect]

#fig-r-eff-hasty

#todo[introduce _$β$-rule_]

#todo[introduce _uniformity_]

#todo[actual effect rules are nicer]

#todo[
  we don't start with the actual rules to avoid mutual recursion between effect system
  and equivalence theory
]

#figure(
  [
    #todo[this]
  ],
  caption: [Equivalence rules for #iter-calc(ms("F"))],
)

#fig-r-eq-congr-hasty

#todo[refinement goes here]

== Regions

#figure(
  [
    #todo[this]
  ],
  caption: [Equivalence rules for #gssa-calc()],
)

#figure(
  [
    #todo[this]
  ],
  caption: [Congruence rules for #gssa-calc() equivalence],
)

=== Effects

#todo[effects for regions is just like for expressions; _except_]

#todo[
  jumping to a label invokes that label's effects;
  so we need to keep track of each label's effects
]

#figure(
  [
    #todo[this]
  ],
  caption: [Effect rules for #gssa-calc()],
)

#todo[refinement goes here]

= Substructural SSA

== Substructural Types

#todo[
  two components:
  - _quantities_ in contexts
  - substructural types themselves
]

#todo[definition]

#todo[affinity rules]

#todo[weakening rules]

#todo[splitting rules]

#todo[
  - split vs. splat : consider $tysplits(tzero, tunit, tunit)$
]

#todo[lattice structure 2]

== Expressions

#todo[typing + effect rules]

#todo[weakening]

#todo[linear substitution]

#todo[refinement calculus]

== Regions

#todo[typing + effect rules]

#todo[weakening]

#todo[substitution]

#todo[label substitution]

#todo[refinement calculus]

= Basic (Enriched) Category Theory

#[
  #set heading(offset: 1)
  #include "content/background/category-theory.typ"
]

= Semantics of Imperative Programming <imp-cats>

#todo[
  Chapter structure:
  - We introduce some category theory.
    The goal is a _$cal(V)$-enriched distributive copy-discard Elgot category_.
  - Each _enriched structure_ corresponds to some form of _control_:
    - Categories: sequential control-flow
    - Coproducts: branching control-flow
    - Elgot structure: looping control-flow
    - Premonoidal categories: variable binding
    - Distributivity / Strength: compatibility between variable binding and control-flow structures
  - Each _enrichment_ corresponds to a syntactic system:
    - Nothing: equivalence
    - Partial orders: refinement
    - Lattices: UB-like structure
  - We introduce a #iter-calc()-model for a function space $ms("F")$
  - We give a semantics for #iter-calc(ms("F")) in this model
  - We state:
    - _Weakening_
    - Corollary: _Coherence_
    - _Soundness of substitution_
    - _Soundness_
    - _Completeness_
  - We give a semantics for #ssa-calc(ms("E")) in this model
  - We state:
    - _Weakening_
    - Corollary: _Coherence_
    - _Soundness of substitution_
    - _Soundness_
    - _Completeness_ (later: need to work via isomorphism to #iter-calc() from (previous?) chapters)
]

#todo[
  - High-level overview diagram
  - Todo: mapping from _computational_ to _mathematical_ structures:
    - Poset-enriched categories are _sequential composition_ of computer programs.

      Two directions from here:

      - Coproducts are the same as _branching control flow_
        - If we want to add loops, we get an _iterative category_,
          but, this is not well-behaved with some advanced loop optimizations
        - To make things well-behaved, we add a _uniformity condition_ and get an _Elgot category_

      - Premonoidal are the same as _sequential composition with linear variables_
        (linear means can be used _exactly_ once)

        - A _semicartesian_ premonoidal category is  _sequential composition with affine variables_.
          We will study these later!

        -
]

#todo[
  - Categories, functors and products
  - Concrete categories and concretely cartesian categories
  - $cal(V)$-enriched categories, functors
  - $cal(V)$-enriched natural transformations; multifunctor lore
  - Introduce _monads_
  - Introduce _subcategories_, wide and full
    - $cal(V)$-enriched: injection must be a $cal(V)$-morphism
    - Introduce $ms("Rel")$: subcategories are $cset$, $ms("PFun")$, but also $ms("Rel")^+$
    - Naturally want to keep track of lattices like this
    - Previously in the paper we discuss _effect systems_
    - Can stick these on a category in the obvious manner: it's a monotone map into the subcategories
      - _Not_ necessarily join/meet-preserving! Only preserves $⊤$.
  // - Now: products; part 2. $×$ of $C_ε$ is $C_ε$ and projections are $C_⊥$
  - Coproducts and initial objects
    - Effect system interaction: $+$ of $C_ε$ is $C_ε$ and injections are $C_⊥$
  - Elgot categories
    - Uniformity w.r.t. to a subcategory
    - Uniformity w.r.t. to an effect system: needs to have $⊥$ uniform
  - Premonoidal categories
    - $⊗$ respects effects, and all $α, σ$ are $C_⊥$
    - copy-discard
    - an effect respecting copy-discard _is_ a Freyd category!
      - In particular, $cal(C)_⊥$ must be Cartesian, so we have successfully recovered the _essence_
        of a Kleisli category over a cartesian base
]

#[
  #set heading(offset: 1)

  #include "content/semantics-of-ssa/strong-elgot-categories.typ"
]

== Cartesian models of #iter-calc()

#include "content/semantics-of-ssa/semantics-of-expressions.typ"

== Substructural models of #iter-calc()

#todo[this]

= Semantics of SSA

== Semantics of Regions

#include "content/semantics-of-ssa/semantics-of-regions.typ"

= Monadic Models of SSA

#todo[this]

#the-bibliography

#pagebreak()

#let appendix(body) = {
  set heading(numbering: "A", supplement: [Appendix])
  counter(heading).update(0)
  (thesis-state.update)(appendix-state)
  [ #body <appendix> ]
}

#show: appendix

= Type Theory

/*
TODO: shunt proof to appendix

#block-note[
  If $sle(ms("X"))$ is a preorder, so is $tyle(ms("X"))$.

  - Reflexivity: if $sty(X)$ is reflexive;
    given $A ∈ sty(ms("X"))$, prove $tywk(A, A)$.

    By induction on type $A$
    - (base): $tywk(X, X)$ (by reflexivity of $sle(ms("X"))$)
    - ($Π$ empty): $tywk(Π [], Π [])$
    - ($Σ$ empty): $tywk(Σ [], Σ [])$
    - ($Π$ cons):
      $tywk(Π lb("T"), Π lb("T"))$ and $tywk(A, A)$ so
      $tywk(Π (lb("T"), fty(lb("f"), A)), Π (lb("T"), fty(lb("f"), A)))$
    - ($Σ$ cons):
      $tywk(Σ lb("T"), Σ lb("T"))$ and $tywk(A, A)$ so
      $tywk(Σ (lb("T"), fty(lb("f"), A)), Σ (lb("T"), fty(lb("f"), A)))$
  - Transitivity: if $sle(ms("X"))$ is transitive;
    given $tywk(A_1, A_2)$ and $tywk(A_2, A_3)$ prove $tywk(A_1, A_3)$.

    Suffices to show $∀ A_3 . tywk(A_2, A_3) => tywk(A_1, A_3)$
    by induction on the derivation $tywk(A_1, A_2)$.

    - @twk-base:
      Have $A_1 = X_1 ∈ ms("X")$, $A_2 = X_2 ∈ ms("X")$
      with $X_1 sle(X) X_2$.

      Fix $A_3$ s.t. $tywk(A_2, A_3)$.
      By inversion on $tywk(X_2, A_3)$, either:
      - $A_3 = X_3 ∈ ms("X")$ with $X_2 sle(X) X_3$;
        in which case result follows by transitivity of $sle(X)$
      - $A_3 = tunit$;
        in which case result follows by @twk-unit.

    - @twk-sigma:
      Have $A_1 = Σ (lb("T")_1, fty(lb("f"), B_1))$, $A_2 = Σ (lb("T")_2, fty(lb("f"), B_2))$
      with $tywk(Σ lb("T")_1, Σ lb("T")_2)$ and $tywk(B_1, B_2)$.

      Fix $A_3$ s.t. $tywk(A_2, A_3)$.
      By inversion on $tywk(Σ (lb("T")_2, fty(lb("f"), B_2)), A_3)$, either:
      - @twk-sigma : $A_3 = Σ (lb("T")_3, fty(lb("f"), B_3))$ with
        $tywk(Σ lb("T")_2, Σ lb("T")_3)$ and $tywk(B_2, B_3)$;

        By induction, have $Σ lb("T")_1 ≤ Σ lb("T")_3$ and $tywk(B_1, B_3)$;
        so result follows by @twk-sigma.

    - @twk-pi:
      Have $A_1 = Π (lb("T")_1, fty(lb("f"), B_1))$, $A_2 = Π (lb("T")_2, fty(lb("f"), B_2))$
      with $tywk(Π lb("T")_1, Π lb("T")_2)$ and $tywk(B_1, B_2)$.

      Fix $A_3$ s.t. $tywk(A_2, A_3)$.
      By inversion on $tywk(Π (lb("T")_2, fty(lb("f"), B_2)), A_3)$, either:
      - $A_3 = Π (lb("T")_3, fty(lb("f"), B_3))$ with
        $tywk(Π lb("T")_2, Π lb("T")_3)$ and $tywk(B_2, B_3)$;

        By induction, have $Π lb("T")_1 ≤ Π lb("T")_3$ and $tywk(B_1, B_3)$;
        so result follows by @twk-pi.

      - $A_3 = tunit$;
        in which case result follows by @twk-unit.

      - @twk-unit : $A_3 = tunit$;
        in which case result follows by @twk-unit.

    - @twk-unit:
      Have $A_2 = tunit$.
      Fix $A_3$ s.t. $tywk(A_2, A_3)$.
      By inversion on $tywk(tunit, A_3)$, $A_3 = tunit$; result follows by @twk-unit.

    - @twk-zero: Have $A_1 = tzero$; result follows by @twk-zero.
]

#block-note[
  If $sle(ms("X"))$ is a partial order, so is $tyle(ms("X"))$

  Suffices to show: if $sle(ms("X"))$ is antisymmetric, so is $tyle(ms("X"))$

  Suffices to show: by induction on $atywk(A, B, ms("X"))$ that $atywk(B, A, ms("X")) => A = B$

  - @twk-base:
    Have $A = X$, $B = Y ∈ ms("X")$ with $X sle(ms("X")) Y$.

    By inversion, result follows from antisymmetry of $sle(ms("X"))$
  - @twk-sigma:
    Have $A = Σ (lb("T"), fty(lb("f"), A'))$, $B = Σ (lb("T"'), fty(lb("f"), B'))$ with
    $atywk(Σ lb("T"), Σ lb("T"'), ms("X"))$ and $atywk(A', B', ms("X"))$.

    By inversion, have $atywk(Σ lb("T"'), Σ lb("T"), ms("X"))$ and $atywk(B', A', ms("X"))$.

    Hence, by induction, have $A' = B'$ and $Σ lb("T") = Σ lb("T"')$;
  - @twk-pi:
    Have $A = Π (lb("T"), fty(lb("f"), A'))$, $B = Π (lb("T"'), fty(lb("f"), B'))$ with
    $atywk(Π lb("T"), Π lb("T"'), ms("X"))$ and $atywk(A', B', ms("X"))$.

    By inversion, have $atywk(Π lb("T"'), Π lb("T"), ms("X"))$ and $atywk(B', A', ms("X"))$.

    Hence, by induction, have $A' = B'$ and $Π lb("T") = Π lb("T"')$;
    implying the desired result.
    implying the desired result.
  - @twk-unit: have $B = tunit$; by inversion, $A = tunit$.
  - @twk-zero: have $A = tzero$; by inversion, $B = tzero$.
]
*/

= Category Theory

//TODO: pull down
/*
#definition(name: "Opposite Category")[
  Given a category $cal(C)$, we define it's opposite category $opc(cal(C))$ to have
  - Objects $|opc(cal(C))| = |cal(C)|$
  - Morphisms $opc(cal(C))(A, B) = { opm(f) | f ∈ cal(C)(B, A) }$
    #footnote[
      This is in bijection with $cal(C)(B, A)$
      // (and is usually defined to be equal to it!)
      but we add the $opm(-)$-tag to avoid confusion.
    ].
  - Composition given by $opm(f) ; opm(g) = opm((g ; f))$
]
*/

/*
In particular:
- The (unique) initial object in $cset$ is the empty set $∅$
- Any singleton set is a terminal object in $cset$.
  We fix a singleton set $tunit_cset = {*}$.
- Likewise, the (unique) initial object in $ms("Cat")$ is the empty category with objects $∅$
- The terminal object in $ms("Cat")$ has
  one object $* ∈ mb(1)_cset$
  and only the identity morphism $id_* : mb(1)_ms("Cat")(*, *)$

#todo[fix this this is not a good discussion]

The existence of the opposite category means that for every structure $cal(S)$
defined on arbitrary categories $cal(C)$,
we can immediately ask whether $cal(S)$ exists on the _opposite category_ $opc(cal(C))$.
If it does, this naturally induces a structure $opc(cal(S))$ on $cal(C)$ as well,
the _dual_ of $cal(S)$.

As an example of this,
- A category $cal(C)$ has an initial object if and only if $opc(cal(C))$ has a terminal object;
  so the terminal object is dual to the initial object
- Likewise, a category $cal(C)$ has a terminal object if and only if $opc(cal(C))$ has an initial object;
  so the initial object is dual to the terminal object
- In general, if $cal(S)$ is dual to $opc(cal(S))$, then $opc(cal(S))$ is dual to $cal(S)$.
  In particular, this means that $opc(opc(cal(S))) = cal(S)$

In general, we get the dual structure $opc(cal(S))$ to $cal(S)$
by flipping the direction of all morphisms in the
definition of $cal(S)$.
*/


/*
#definition(name: [$cal(V)$-Quiver])[
  A $cal(V)$-quiver $cal(Q)$ consists of
  - A set of objects $|cal(Q)|$
  - For each pair of objects $A, B : |cal(Q)|$, a hom-object $cal(Q)(A, B) ∈ |cal(V)|$

  In particular, every $cal(V)$-category can be made into a $cal(V)$-quiver by forgetting
  the identities and composition.

  We define the category of $cal(V)$-quivers $ms("Quiv")_cal(V)$ to have:
  - Objects $cal(V)$-quivers
  - Morphisms $F : ms("Quiv")_cal(V)(cal(Q)_1, cal(Q)_2)$ consisting of
    - A mapping on objects $|F| : |cal(Q)_1| → |cal(Q)_2|$
    - For each pair of objects $A, B : |cal(Q)_1|$, a $cal(V)$-morphism
      $
        F_(A, B) : cal(V)(cal(Q)_1(A, B), cal(Q)_2(F A, F B))
      $
  - Identity morphisms $id_(cal(Q)) = (id, id)$
  - Composition given by
    - $|F ; G| = |G| ∘ |F|$
    - $(F ; G)_(A, B) = F_(A, B) ; G_(F A, F B)$

  In particular, this is the same as composition of functors,
  giving us a faithful forgetful functor from the category of $cal(V)$-categories
  $ms("Cat")_cal(V)$ to the category of $cal(V)$-quivers $ms("Quiv")_cal(V)$.

  Given a family of $cal(V)$-quivers $cal(Q)_i$ for $i ∈ I$, we may define:
  - The _product quiver_ $Π_i Q_i$
]
*/

/*
#definition(name: [$cal(V)$-Multifunctor])[
  Given a family of $cal(V)$-categories $scat(C) = [cal(C)_i | i ∈ I]$
  and a $cal(V)$-category $cal(D)$,
  a _multifunctor_ $F$ from $icol(C)$ to $cal(D)$ consists of
  - A mapping from families of objects $icol(A) = [A_i : |cal(C)_i| | i ∈ I]$
    to objects $F icol(A) : |cal(D)|$
  - For each $j ∈ I$,
    a mapping from families of objects $icol(A)_j = [A_i : |cal(C)_i| | i ∈ I backslash {j}]$
    a $cal(V)$-functor
    $
      F med icol(A)_j : cal(C)_j → cal(D)
    $
    such that
    $
      ∀ A_j : |cal(C)_j|, F_j med icol(A)_j med A_j = F med icol(A) : |cal(D)|
    $
    where
    $
      icol(A) = [j ↦ A_j] ovrd icol(A)_j = [A_i | i ∈ I]
    $

  In other words, $F$ is a function of $A_i$
  which is a $cal(V)$-functor in each argument $A_j$ _separately_,
  when all other arguments $A_i$ for $i ≠ j$ are held fixed.

  Given $cal(V)$-multifunctors $F, G: scat(C) → D$, we say that a family of morphisms
  $η_icol(A): cal(D)(F icol(A), G icol(A))$ is _natural_ in $j ∈ I$ if,
  for each family of objects $icol(A)_j = [A_i : |cal(C)_i| | i ∈ I backslash {j}]$,
  the family of morphisms $η_icol(A)_j$ given by
  $(η_icol(A)_j)_X := η_([j ↦ X] ovrd icol(A)_j)$
  is a natural transformation $η_(icol(A)_j) : F icol(A)_j => G icol(A)_j$.

  That is, for every morphism $f : cal(C)_j (A_j, A_j')$,
  we have that the following diagram commutes
  $
    #diagram(cell-size: 15mm, $
      F med icol(A) edge(η_icol(A), ->) edge("d", F med icol(A)_j med f, ->) &
      G med icol(A) edge("d", G med icol(A)_j med f, ->, label-side: #left) \
      F med icol(A)' edge(η_icol(A)', ->, label-side: #right) & G med icol(A)' $)
  $
  where
  $
    icol(A) = [j ↦ A_j] ovrd icol(A)_j = [A_i | i ∈ I] quad quad quad
    icol(A)' = [j ↦ A_j'] ovrd icol(A)_j = [A_i | i ∈ I]
  $
]
*/

/*
#definition(name: [$cal(V)$-Natural Multitransformation])[
  Given $cal(V)$-multifunctors $F, G: scat(C) → D$, we define a $cal(V)$-natural multitransformation
  $η : F => G$ to consist of:
  - For each family of objects $icol(A) = [A_i : cal(C)_i | i ∈ I]$,
    a morphism $η_(icol(A)) : cal(D)(F icol(A), G icol(A))$
  - For each $j ∈ I$,
    a mapping from families of objects $icol(A)_j = [A_i : cal(C)_i | i ∈ I backslash {j}]$
    a natural tranformation
    $
      η_icol(A)_j : F_j med icol(A)_j => G_j med icol(A)_j
    $
    such that
    $
      ∀ A_j : |cal(C)_j|, (η_(icol(A)_j))_(A_j) = η_[A_i | i ∈ I]
        : cal(D)(F [A_i | i ∈ I]) → cal(D)(G [A_i | i ∈ I])
    $

  In other words, if we consider $F$, $G$, and $η$ as functions of $A_i$, and, for a given $j ∈ I$,
  fix all $A_i$ for $i ≠ j$, then
  - $F$ and $G$ are functors
  - $η$ is a natural transformation from $F$ to $G$

  That is, $η$ is a natural transformation in each argument $A_j$ _separately_,
  i.e., is _natural in $A_j$_.
]
*/

/*
We define a

Consider now families of objects
$X_(A_1,...,A_n), Y_(A_1,...,A_n) ∈ |cal(C)|$ parametrized by $n$ objects $A_i ∈ |cal(C)|$
and a family of morphisms
$m_(A_1,...,A_n) : cal(C)(X_(A_1,...,A_n), Y_(A_1,...,A_n))$.
We say that $m$ is _natural_ in $A_i$ if:
- There exists a $cal(V)$-functor $F_i$ such that
  $F_i med B = X_i$

Given a function $|cal(C)|^n → |cal(C)|$
*/
