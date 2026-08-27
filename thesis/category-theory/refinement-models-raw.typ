// Mechanical transcription from:
// papers/isotope/complete-refinement-ssa.tex
// Repository commit: 9480278f2503902f0fa632d05d7f0c8faae893f3
// Section: Semantics / Models of lambda_iter
// Source lines: 1653--2254
// Conversion: LaTeX presentation mechanics translated to Typst by Pandoc,
// followed only by compile repairs and explicit TODO markers.

#import "/lib/prelude.typ": *
#show: chapter.with(title: "Models of lambda_iter (raw import)")

#todo[During thesis integration, identify which refinement-, effect-, and substructural-specific material should move to the refinement chapter, and specialize the remaining exposition to the unrefined Freyd-category narrative. Do not apply those cuts during the raw transcription pass.]

== Models of $lambda_(sans("iter"))$
<models-of-lambda_ensuremathmathsfiter>
A good categorical semantics is one in which the semantics of a term is
constructed in a straightforward, compositional manner from the
semantics of its subterms. Furthermore, we would like the equational
properties of our term formers to correspond closely to the universal
properties of the categorical structure used to interpret them. Thus,
our goal is to pick categorical structures which correspond one-to-one
to the features of $lambda_(sans("iter"))$. In particular, we need to
find categorical structures to model our three primary structured
control-flow constructs, which are:

- #emph[Sequencing] and #emph[binding], which we will do using the
  structure of a #emph[premonoidal category]

- #emph[Branching], which we will do using #emph[coproducts]

- #emph[Iteration], which we will do using a #emph[Conway operator]

To maintain compositionality, we must additionally require that these
structures interact properly with each other. Hence, we will also
require our category to satisfy

- #emph[Distributivity], which ensures the premonoidal and coproduct
  structures are compatible

- #emph[Strength], which ensures the Conway operator is compatible with
  the premonoidal structure

- #emph[(Directed) Uniformity], which ensures the Conway operator is
  compatible with our effect and refinement systems.

Finally, we'll need to model the features of our type theory;
particularly:

- #emph[Refinement], which we will do using #emph[poset-enrichment]

- #emph[Effects], which we will do by introducing the new notion of a
  #emph[substructural effectful category]

In ordinary categorical semantics, we want syntactic equivalence to
correspond to equality of morphisms: given
$Gamma^(upright(bold(q))) tack.r_(cal(R)) a approx b : A$,
$⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt a : A ⟧ = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt b : A ⟧$.

However, in our calculus, we do not only have a syntactic notion of
equivalence, but we also have the order structure arising from
refinement. Since terms correpond to morphisms, this means we need to be
able to compare morphisms according to an order structure interpreting
the refinement relation. Thus, to interpret $arrow.r.twohead$, we
generalize from ordinary categories to #emph[poset-enriched] categories,
in which our hom-sets are partially ordered. In particular, we define:

#block[
A category $cal(C)$ is #emph[poset-enriched] if each hom-set
$cal(C) \( A \, B \)$ is equipped with a partial order $arrow.r.twohead$
which is compatible with composition, i.e., which satisfies
$ forall f arrow.r.twohead f' in cal(C) \( A \, B \) . forall g arrow.r.twohead g' in cal(C) \( B \, C \) . \( f ; g \) arrow.r.twohead \( f' ; g' \) $
A poset-enriched functor between categories $cal(C)$, $cal(D)$ is then
simply a functor whose action on morphisms is monotonic.

]
We can now quite naturally intepret soundness of refinement as follows:
given
$Gamma^(upright(bold(q))) tack.r_(cal(R)) a arrow.r.twohead b : A$, we
require that
$⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt a : A ⟧ arrow.r.twohead ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt b : A ⟧$.
Soundness of equivalence follows directly from antisymmetry of partial
orders.#footnote[Requiring $cal(C)$ to be a poset-enriched category does
not in fact rob us of any generality, since #emph[all] categories are
poset-enriched under the identity ordering on hom-sets.]

We now wish to give poset-enriched versions of the models for our three
control-flow primitives, namely, seqencing, branching, and iteration.
Premonoidal categories were introduced in
#cite(<power-premonoidal-97>, form: "prose") to model side-effectful,
sequential computations with first-order binding. A premonoidal category
can be viewed as a generalization of a monoidal category, in which
#emph[sliding] does not necessarily hold; i.e., we have that, in
general,
$\( f ⊗ sans("id") \) ; \( sans("id") ⊗ g \) ≠ \( sans("id") ⊗ g \) ; \( f ⊗ sans("id") \)$.
To better understand this in terms of programming languages, a
premonoidal category may also be viewed as a generalization of the
Moggi's @moggi-91-monad monadic semantics: if we consider a strong monad
over a Cartesian category, then the Kleisli category is premonoidal with
the Cartesian product in the underlying category as tensor product.

The Kleisli category satisfies sliding when the underlying monad is
#emph[commutative]: when the sequencing of side-effects does not matter
(e.g., the reader monad). We need to generalize monoidal categories to
premonoidal categories precisely to support monads for which sequencing
does matter, such as printing or state. For example, given a function
$sans("print") : sans("str") arrow.r \( \)$,
$\( sans("print") ⊗ sans("id") \) ; \( sans("id") ⊗ sans("print") \) ≠ \( sans("id") ⊗ sans("print") \) ; \( sans("print") ⊗ sans("id") \)$
since, given input $(mono("hello"), mono("world"))$, the
left-hand side will print $mono("hello world")$, while the
right-hand side will print $mono("world hello")$. Note that the
sequencing in the induced premonoidal category corresponds precisely to
the bind of the underlying monad.

We give a precise definition of a (#emph[poset-enriched]) premonoidal
category below:

#block[
We define a #emph[binoidal category] to be a category $cal(C)$ equipped
with a binary operation
$⊗ : \| cal(C) \| times \| cal(C) \| arrow.r \| cal(C) \|$ on
the objects of $cal(C)$ and, for each $A \, B in \| cal(C) \|$, functors
$A ⊗ - \, - ⊗ B : cal(C) arrow.r cal(C)$. We say a
morphism $f : A arrow.r A'$ in a binoidal category is #emph[central] if,
for all $g : B arrow.r B'$, it satisfies #emph[sliding]:
$ f ⊗ B ; A' ⊗ g = A ⊗ g ; f ⊗ B' #h(2em) B ⊗ f ; g ⊗ A' = g ⊗ A ; B' ⊗ f $
in which case we may write these morphisms as
$f ⊗ g : A ⊗ B arrow.r A' ⊗ B'$ and
$g ⊗ f : B ⊗ A arrow.r B' ⊗ A'$
respectively. In the poset-enriched setting, we also assume that the
left and right tensor functors are poset-enriched, i.e. monotonic on
morphisms.

A #emph[premonoidal category] is, then, a binoidal category equipped
with:

- An #emph[identity] object $I in \| cal(C) \|$

- For each triple of objects $A \, B \, C in \| cal(C) \|$, a central,
  natural isomorphism
  $alpha_(A \, B \, C) : \( A ⊗ B \) ⊗ C arrow.r A ⊗ \( B ⊗ C \)$,
  the #emph[associator]

- For each object $A$, central, natural isomorphisms
  $lambda_A : A ⊗ I arrow.r A$ and
  $rho_A : I ⊗ A arrow.r A$, the #emph[left] and #emph[right
  unitors]

satisfying the #emph[triangle] and #emph[pentagon identity]
$ alpha_(A \, I \, B) ; A ⊗ lambda_B = rho_A ⊗ B #h(2em) alpha_(A ⊗ B \, C \, D) ; alpha_(A \, B \, C ⊗ D) = alpha_(A \, B \, C) ⊗ D ; alpha_(A \, B ⊗ C \, D) ; A ⊗ alpha_(A \, B \, C) $
We say a premonoidal category is #emph[symmetric] if it is also equipped
with a central, natural involution
$sigma_(A \, B) : A ⊗ B arrow.r B ⊗ A$, the
#emph[symmetry], satisfying the #emph[hexagon identity]
$ alpha_(A \, B \, C) ; sigma_(A \, B ⊗ C) ; alpha_(B \, C \, A) = sigma_(A \, B) ⊗ C ; alpha_(B \, A \, C) ; B ⊗ sigma_(A \, C) $

]
One theorem of note about premonoidal categories is #emph[coherence],
which we state as follows:

#block[
For any premonoidal category $cal(C)$, the subcategory $cal(C)_(cal(A))$
generated by associators, unitors, and their tensor products is an
equivalence relation, i.e., for all $A \, B : \| cal(C)_(cal(A)) \|$, if
$f \, g : A arrow.r B$ can be constructed using only identity,
composition, associators, unitors, and their tensor products, then
$f = g$, and $f \, g$ are isomorphisms in $cal(C)_(cal(A))$.
<thm:monoidal-coherence>

]
We will hence sometimes abuse notation and write
$alpha_B : cal(C) \( A \, B \)$ or simply $alpha$ for the unique
morphism in $cal(C)_(cal(A))$ from $A$ to $B$, where the composition of
associators and unitors is too cumbersome to write out in full. In
particular, we note that we always have that
$alpha : cal(C) \( A \, A \) := sans("id")_A$.

We model branching control-flow using the coproduct $A + B$ as a
primitive, whose definition is unchanged in the poset-enriched setting.
Given morphisms $f : A arrow.r C$ and $g : B arrow.r C$, their coproduct
$\[ f \, g \] : A + B arrow.r C$ quite naturally models a case-statement
which executes $f$ given an $A$ and executes $g$ given a $B$. We can
then implement an if-statement as a case-statement on
$upright(bold(2)) = I + I$.

Since coproducts induce a monoidal structure on a category, we will also
write $alpha_B^(+) : cal(C) \( A \, B \)$ or simply $alpha^(+)$ to
denote the unique morphism from $A$ to $B$ with analogy to the $alpha$
notation described above. Similarly, we will write $sigma^(+)$ to denote
the symmetry for coproducts.

Coproducts on their own, however, cannot interpret variables captured by
the branches of a case-statement. For example, given $x : bb(Z)$,
$y : bb(Z) + sans("str")$, consider the following expression:
$ sans("case") #h(0em) y #h(0em) { iota_l #h(0em) y : sans("print") \( mono("\"add: \"") \, x + y \) \, iota_r #h(0em) y : sans("print") \( y \, x \) } $
While our input context corresponds to the object
$bb(Z) ⊗ \( bb(Z) + sans("str") \)$, we need to somehow get
to
$\( bb(Z) ⊗ bb(Z) \) + \( bb(Z) ⊗ sans("str") \)$
to be able to evaluate our branches. Categorically, what we require is
that our tensor product #emph[distributes] over our coproduct; in which
case we say our category is #emph[distributive]:

#block[
We say a premonoidal category is #emph[distributive] if:

- It is equipped with chosen coproducts $A + B$ such that the injections
  $iota_l \, iota_r$ are central

- The obvious morphism
  $delta : \( A ⊗ B \) + \( A ⊗ C \) arrow.r A ⊗ \( B + C \)$
  is an isomorphism.

]
The last control-flow construct we need to model is looping. A loop with
input $A$ will either exit with output $B$ or recurse with a new input
$A$. Consequently, since we model branching control-flow using
coproducts, the #emph[body] of a loop will look like a morphism
$A arrow.r B + A$. Therefore, a natural way to model iteration is to
posit the existence of a fixpoint operator $\( dot.op \)^dagger$ taking
morphisms $f : A arrow.r B + A$ to their fixpoints
$f^dagger : A arrow.r B$. $f^dagger$ being the fixpoint of the body $f$
means that executing $f^dagger$ on an input $A$ is the same as executing
$f$ on an input $A$ and,

- If we get an output $B$, return it

- If we get an output $A$, feed it as an input to $f^dagger$ and return
  the resulting $B$

Indeed, in a functional language supporting higher-order functions such
as ML or Haskell, we might write `iterate :: (A -> B + A) -> A -> B`
with definition

#block[
#block[
```haskell
iterate f a = case f a of { Left b -> b ; Right a' -> iterate f a' }
```

]
]
This corresponds exactly to the notion of a #emph[pre-iterative
category] given below:

#block[
Let $cal(C)$ be a category with chosen coproducts. We say $cal(C)$ is
#emph[pre-iterative] if it is equipped with a fixpoint operator
$\( - \)^dagger : cal(C) \( A \, B + A \) arrow.r cal(C) \( A \, B \)$
satisfying the loop unrolling equation
$f ; \[ sans("id") \, f^dagger \] = f$

]
Our goal is to have our fixpoint operator's properties correspond
precisely to drawing a loop in a control-flow graph, as in the left-hand
side of Figure~@fig:fixpoint-string-diagram, which corresponds to
$f^dagger$. In particular, we should be able to reconfigure such
diagrams up to isotopy (i.e., moving boxes and wires around without
changing connectivity) without changing the meaning of our program. To
be able to do so soundly, we will need to introduce some additional
equations, which correspond to the graphical transformations in
Figure~@fig:elgot-ax-string-diagrams; a fixpoint satisfying these
equations is called a #emph[Conway iteration operator], as defined
below:

#block[
Given a pre-iterative category $cal(C)$, we say $\( - \)^dagger$ is a
#emph[Conway iteration operator] if it additionally satisfies

- #emph[Naturality:] given $f : A arrow.r B + A$ and $g : B arrow.r C$,
  we have $\( f ; g + sans("id") \)^dagger = f^dagger ; g : A arrow.r C$

- #emph[Dinaturality:] given morphisms $g : A arrow.r B + C$ and
  $h : C arrow.r B + A$, we have that
  $\( g ; \[ iota_l \, h \] \)^dagger = g ; \[ sans("id")_B \, \( h ; \[ iota_l \, g \] \)^dagger \]$

- #emph[Codiagonal:] given $f : A arrow.r \( B + A \) + A$, we have
  $\( f^dagger \)^dagger = \( f ; \[ sans("id") \, iota_r \] \)^dagger : A arrow.r B$

]
#todo[Mechanically port the four TikZ string diagrams from source lines 1889--2057. Pandoc preserved their captions and labels below but omitted the TikZ drawing bodies.]

#figure([#figure([],
    caption: [
      Fixpoint
    ]
  )
  <fig:fixpoint-string-diagram>

  #figure([],
    caption: [
      Naturality
    ]
  )

  #figure([],
    caption: [
      Codiagonal
    ]
  )

  #figure([],
    caption: [
      Dinaturality
    ]
  )

  ],
  caption: [
    Representations of the Conway iteration axioms as string diagrams
  ]
)
<fig:elgot-ax-string-diagrams>

In particular, we note that naturality and codiagonal correspond
directly to our rules let-iter and codiag respectively; we will later
see that dinaturality is derivable.

Just like for branching control-flow, we also require an additional
condition to ensure that our iteration operator is compatible with our
premonoidal structure. Specifically, we would like to be able to
"thread" values through our loop bodies; i.e., the following two
programs should be equivalent for #emph[pure] $c$:
$ \( sans("iter") #h(0em) a #h(0em) { iota_r #h(0em) x : b } \, c \) approx sans("iter") #h(0em) \( a \, c \) #h(0em) { iota_r #h(0em) \( x \, y \) : sans("case") #h(0em) b #h(0em) { iota_l #h(0em) z : iota_l #h(0em) \( z \, y \) \, iota_r #h(0em) z : iota_r #h(0em) \( z \, y \) } } $
This corresponds to requiring our Conway iteration operator to be
#emph[strong], defined as follows:

#block[
If $cal(C)$ is distributive, we say an iteration operator
$\( dot.op \)^dagger$ is #emph[strong] if
$ forall f : A arrow.r B + A \, \( C ⊗ f ; delta^(- 1) \)^dagger = C ⊗ f^dagger $

]
We've now got almost everything we need to model pure and arbitrarily
effectful $lambda_(sans("iter"))$ programs, but we still need to be
able to perform a more fine-grained classification of effects. To do so,
we introduce a generalization of the notion of an #emph[effectful
category], which in the literature (e.g. @promonad) only distinguishes
between pure and arbitrarily effectful morphisms.

#block[
An effectful category $cal(C)$ over an effect system $cal(E)$ consists
of a symmetric premonoidal poset-enriched category $cal(C)$ equipped
with a monotonic mapping from $epsilon.alt in cal(E)$ to wide#footnote[A
#emph[wide] subcategory is one which has all of the objects of the
original category.] (symmetric premonoidal) subcategories
$cal(C)_epsilon.alt subset.eq cal(E)$ #footnote[Note that
$cal(C)_epsilon.alt \( A \, B \)$ is #emph[not] necessarily closed under
refinement: we can have $f in cal(C)_epsilon.alt \( A \, B \)$ and
$f arrow.r.twohead f'$ with
$f' in.not cal(C)_epsilon.alt \( A \, B \)$.] such that, given
$epsilon.alt \, eta in cal(E)$, $f in cal(C)_epsilon.alt \( A \, B \)$,
and $g in cal(C)_eta \( A' \, B' \)$,
$epsilon.alt harpoon.rt eta arrow.r.double.long f times.l g arrow.r.twohead f times.r g$
and
$epsilon.alt harpoon.lb eta arrow.r.double.long f times.l g arrow.l.twohead f times.r g$.
We call morphisms with effect $tack.t$ #emph[pure]. We say an effectful
category is #emph[distributive] if the underlying premonoidal category
is, and the injections are pure.

]
The goal of allowing morphisms with compatible effects to commute is to
allow proving substitution of effectful programs sound. Unfortunately,
we don't have quite enough structure to allow substitution #emph[into]
the body of a loop: while commutativity of $a$ and $b$ is enough to
justify that
$sans("let") #h(0em) x = a ; #h(0em) \( b \, x \) approx \( b \, a \)$
proving that
$sans("let") #h(0em) x = a ; #h(0em) sans("iter") #h(0em) b #h(0em) { iota_r #h(0em) y : c } approx sans("iter") #h(0em) b #h(0em) { iota_r #h(0em) y : sans("let") #h(0em) x = a ; #h(0em) c }$
for $x in.not sans("fv") \( b \)$ requires us to be able to move a
morphism #emph[into] the body of a loop. To be able to do that
effectively, we need to introduce the concept of a
#emph[$cal(K)$-uniform iteration operator] as follows:

#block[
Given a wide subcategory $cal(K) subset.eq cal(C)$ of a category
equipped with a Conway iteration operator, we say $cal(C)$ is
#emph[$cal(K)^p$-uniform] for $p in { + \, - }$ if, for all
$h : A arrow.r_(cal(K)) B$, $f : B arrow.r C + B$, and
$g : A arrow.r C + A$, we have that
$h ; f arrow.r.twohead^p g ; C + h arrow.r.double.long h ; f^dagger arrow.r.twohead^p g^dagger$.
We say a category $cal(K)$ is #emph[$cal(K)$-uniform] if it is both
$cal(K)^(+)$- and $cal(K)^(-)$-uniform, which implies in particular that
$h ; f = g ; C + h arrow.r.double.long h ; f^dagger = g^dagger$.

]
We note that this definition corresponds precisely to the ability to
perform the rewrites shown in Figure~#todo[Restore the cross-reference to `fig:unif-cfg` when importing the iteration-rules section.] (setting
$c = sans("id")_C$) whenever $s$ is in $cal(K)$ and $b$ is in $cal(C)$.
Requiring that substitution is compatible with loops is then equivalent
to requiring that the subcategories of morphisms having commutative
effects are uniform with respect to each other. We call this notion an
(effectful) Elgot category:

#block[
We say a distributive effectful category $cal(C)$ is #emph[Elgot] if it
has an iterative effect system and is equipped with a strong Conway
iteration operator, such that, for all effects $epsilon.alt \, eta$
where $epsilon.alt in cal(E)^oo$, the wide subcategory
$cal(C)_epsilon.alt$ is closed under iteration, and, iff
$epsilon.alt harpoon.rt^p eta$, then $cal(C)_epsilon.alt$ is
$cal(C)_eta^p$-uniform. In particular, we note that $cal(C)$ and hence
every $cal(C)_epsilon.alt$ is $cal(C)_tack.t$-uniform.

]
The final piece of the puzzle is that we need a way to #emph[duplicate]
variables of relevant type, as well as #emph[discard] variables of
affine type. We'll supply families of morphisms
$Delta : A arrow.r A ⊗ A$, $! : A arrow.r I$ for this
purpose. We can then handle relevant and affine #emph[effects] by
requiring that the appropriate morphism families are #emph[natural]
w.r.t. the subcategory corresponding to that effect. Following this
idea, we can now define a $lambda_(sans("iter"))$-model as follows:
$lambda_(sans("iter"))$:

#block[
A model
$cal(M) = \( cal(C) \, \( dot.op \)^dagger \, ⟦ dot.op ⟧ \, Delta_() \, !_() \)$
of a $lambda_(sans("iter"))$-signature
$cal(S) = \( cal(X) \, cal(I) \, cal(E) \)$ is:

- An effectful Elgot category ($cal(C)$, $\( dot.op \)^dagger$) over
  $\( cal(E) \, cal(E)^oo \)$

- For each base type $X in cal(X)$, an object
  $⟦ X ⟧ in \| cal(C) \|$, equipped with

  - For $X$ affine, a #emph[discard morphism]
    $!_X : cal(C)_tack.t \( ⟦ X ⟧ \, I \)$

  - For $X$ relevant, a #emph[diagonal morphism]
    $Delta_X : cal(C)_tack.t \( ⟦ X ⟧ \, ⟦ X ⟧ ⊗ ⟦ X ⟧ \)$

- For each function
  $f : sans("Inst") \( cal(S) \)_epsilon.alt \( A \, B \)$, a morphism
  $⟦ f ⟧ : cal(C)_epsilon.alt \( ⟦ A ⟧ \, ⟦ B ⟧ \)$

such that, for all $A \, B in \| cal(S) \|$,
$f : cal(C)_epsilon.alt \( ⟦ A ⟧ \, ⟦ B ⟧ \)$
we have

- If $A$ relevant,
  $Delta_A ; Delta_A ⊗ ⟦ A ⟧ ; alpha = Delta_A ; ⟦ A ⟧ ⊗ Delta_A$
  and $Delta_A ; sigma_(A \, A) = Delta_A$

- If $0 lt.eq sans(q)^p \( epsilon.alt \)$ and $A \, B$ affine,
  $f ; !_B arrow.r.twohead^p !_A$

- If $0 lt.eq sans(q)^p \( epsilon.alt \)$ and $A$ relevant, $B$ affine,
  $Delta_A ; \( f ; !_B \) ⊗ ⟦ A ⟧ arrow.r.twohead^p rho^(- 1)$

- If $omega^(+) lt.eq sans(q)^p \( epsilon.alt \)$ and $A \, B$
  relevant,
  $f ; Delta_B arrow.r.twohead^p Delta_A ; f times.l f = Delta_A ; f times.r f$

where

- $⟦ upright(bold(1)) ⟧ = I$,
  $⟦ A ⊗ B ⟧ = ⟦ A ⟧ ⊗ ⟦ B ⟧$,
  $!_(upright(bold(1))) = sans("id")_I$, and
  $Delta_(upright(bold(1))) = lambda^(- 1) = rho^(- 1)$

- For $A \, B$ affine,
  $!_(A ⊗ B) = !_A ⊗ !_B ; lambda$, and for
  $A \, B$ relevant,
  $Delta_(A ⊗ B) = Delta_A ⊗ Delta_B ; sigma^(sans("mid"))$
  where we define
  $sigma_(A \, B \, C \, D)^(sans("mid")) = alpha_(A ⊗ \( B ⊗ C \) ⊗ D) ; A ⊗ sigma ⊗ D ; alpha$
  having type
  $cal(C)_tack.t \( \( A ⊗ B \) ⊗ \( C ⊗ D \) \, \( A ⊗ C \) ⊗ \( B ⊗ D \) \)$

- $⟦ upright(bold(0)) ⟧ = upright(bold(0))$,
  $⟦ A + B ⟧ = ⟦ A ⟧ + ⟦ B ⟧$,
  $!_(upright(bold(0))) = 0_I$, and
  $Delta_(upright(bold(0))) = 0_(0 + 0)$

- For $A \, B$ affine, $!_(A + B) = \[ !_A \, !_B \]$, and for $A \, B$
  relevant,
  $Delta_(A + B) = \[ Delta_A ; iota_l ⊗ iota_l \, Delta_B ; iota_r ⊗ iota_r \]$

]
We define the #emph[effective type] of an annotated type $A^q$,
$\[ A^q \]$ to be $upright(bold(1))$ if $q = 0$, and $A$ otherwise. We
can then proceed to define the effective type of an annotated context
$Gamma^(upright(bold(q)))$ to be the tensor product of its variables,
i.e., $\[ dot.op \] = upright(bold(1))$ and
$\[ Gamma \, x : A^q \] = \[ Gamma \] ⊗ \[ A^q \]$. We will
abuse notation slightly and extend
$⟦ dot.op ⟧$ to quantity annotated types
$A^q$ by taking
$⟦ A^q ⟧ = ⟦ \[ A^q \] ⟧$;
likewise, we define $!_(A^q) = !_(\[ A^q \])$ and
$Delta_(A^q) = Delta_(\[ A^q \])$, where the #emph[effective type] of an
annotated type $A^q$, $\[ A^q \]$, is $upright(bold(1))$ if $q = 0$, and
$A$ otherwise. Likewise, we proceed to define the semantics of an
annotated context
$⟦ Gamma^(upright(bold(q))) ⟧ : \| cal(C) \|$
as $⟦ \[ Gamma^(upright(bold(q))) \] ⟧$.

We can now define the semantics of our structural judgements, weakenings
and context splitting, in Figure~@fig:struct-sem. In particular,
weakenings simply discard unused variables (which are guaranteed to be
of affine type), while context splitting duplicates variables used in
both the left and right component contexts (which are guaranteed to be
of relevant type).

#todo[Check the mechanically converted structural-semantics figure against source lines 2193--2242, and replace the Pandoc rendering with native Typst layout without changing its equations.]

#figure([#block[
  minipage=1.1,scale=0.9
  $ #box(stroke: black, inset: 3pt, [$ ⟦ Gamma^(upright(bold(q))) mapsto Delta^(upright(bold(q))') ⟧ : cal(C)_tack.t \( ⟦ Gamma^(upright(bold(q))) ⟧ \, ⟦ Delta^(upright(bold(q))') ⟧ \) $])\
  ⟦ dot.op mapsto dot.op ⟧ = sans("id")_I #h(2em) ⟦ Gamma^(upright(bold(q))) \, x : A_epsilon.alt^q mapsto Delta^(upright(bold(q))') ⟧ = ⟦ Gamma^(upright(bold(q))) ⟧ ⊗ !_(A^q) ; lambda ; ⟦ Gamma^(upright(bold(q))) mapsto Delta^(upright(bold(q))') ⟧\
  ⟦ Gamma^(upright(bold(q))) \, x : A_epsilon.alt^q mapsto Delta^(upright(bold(q))') \, x : A_(epsilon.alt')^(q') ⟧ = ⟦ Gamma^(upright(bold(q))) mapsto Delta^(upright(bold(q))') ⟧ ⊗ cases(delim: "{", sans("id")_(⟦ A ⟧) & upright("if ") q \, q' ≠ 0, !_(A^q) & upright("otherwise"), ) $

  $ #box(stroke: black, inset: 3pt, [$ ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ : cal(C)_tack.t \( ⟦ Gamma^(upright(bold(q))) ⟧ \, ⟦ Gamma_(upright(bold(e))_l)^(upright(bold(q))_l) ⟧ ⊗ ⟦ Gamma_(upright(bold(e))_r)^(upright(bold(q))_r) ⟧ \) $])\
  ⟦ dot.op tack.r dot.op = dot.op + dot.op ⟧ = rho^(- 1)\
  ⟦ Gamma \, x : A tack.r \( upright(bold(q)) \, q \) = \( upright(bold(q))_l \, q_l \) + \( upright(bold(q))_r \, q_r \) ⟧ = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ⊗ (cases(delim: "{", lambda^(- 1) & upright("if ") q_l = 0 upright(" else"), rho^(- 1) & upright("if ") q_r = 0 upright(" else"), Delta_A & upright("otherwise"))) ; sigma^(sans("mid")) $

  ]],
  caption: [
    Denotational semantics for structural $lambda_(sans("iter"))$
    judgements
  ]
)
<fig:struct-sem>
