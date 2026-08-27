// Verbatim mechanical transcription from:
// papers/isotope/denotational-semantics-of-ssa.tex
// Repository commit: afa82558acf643f53a3e038e635ed9520ace88c6
// Source section: Denotational Semantics, lines 3085–4533

#import "/lib/prelude.typ": *
#show: chapter.with(title: "Denotational Semantics")

<sec:densem>
Now that we have given an equational theory for SSA, we would like to build a denotational semantics for SSA: a mapping from well-typed programs $Gamma tack.r r gt.tri sans(L)$ to mathematical objects $⟦ Gamma tack.r r gt.tri sans(L) ⟧$. This naturally gives us another way to reason about whether two programs "$r$, $r'$" are "the same:" we can ask whether $⟦ Gamma tack.r r gt.tri sans(L) ⟧ = ⟦ Gamma tack.r r' gt.tri sans(L) ⟧$. Our goal is to build a denotational semantics which is both #emph[sound] and #emph[complete]; that is, such that $ Gamma tack.r r approx r' gt.tri sans(L) arrow.l.r.double ⟦ Gamma tack.r r gt.tri sans(L) ⟧ = ⟦ Gamma tack.r r' gt.tri sans(L) ⟧ $ More specifically, we'll begin by defining a notion of a #emph[model] $cal(M)$ of SSA, and then define the denotational semantics w.r.t. a model $⟦ Gamma tack.r r gt.tri sans(L) ⟧_(cal(M))$. We'll then prove that, for #emph[any] model of SSA, if $Gamma tack.r r approx r' gt.tri sans(L)$, then $ ⟦ Gamma tack.r r gt.tri sans(L) ⟧_(cal(M)) = ⟦ Gamma tack.r r' gt.tri sans(L) ⟧_(cal(M)) $ In other words, our equational theory is #emph[sound], and so never allows us to prove an equation which does not in fact hold. We'll then give an model $cal(M)$ such that $ ⟦ Gamma tack.r r gt.tri sans(L) ⟧_(cal(M)) = ⟦ Gamma tack.r r' gt.tri sans(L) ⟧_(cal(M)) ==> Gamma tack.r r approx r' gt.tri sans(L) $ showing that our equational theory is also #emph[complete]: if an equation holds in an #emph[arbitrary] model of SSA, it must in fact be derivable via our theory.

We'd further like our denotational semantics to be #emph[compositional]: the denotation of a program should be a fixed function of the denotations of its parts. To do this, we will give SSA a #emph[categorical] semantics, interpreting (label) contexts as objects and programs as morphisms between them in some target category $cal(C)$. Different program structures, such as branching and sequential composition, will correspond more-or-less directly to structures in our target category.

Before we begin, we fix some notational conventions:

- We denote the #emph[composition] of two morphisms $f : A arrow.r B$ and $g : B arrow.r C$ as $f ; g : A arrow.r C$

- We denote the coproduct of a morphism $f : B arrow.r C$ with the identity $sans("id")_A$ as $f + A : B + A arrow.r C + A$ or $A + f : A + B arrow.r A + C$.

== Freyd-Elgot Categories
<freyd-elgot-categories>
#cite(<moggi-91-monad>, form: "prose") showed that the Kleisli category of a strong monad over a CCC interprets effectful higher-order functional programs. There are two mismatches in using this as a semantics for SSA. On one hand, SSA has features not necessarily supported by Moggi models such as arbitrary, unstructured cyclic control-flow. On the other hand Moggi models support features SSA (as a first-order language) does not have, such as higher-order functions and first-class computation values.

Given that we want to model SSA with some category $cal(C)$, we hence have to think about what structure we need $cal(C)$ to possess so that it has exactly our desired features. Obviously, we need a way to take the product of two objects, to be able to model contexts as well as pairs. The usual way to do this is via #emph[monoidal categories]. However, monoidal categories typically have too many equations: computations operating on independent data must always commute (this is the "sliding rule"), which is obviously not true for effects such as printing, since $ sans("print") ( x ) ; sans("print") ( y ) eq.not sans("print") ( y ) ; sans("print") ( x ) $ Instead, we will only require that our category be #emph[premonoidal], as introduced by #cite(<power-97-premonoidal>, form: "prose"): "monoidal, without sliding." Indeed, the Kleisli category of a strong monad on a CCC is not always monoidal, as demonstrated by the writer monad on $sans("Set")$ (which exposes $sans("print")$), but #emph[is] always premonoidal. We define a premonoidal category as follows:

#block[
We define a #emph[binoidal category] to be a category $cal(C)$ equipped with a binary operation $⊗ : bar.v cal(C) bar.v times bar.v cal(C) bar.v arrow.r bar.v cal(C) bar.v$ on the objects of $cal(C)$ and, for each $A   B in bar.v cal(C) bar.v$, functors $A ⊗ -   - ⊗ B : cal(C) arrow.r cal(C)$. We say a morphism $f : A arrow.r A'$ in a binoidal category is #emph[central] if, for all $g : B arrow.r B'$, it satisfies #emph[sliding]: $ f ⊗ B ; A' ⊗ g = A ⊗ g ; f ⊗ B' #h(2em) B ⊗ f ; g ⊗ A' = g ⊗ A ; B' ⊗ f $ in which case we may write these morphisms as $f ⊗ g : A ⊗ B arrow.r A' ⊗ B'$ and $g ⊗ f : B ⊗ A arrow.r B' ⊗ A'$ respectively. A #emph[premonoidal category] is, then, a binoidal category equipped with:

- An #emph[identity] object $I in bar.v cal(C) bar.v$

- For each triple of objects $A   B   C in bar.v cal(C) bar.v$, a central, natural isomorphism $alpha_(A   B   C) : ( A ⊗ B ) ⊗ C arrow.r A ⊗ ( B ⊗ C )$, the #emph[associator]

- For each object $A$, central, natural isomorphisms $lambda_A : A ⊗ I arrow.r A$ and $rho_A : I ⊗ A arrow.r A$, the #emph[left] and #emph[right unitors]

satisfying the #emph[triangle] and #emph[pentagon identity] $ alpha_(A   I   B) ; A ⊗ lambda_B = rho_A ⊗ B #h(2em) alpha_(A ⊗ B   C   D) ; alpha_(A   B   C ⊗ D) = alpha_(A   B   C) ⊗ D ; alpha_(A   B ⊗ C   D) ; A ⊗ alpha_(B   C   D) $ We say a premonoidal category is #emph[symmetric] if it is also equipped with a central, natural involution $sigma_(A   B) : A ⊗ B arrow.r B ⊗ A$, the #emph[symmetry], satisfying the #emph[hexagon identity] $ alpha_(A   B   C) ; sigma_(A   B ⊗ C) ; alpha_(B   C   A) = sigma_(A   B) ⊗ C ; alpha_(B   A   C) ; B ⊗ sigma_(A   C) $ We say a premonoidal category is #emph[monoidal] if every morphism is central.

]
One important theorem about premonoidal categories is #emph[coherence]:

#block[
The subcategory $cal(A)$ generated by associators, unitors, and their tensor products is an equivalence relation, i.e., for all $A   B : bar.v cal(A) bar.v$, if $f   g : A arrow.r B$ can be constructed using only identity, composition, associators, unitors, and their tensor products, then:

+ $f = g$

+ $f   g$ are isomorphisms in $cal(A)$

<thm:monoidal-coherence>

]
In particular, as a syntactic convenience, we will often simply write “$alpha$" for the (unique) morphism between objects $A$ and $B$, when it exists, satisfying the requirements of Theorem~#todo[Cross-reference: \@thm:monoidal-coherence.] For example, given $f : A arrow.r B ⊗ ( ( C ⊗ I ) ⊗ D )$ and $g : ( ( B ⊗ ( I ⊗ C ) ) ⊗ D ) arrow.r E$, we have $ f ; alpha ; g := f ; B ⊗ ( lambda_C ⊗ D ) ; alpha_(B   C   D)^(- 1) ; ( B ⊗ rho_C^(- 1) ) ⊗ D ; g $ Just like for higher-order functional languages, we can interpret types $A$ as objects $⟦ A ⟧ : bar.v cal(C) bar.v$. Similarly, we can interpret variable contexts $Gamma$ by taking products of objects, as follows: $ #box(stroke: black, inset: 3pt, [$ ⟦ Gamma ⟧ : bar.v cal(C) bar.v $]) #h(2em) ⟦ dot.op ⟧ = I #h(2em) ⟦ Gamma   x : A ⟧ = ⟦ Gamma ⟧ ⊗ ⟦ A ⟧ $ We would like to interpret an expression-in-context $Gamma tack.r_epsilon.alt a : A$ as a morphism in $cal(C)$ from $⟦ Gamma ⟧$ to $⟦ A ⟧$. However, in standard SSA, it is possible for a variable to be unused, or used multiple times. Our premonoidal structure, however, does not give us any way to #emph[project] out of a product type, making it impossible to interpret expressions-in-context like $x : A   y : B tack.r_() x : A$. In order to project out individual variables, we need Cartesian structure, but a premonoidal category can only interpret #emph[linear] expressions, that is, those which use every variable exactly once. However, it is too much to require the whole premonoidal category to be Cartesian, because that would validate the sliding rule, which is what we set out to avoid.

In the case of the Kleisli category over a CCC, the Cartesian structure of the CCC becomes the premonoidal structure of the Kleisli category. This lets us use the Cartesian structure to project out the variables, while the product in the Kleisli category still does not satisfy sliding. By analogy with this case, we can suppose that there is a subcategory $cal(C)_tack.t$ of the premonoidal category $cal(C)$, which has the property that the premonoidal structure in $cal(C)$ behaves like a Cartesian product in $cal(C)_tack.t$.

If we generalize this structure to an arbitrary premonoidal category, we get the notion of a #emph[Freyd category], as introduced in #cite(<levy-03-environment>, form: "prose"):

#block[
A #emph[Freyd category] is a premonoidal category $cal(C)$ equipped with a wide subcategory $cal(C)_tack.t subset.eq cal(C)$ of #emph[pure] morphisms such that

- $cal(C)_tack.t$ contains all associators, unitors, and symmetries

- $I$ is a terminal object in $cal(C)_tack.t$. In particular, this implies the terminal morphisms $!_A : A arrow.r I$ are pure.

- For each $A   B$, $A ⊗ B$ is a cartesian product of $A   B$ in $cal(C)_tack.t$

- For pure morphisms $f   g$, $f ⊗ g = ⟨ pi_l ; f   pi_r ; g ⟩$

Where $cal(C)$ is clear from context, we will write $A arrow.r_tack.t B$ to denote a pure morphism $cal(C)_tack.t ( A   B )$.

Alternatively, it is equivalent to require

- $cal(C)_tack.t$ contains all associators, unitors, and symmetries

- $I$ is a terminal object in $cal(C)_tack.t$

- For each $A$, there exists a pure morphism $Delta_A : A arrow.r A ⊗ A$ forming a comonoid with the (pure) terminal morphism $!_A : A arrow.r I$, i.e: $Delta_A ; !_A ⊗ A ; rho = Delta_A ; A ⊗ !_A ; lambda = sans("id")_A$

- For every pure morphism $f : A arrow.r_tack.t B$, $f ; Delta_B = Delta_A ; f ⊗ f$ and $f ; !_B = !_A$.

In both cases, we have that $pi_l = A ⊗ !_B ; lambda$, $pi_r = !_A ⊗ B ; rho$, $⟨ f   g ⟩ = Delta_A ; f ⊗ g$, and $Delta_A = ⟨ sans("id")_A   sans("id")_A ⟩$

]
For convenience, given $f : A arrow.r B$ in a Freyd category, we will define the notation $ sans("let") ( f ) := Delta_A ; A ⊗ f : A arrow.r A ⊗ B $ Note that this is pure if and only if $f$ is. This has the following useful properties:

- $sans("let") ( f ) ; pi_r = f$ and, for $f$ pure, $sans("let") ( f ) ; pi_l = sans("id")$

- $sans("let") ( f ; g ) = sans("let") ( f ) ; A ⊗ g$ and $sans("let") ( sans("id")_A ) = Delta_A$

- $sans("let") ( sans("let") ( f ) ) = sans("let") ( f ) ; Delta_A ⊗ B ; alpha_(A   A   B)$, and, therefore, given $g : A ⊗ B arrow.r C$, we have $sans("let") ( sans("let") ( f ) ; g ) = sans("let") ( f ) ; sans("let") ( g ) ; pi_l ⊗ C$

We now have everything we need to model effectful first-order expressions. For reasoning about substitution, we will also demand that the denotation of “#emph[pure]" expressions $Gamma tack.r_tack.t a : A$ lies in $cal(C)_tack.t ( ⟦ Gamma ⟧   ⟦ A ⟧ )$. In general, we will write:

- $cal(C)_top$ to mean just $cal(C)$, allowing us to write $cal(C)_epsilon.alt$ for an #emph[effect] $epsilon.alt in { tack.t   top }$.

- Morphisms in $cal(C)_epsilon.alt$ as $A arrow.r_epsilon.alt B$, where $cal(C)$ is clear from context.

At this point, we still have no way to interpret control-flow, i.e. $sans("case")$-expressions. Furthermore, if we want to model regions as morphisms, we need some way of modelling label-contexts $sans(L)$. At first glance, it seems sufficient for branching control-flow to require the existence of coproducts, and indeed, assuming the existence of all coproducts and an initial object, we may model label-contexts as follows: $ #box(stroke: black, inset: 3pt, [$ ⟦ sans(L) ⟧ : bar.v cal(C) bar.v $]) #h(2em) ⟦ dot.op ⟧ = upright(bold(0)) #h(2em) ⟦ sans(L)   ell ( A ) ⟧ = ⟦ sans(L) ⟧ + ⟦ A ⟧ $ Regions can now be interpreted as morphisms in $cal(C)$ from $⟦ Gamma ⟧$ to $⟦ sans(L) ⟧$, as desired. Just like for products, we will write "$alpha^(+)$" for the (unique) morphism between objects $A$ and $B$, when it exists, satisfying the requirements of Theorem~#todo[Cross-reference: \@thm:monoidal-coherence] where coproducts are taken as the monoidal structure; we will sometimes also write $alpha_B^(+)$ for clarity.

It turns out that our coproducts must be #emph[distributive] to allow us to use variables in scope before a branch. In particular, we define a #emph[distributive] premonoidal category as follows:

#block[
A premonoidal category $cal(C)$ with all coproducts is #emph[distributive] if, for all $A   B   C$, the obvious morphism $ delta_(A   B   C) = \[ ( A + iota_l )   ( A + iota_r ) \] : ( A ⊗ B ) + ( A ⊗ C ) arrow.r A ⊗ ( B + C ) $ has an inverse $delta^(- 1)$. We will say a Freyd category $cal(C)$ is distributive if it has all coproducts and the subcategory of pure morphisms $cal(C)_tack.t$ is distributive (which implies, in particular, that $cal(C)$ is distributive when taken as a premonoidal category).

]
We note in particular that every cartesian closed category with coproducts is a distributive Freyd category, as is the Kleisli category of a monad over a CCC with coproducts. For any finite coproduct $Sigma_i B_i$, we will introduce the notation $delta_Sigma : Sigma_i ( A ⊗ B_i ) arrow.r A ⊗ Sigma_i B_i$ and $delta_Sigma^(- 1) : A ⊗ Sigma_i B_i arrow.r Sigma_i ( A ⊗ B_i )$ to denote the obvious morphisms.

This gives us enough machinery to express any #emph[acyclic] control-flow graph, however, we still have no way to model loops. What we would like is to equip our category with an #emph[iteration operator] taking a morphism $f : A arrow.r B + A$, representing a "loop" which, given input $A$, either produces a result $B$ or continues to another iteration with a new $A$, to its #emph[fixpoint] $f^dagger : A arrow.r B$. Naturally, we require that this operator satisfies various properties, and in particular is #emph[strong], that is, compatible with the distributor. Formally, we define a #emph[(strong) Conway iteration operator] as follows:

#block[
A category $cal(C)$ with all coproducts is said to have a #emph[iteration operator] if we can define an operator $( - )^dagger$ taking every morphism $f : A arrow.r B + A$ to a morphism $f^dagger : A arrow.r B$, the #emph[fixpoint] of $f$, with the following property: given $f : A arrow.r B + A$, we have $f^dagger = f ; \[ sans("id")   f^dagger \]$. We say this operator is a #emph[Conway iteration operator] if it additionally satisfies the following properties:

- #emph[Naturality:] given $f : A arrow.r B + A$ and $g : B arrow.r C$, we have $( f ; g + sans("id") )^dagger = f^dagger ; g : A arrow.r C$

- #emph[Dinaturality:] given morphisms $g : A arrow.r B + C$ and $h : C arrow.r B + A$, we have that $( g ; \[ iota_l   h \] )^dagger = g ; \[ sans("id")_B   ( h ; \[ iota_l   g \] )^dagger \]$

- #emph[Codiagonal:] given $f : A arrow.r ( B + A ) + A$, we have $( f^dagger )^dagger = ( f ; \[ sans("id")   iota_r \] )^dagger : A arrow.r B$

If $cal(C)$ is distributive, we say this operator is #emph[strong] if $ forall f : A arrow.r B + A   ( C ⊗ f ; delta^(- 1) )^dagger = C ⊗ f^dagger $ Given a wide subcategory $cal(K) subset.eq cal(C)$, we say $cal(C)$ is #emph[$cal(K)$-uniform] if, for all $h : A arrow.r_(cal(K)) B$, $f : B arrow.r C + B$, and $g : A arrow.r C + A$, we have that $ h ; f = g ; C + h ==> h ; f^dagger = g^dagger $

]
We will call Freyd categories equipped with an appropriate Elgot structure #emph[strong Elgot categories]. In particular, we define

#block[
A Freyd category $cal(C)$ with all coproducts is said to have an #emph[Elgot structure] if it has a Conway iteration operator which is $cal(C)_tack.t$-uniform. If $cal(C)$ is distributive, we say $cal(C)$ is strong Elgot if its iteration operator is strong. In particular, we say a monad is Elgot if its Kliesli category has an Elgot structure. Similarly, we say a #emph[strong] monad is strong Elgot if its Kliesli category has a strong Elgot structure.

]
It turns out that, to check something is a strong Elgot category, we do not need to explicitly verify dinaturality. In particularly, we may verify the following:

#block[
If $( - )^dagger$ is an iteration operator which satisfies naturality and codiagonal and is $cal(K)$-uniform for $cal(K)$ co-Cartesian, then it also satisfies dinaturality.

]
#block[
#emph[Proof.] See Lemma 31 of #cite(<goncharov-18-guarded-traced>, form: "prose")~◻

]
Since in a distributive Freyd category $cal(C)_tack.t$ must be distributive (and hence co-cartesian), dinaturality follows from the other axioms of an Elgot category. Given a distributive Freyd category equipped with a (strong) Elgot structure, we will often want to consider the fixpoint of a morphism $f : R ⊗ A arrow.r B + A$, where our "context" $R$ does not change between iterations. To do this, we first need to build up a morphism $ sans("rcase") ( f ) := sans("let") ( f ) ; pi_l ⊗ ( B + A ) ; delta^(- 1) : R ⊗ A arrow.r R ⊗ B + R ⊗ A $ which computes $f$ and then distributes a copy of the read-only state $R$ to each branch of the result. We may then define the fixpoint $ sans("rfix") ( f ) := ( sans("rcase") ( f ) )^dagger ; pi_r : R ⊗ A arrow.r B $ We consider some more properties of $sans("rcase") ( f )$ and $sans("rfix") ( f )$ in Appendix~#todo[Cross-reference: \@apx:environment.]

== String Diagrams
<string-diagrams>
#emph[String diagrams] provide a graphical calculus for reasoning about (symmetric) monoidal categories, which allows us to succinctly express complex morphisms and rewrites. Since both cartesian and co-cartesian categories are monoidal (with the product and coproduct as tensor, respectively), we can use string diagrams to reason about both. In the co-cartesian case, string diagrams behave much like control-flow diagrams, with boxes representing sub-programs, input wires entry points, and output wires exit points. In particular, a #emph[region] is just a box with a single input wire. Continuing this analogy, we draw the codiagonal morphism $\[ sans("id")_A   sans("id")_A \]$ as joining two wires, and the zero morphism as a wire coming from nowhere, as in Figure~#todo[Cross-reference: \@fig:coproduct-string-diagrams.]

#figure(coproduct-cfg-diagram(),
  caption: [
    A string diagram using the coproduct as symmetric monoidal structure, interpreted as a CFG
  ]
)
<fig:coproduct-string-diagrams>

The power of string diagrams comes from the fact that many syntactically distinct ways to write equal values are obviously graphically equivalent by #emph[isotopy]: essentially, moving boxes and wires around. String diagrams also give us an elegant way to represent and reason about Elgot structures. It turns out that Elgot structures induce a #emph[trace] on the coproduct @hasegawa-trace-02: given $f : A + C arrow.r B + C$, we can define $ sans("Tr")_(A   B)^C ( f ) = iota_l ; \[ f ; B + iota_r \]^dagger = iota_l ; f ; \[ sans("id")   ( iota_l ; f )^dagger \] : A arrow.r B $ Since this satisfies the axioms of a trace over a symmetric monoidal category, we can draw it, and therefore the Elgot operator, as in Figure~#todo[Cross-reference: \@fig:elgot-string-diagrams.] Continuing with the control-flow diagram analogy, such traces can be interpreted as #emph[loops], with the Elgot axioms, now drawn as diagrams in Figure~#todo[Cross-reference: \@fig:elgot-ax-string-diagrams.]

#figure([#figure(elgot-trace-diagram(kind: "trace"),
    caption: [
      The trace of $f : A + C arrow.r B + C$
    ]
  )

  #figure(elgot-trace-diagram(kind: "fixpoint"),
    caption: [
      The fixpoint of $f : A arrow.r B + A$
    ]
  )

  ],
  caption: [
    Representations of the coproduct trace and Elgot structure as string diagrams
  ]
)
<fig:elgot-string-diagrams>

#figure([#figure(conway-axiom-diagram("fixpoint"),
    caption: [
      Fixpoint
    ]
  )

  #figure(conway-axiom-diagram("naturality"),
    caption: [
      Naturality
    ]
  )

  #figure(conway-axiom-diagram("codiagonal"),
    caption: [
      Codiagonal
    ]
  )

  #figure(conway-axiom-diagram("dinaturality"),
    caption: [
      Dinaturality
    ]
  )

  ],
  caption: [
    Representations of the Elgot axioms as string diagrams
  ]
)
<dssa:fig:elgot-ax-string-diagrams>

Unfortunately, unmodified string diagrams do not work for premonoidal categories, and hence for Freyd categories. The reason is because, since not all morphisms are central, premonoidal categories do not in general validate #emph[sliding]. However, this is easy enough to fix: we can postulate a (dashed red) "state" wire which all impure morphisms require as an input and output, as in Figure~#todo[Cross-reference: \@fig:premonoidal-string-diagram.] Since the state wire linearly threads through all impure boxes, it establishes a unique order in which they must be executed; this construction is shown to be sound in #cite(<promonad>, form: "prose"). Pure morphisms do not have a state wire, so a diagram representing a pure morphism will simply have a dashed red "stripe" on the side. This gives us a convenient way to distinguish between string diagrams using the monoidal structure induced by the coproduct and those using the premonoidal structure induced by the tensor product in a category having both (such as a distributive premonoidal category): the latter will have a state wire, while the former will not.

#figure(premonoidal-state-diagram(),
  caption: [
    A string diagram in a premonoidal category, demonstrating the necessity of using a state wire
  ]
)
<fig:premonoidal-string-diagram>

== Semantics
<semantics>
We now have all the ingredients we need to give a semantics to $lambda_(sans("SSA"))$ expressions and regions. In particular, an $lambda_(sans("SSA"))$ expression model of a signature $S g = ( cal(T)   cal(I) )$ consists of:

- An distributive Freyd category $cal(C)$

- A map $⟦ dot.op ⟧$ from base types $X$ to objects $⟦ X ⟧ : bar.v cal(C) bar.v$

- A map $⟦ dot.op ⟧$ from primitive instructions $f in cal(I)_epsilon.alt ( A   B )$ to morphisms $⟦ f ⟧ : ⟦ A ⟧ arrow.r_epsilon.alt ⟦ B ⟧$, where we model a type $A$ as follows:

  - The unit type $upright(bold(1))$ is modelled as the monoidal unit $I$

  - The empty type $upright(bold(0))$ is modelled as the initial object $upright(bold(0))$

  - Products $A ⊗ B$ are modelled as tensor products $⟦ A ⟧ ⊗ ⟦ B ⟧$

  - Sum types $A + B$ are modelled as coproducts $⟦ A ⟧ + ⟦ B ⟧$

If an $lambda_(sans("SSA"))$ expression model additionally has an Elgot structure on $cal(C)$, we will refer to it simply as an $lambda_(sans("SSA"))$ model. We will model #emph[contexts] and #emph[label contexts] as tensor products and coproducts of the denotations of their parameters, respectively, as in Figure~#todo[Cross-reference: \@fig:ssa-ty-sem.]

#figure([$ #box(stroke: black, inset: 3pt, [$ ⟦ A ⟧ : bar.v cal(C) bar.v $]) $ $ ⟦ upright(bold(1)) ⟧ = I #h(2em) ⟦ A ⊗ B ⟧ = ⟦ A ⟧ ⊗ ⟦ B ⟧ #h(2em) ⟦ upright(bold(0)) ⟧ = upright(bold(0)) #h(2em) ⟦ A + B ⟧ = ⟦ A ⟧ + ⟦ B ⟧\
   $ $ #box(stroke: black, inset: 3pt, [$ ⟦ Gamma ⟧ : bar.v cal(C) bar.v $]) $ $ ⟦ dot.op ⟧ = I #h(2em) ⟦ Gamma   x : A ⟧ = ⟦ Gamma ⟧ ⊗ ⟦ A ⟧\
   $ $ #box(stroke: black, inset: 3pt, [$ ⟦ sans(L) ⟧ : bar.v cal(C) bar.v $]) $ $ ⟦ dot.op ⟧ = 0 #h(2em) ⟦ sans(L)   ell ( A ) ⟧ = ⟦ sans(L) ⟧ + ⟦ A ⟧\
   $ $ #box(stroke: black, inset: 3pt, [$ ⟦ Gamma lt.eq Delta ⟧ : ⟦ Gamma ⟧ arrow.r_tack.t ⟦ Delta ⟧ $]) $ $ ⟦ dot.op lt.eq dot.op ⟧ = sans("id")_I #h(2em) ⟦ Gamma   x : A lt.eq Delta ⟧ = pi_l ; ⟦ Gamma lt.eq Delta ⟧ #h(2em) ⟦ Gamma   x : A lt.eq Delta   x : A ⟧ = ⟦ Gamma lt.eq Delta ⟧ ⊗ ⟦ A ⟧\
   $ $ #box(stroke: black, inset: 3pt, [$ ⟦ sans(L) lt.eq sans(K) ⟧ : ⟦ sans(L) ⟧ arrow.r_tack.t ⟦ sans(K) ⟧ $]) $ $ ⟦ dot.op lt.eq dot.op ⟧ = sans("id")_(upright(bold(0))) #h(2em) ⟦ sans(L) lt.eq sans(K)   ell ( A ) ⟧ = ⟦ sans(L) lt.eq sans(K) ⟧ ; iota_ell #h(2em) ⟦ sans(L)   ell ( A ) lt.eq sans(K)   ell ( A ) ⟧ = ⟦ sans(L) lt.eq sans(K) ⟧ + ⟦ A ⟧ $

  ],
  caption: [
    Denotational semantics for $lambda_(sans("SSA"))$ types, contexts, and weakenings
  ]
)
<fig:ssa-ty-sem>

We can now interpret $lambda_(sans("SSA"))$-expressions $Gamma tack.r_epsilon.alt a : A$ over a given signature $S g$ as morphisms $⟦ Gamma ⟧ arrow.r_epsilon.alt ⟦ A ⟧$ using the rules in Figure~#todo[Cross-reference: \@fig:ssa-expr-sem.] Up to this point, both our syntax and semantics are quite standard; in particular:

- Variables $x$ are modelled as projections from the appropriate index in the context's denotation $pi_(Gamma   x) : ⟦ Gamma ⟧ arrow.r_tack.t ⟦ A ⟧$

- Applications of primitive instructions $f #h(0em) a$ are modelled as $⟦ f ⟧$ precomposed with the denotation of $a$.

- Unary $sans("let")$-bindings are modelled by:

  - Duplicating the context using the diagonal morphism $Delta_(⟦ Gamma ⟧)$

  - Passing the right copy of the context through $⟦ Gamma tack.r_epsilon.alt a : A ⟧$ to get an input of type $⟦ Gamma ⟧ ⊗ ⟦ A ⟧ = ⟦ Gamma   x : A ⟧$

  - Passing the result of this through $⟦ Gamma   x : A tack.r_epsilon.alt b : B ⟧$ to get the final result of type $⟦ B ⟧$

- Pairs are modelled by passing the result of the diagonal morphism $Delta_(⟦ Gamma ⟧)$ to $⟦ Gamma tack.r_epsilon.alt a : A ⟧ times.l ⟦ Gamma tack.r_epsilon.alt b : B ⟧$ i.e., first passing the left copy through $⟦ Gamma tack.r_epsilon.alt a : A ⟧$ and then the right copy through $⟦ Gamma tack.r_epsilon.alt b : B ⟧$. By the axioms of a Freyd category, for pure morphisms, this is the same as simply taking the product $⟨ ⟦ Gamma tack.r_epsilon.alt a : A ⟧   ⟦ Gamma tack.r_epsilon.alt b : B ⟧ ⟩$.

- Binary $sans("let")$-bindings are modelled similarly to unary $sans("let")$-bindings, except that after passing the right copy of the context through $⟦ Gamma tack.r_epsilon.alt e : A ⊗ B ⟧$, we re-associate $⟦ Gamma ⟧ ⊗ ( ⟦ A ⟧ ⊗ ⟦ B ⟧ )$ to $( ⟦ Gamma ⟧ ⊗ ⟦ A ⟧ ) ⊗ ⟦ B ⟧ = ⟦ Gamma   x : A   y : B ⟧$ before passing the entire result through $⟦ Gamma   x : A   y : B tack.r_epsilon.alt c : C ⟧$.

- The unit value $( )$ is modelled as the terminal morphism $1_(⟦ Gamma ⟧)$, while $sans("abort") #h(0em) a$ is modelled as the denotation of $a$ postcomposed with the zero morphism $0_(⟦ A ⟧)$. Injections, similarly, are simply modelled as the appropriate coproduct injections.

- A $sans("case")$-expression is modelled by

  - Duplicating the context using the diagonal morphism $Delta_(⟦ Gamma ⟧)$

  - Using the right copy of the context to compute the discriminant using $⟦ Gamma tack.r_epsilon.alt e : A + B ⟧$

  - Applying the inverse distributor $delta^(- 1)$ to obtain a coproduct $⟦ Gamma ⟧ ⊗ ⟦ A ⟧ + ⟦ Gamma ⟧ ⊗ ⟦ B ⟧$

  - Computing $⟦ Gamma   x : A tack.r_epsilon.alt a : C ⟧$ on the right branch and $⟦ Gamma   y : B tack.r_epsilon.alt b : C ⟧$ on the left branch

#figure([$ #box(stroke: black, inset: 3pt, [$ ⟦ Gamma tack.r_epsilon.alt a : A ⟧ : ⟦ Gamma ⟧ arrow.r_epsilon.alt ⟦ A ⟧ $]) $ $ ⟦ Gamma tack.r_epsilon.alt x : A ⟧ & = pi_(Gamma   x)\
  ⟦ Gamma tack.r_epsilon.alt f #h(0em) a : B ⟧ & = ⟦ f ⟧ compose ⟦ Gamma tack.r_epsilon.alt a : A ⟧\
  ⟦ Gamma tack.r_epsilon.alt sans("let") #h(0em) x = a ; #h(0em) b : B ⟧ & = sans("let") ( ⟦ Gamma tack.r_epsilon.alt a : A ⟧ ) ; ⟦ Gamma   x : A tack.r_epsilon.alt b : B ⟧\
  ⟦ Gamma tack.r_epsilon.alt ( a   b ) : A ⊗ B ⟧ & = Delta_(⟦ Gamma ⟧) ; ⟦ Gamma tack.r_epsilon.alt a : A ⟧ times.l ⟦ Gamma tack.r_epsilon.alt b : B ⟧\
  ⟦ Gamma tack.r_epsilon.alt sans("let") #h(0em) ( x   y ) = e ; #h(0em) c : C ⟧ & = sans("let") ( ⟦ Gamma tack.r_epsilon.alt e : A ⊗ B ⟧ ) ; alpha ; ⟦ Gamma   x : A   y : B tack.r_epsilon.alt c : C ⟧\
  ⟦ Gamma tack.r_epsilon.alt ( ) : upright(bold(1)) ⟧ & = 1_(⟦ Gamma ⟧)\
  ⟦ Gamma tack.r_epsilon.alt iota_l #h(0em) a : A + B ⟧ & = ⟦ Gamma tack.r_epsilon.alt a : A ⟧ ; iota_l\
  ⟦ Gamma tack.r_epsilon.alt iota_r #h(0em) b : A + B ⟧ & = ⟦ Gamma tack.r_epsilon.alt b : B ⟧ ; iota_r\
  ⟦ Gamma tack.r_epsilon.alt sans("case") #h(0em) e #h(0em) { iota_l #h(0em) x : a   iota_r #h(0em) y : b } : C ⟧ & = sans("let") ( ⟦ Gamma tack.r_epsilon.alt e : A + B ⟧ ) ; delta_(⟦ Gamma ⟧)^(- 1) ;\
   & #h(2em) \[ ⟦ Gamma   x : A tack.r_epsilon.alt a : C ⟧   ⟦ Gamma   y : B tack.r_epsilon.alt b : C ⟧ \]\
  ⟦ Gamma tack.r_epsilon.alt sans("abort") #h(0em) a : A ⟧ & = ⟦ Gamma tack.r_epsilon.alt a : upright(bold(0)) ⟧ ; 0_(⟦ A ⟧) $ $ upright("where") quad #box(stroke: black, inset: 3pt, [$ pi_(Gamma   x) : ⟦ Gamma ⟧ arrow.r_tack.t ⟦ A ⟧ $]) #h(2em) pi_(( Gamma   x : A )   x) = pi_r #h(2em) pi_(( Gamma   y : B )   x) = pi_l ; pi_(Gamma   x) $

  ],
  caption: [
    Denotational semantics for $lambda_(sans("SSA"))$ expressions
  ]
)
<fig:ssa-expr-sem>

Similarly, if we in fact have an $lambda_(sans("SSA"))$ model, we can interpret $lambda_(sans("SSA"))$ regions $Gamma tack.r r gt.tri sans(L)$ as morphisms $⟦ Gamma ⟧ arrow.r ⟦ sans(L) ⟧$; note that we don't assume anything about the effect of these morphisms. As $sans(L)$ is a coproduct, we can view the result object of a region $r$ as encoding both #emph[data] and #emph[control-flow] information. In particular, we interpret a branch $sans("br") #h(0em) ell #h(0em) a$ as simply the injection of the (pure) expression $Gamma tack.r_tack.t a : A$, our #emph[data], into the element of the coproduct corresponding to $ell$, which encodes the point in control-flow the rest of the program should jump to next. This is in contrast to #emph[expressions], which purely encode data, with no particular instructions on how to use it afterwards. Our interpretation of $sans("let")$-statements and $sans("case")$-statements, given in Figure~#todo[Cross-reference: \@fig:ssa-reg-sem], is exactly the same as that of the corresponding expressions.

Finally, we come to the interpretation of $sans("where")$-statements, which is where the Elgot structure comes in. The semantics of a $sans("where")$-block $Gamma tack.r r #h(0em) sans("where") #h(0em) ( ell_i ( x_i ) : { t_i }   )_i gt.tri sans(L)$ can be broken down into two major components:

- The #emph[terminator] $sans("esem")_(Gamma   sans(L)) ( r ) : ⟦ Gamma ⟧ arrow.r ⟦ sans(L) ⟧ + Sigma_i ⟦ A_i ⟧$, which, given as input the context $⟦ Gamma ⟧$, executes $r$ and then re-associates the output. The output type $⟦ sans(L) ⟧ + Sigma_i ⟦ A_i ⟧$ expresses that $r$ may either:

  - Via the left injection, return immediately, jumping to an enclosing label in $sans(L)$

  - Via the right injection, jump to the $i^(t h)$ basic block $t_i$ in the $sans("where")$-statement by returning a value in $⟦ A_i ⟧$

- The "#emph[loop]" $sans("lsem")_(Gamma   sans(L)) ( ( ell_i ( x_i ) : { t_i }   )_i ) : ⟦ Gamma ⟧ ⊗ Sigma_i ⟦ A_i ⟧ arrow.r ⟦ sans(L) ⟧ + Sigma_i ⟦ A_i ⟧$ which, given as input the context $⟦ Gamma ⟧$ and an input $⟦ A_i ⟧$ for the $i^(t h)$ basic block $t_i$, executes $t_i$ and then re-associates the output. The output type $⟦ sans(L) ⟧ + Sigma_i ⟦ A_i ⟧$ again expresses that control-flow may either exit the $sans("where")$-block (via $⟦ sans(L) ⟧$) or jump to some other basic block (via $Sigma_i ⟦ A_i ⟧$).

We glue these together in the obvious manner to get the semantics for a where-block:

- Compute $sans("let") ( sans("esem")_(Gamma   sans(L)) ( r ) )$, which, given as input the context $⟦ Gamma ⟧$, copies the context, executes \$\\entrymor{r}\$, and then returns the copied context and the output as $⟦ Gamma ⟧ ⊗ ( ⟦ sans(L) ⟧ + Sigma_i ⟦ A_i ⟧ )$

- Distribute the context into each branch of the coproduct, yielding $⟦ Gamma ⟧ ⊗ ⟦ sans(L) ⟧ + ⟦ Gamma ⟧ ⊗ Sigma_i ⟦ A_i ⟧$

- If we are in the left branch, project out the result to yield $⟦ sans(L) ⟧$, and return immediately

- Otherwise, compute $sans("lsem")_(Gamma   sans(L)) ( ( ell_i ( x_i ) : { t_i }   )_i )$ in a loop, passing in a fresh copy of the context each time. This is implemented with $sans("rfix")$.

This simplifies significantly in the case of a $sans("where")$-block defining just a single label, yielding $ ⟦ Gamma tack.r r #h(0em) sans("where") #h(0em) ell ( x ) : { s } gt.tri sans(L) ⟧ = sans("let") ( ⟦ Gamma tack.r r gt.tri sans(L)   ell ( A ) ⟧ ) ; delta^(- 1) ; \[ pi_r   sans("rfix") ( ⟦ Gamma   x : A tack.r s gt.tri sans(L)   ell ( A ) ⟧ ) \] $ In particular, it is a consequence of label weakening (Lemma~#todo[Cross-reference: \@lem:wk]) that, in the case where $s$ does not call $ell$, this simplifies further to $ ⟦ Gamma tack.r r #h(0em) sans("where") #h(0em) ell ( x ) : { s } gt.tri sans(L) ⟧ = sans("let") ( ⟦ Gamma tack.r r gt.tri sans(L)   ell ( A ) ⟧ ) ; delta^(- 1) ; \[ pi_r   ⟦ Gamma   x : A tack.r s gt.tri sans(L) ⟧ \] $

#figure([$ #box(stroke: black, inset: 3pt, [$ ⟦ Gamma tack.r r gt.tri sans(L) ⟧ : ⟦ Gamma ⟧ arrow.r ⟦ sans(L) ⟧ $]) $ $ ⟦ Gamma tack.r sans("br") #h(0em) ell #h(0em) a gt.tri sans(L) ⟧ & = ⟦ Gamma tack.r_tack.t a : A ⟧ ; iota_(sans(L)   ell)\
  ⟦ Gamma tack.r sans("let") #h(0em) x = a ; r gt.tri sans(L) ⟧ & = sans("let") ( ⟦ Gamma tack.r_epsilon.alt a : A ⟧ ) ; ⟦ Gamma   x : A tack.r r gt.tri sans(L) ⟧\
  ⟦ Gamma tack.r sans("let") #h(0em) ( x   y ) = e ; r gt.tri sans(L) ⟧ & = sans("let") ( ⟦ Gamma tack.r_epsilon.alt e : A ⊗ B ⟧ ) ; alpha ; ⟦ Gamma   x : A   y : B tack.r r gt.tri sans(L) ⟧\
  ⟦ Gamma tack.r sans("case") #h(0em) e #h(0em) { iota_l #h(0em) x : r   iota_r #h(0em) y : s } gt.tri sans(L) ⟧ & = sans("let") ( ⟦ Gamma tack.r_epsilon.alt e : A + B ⟧ ) ; delta^(- 1) ;\
   & quad #h(0em) \[ ⟦ Gamma   x : A tack.r r gt.tri sans(L) ⟧   ⟦ Gamma   y : B tack.r s gt.tri sans(L) ⟧ \]\
  ⟦ Gamma tack.r r #h(0em) sans("where") #h(0em) ( ell_i ( x_i ) : { t_i }   )_i gt.tri sans(L) ⟧ & = sans("let") ( sans("esem")_(Gamma   sans(L)) ( r ) ) ; delta^(- 1) ; \[ pi_r   sans("rfix") ( sans("lsem")_(Gamma   sans(L)) ( ( ell_i ( x_i ) : { t_i }   )_i ) ) \] $ $ upright("where") #h(2em) & #box(stroke: black, inset: 3pt, [$ iota_(sans(L)   ell) : ⟦ A ⟧ arrow.r_tack.t ⟦ sans(L) ⟧ $]) #h(2em) #h(2em) #h(2em) iota_(( sans(L)   ell ( A ) )   ell) = iota_r #h(2em) iota_(( sans(L)   kappa ( B ) )   x) = iota_l ; iota_(sans(L)   ell)\
   & #box(stroke: black, inset: 3pt, [$ sans("esem")_(Gamma   sans(L)) ( r ) : ⟦ Gamma ⟧ arrow.r ⟦ L ⟧ + Sigma_i ⟦ A_i ⟧ $])\
   & sans("esem")_(Gamma   sans(L)) ( r ) = ⟦ Gamma tack.r r gt.tri sans(L)   ( ell_i ( A_i )   )_i ⟧ ; alpha_(⟦ sans(L) ⟧ + Sigma_i ⟦ A_i ⟧)^(+)\
   & #box(stroke: black, inset: 3pt, [$ sans("lsem")_(Gamma   sans(L)) ( ell_i ( x_i ) : { t_i }   )_i ) : ⟦ Gamma ⟧ ⊗ Sigma_i ⟦ A_i ⟧ arrow.r ⟦ sans(L) ⟧ + Sigma_i ⟦ A_i ⟧ $])\
   & sans("lsem")_(Gamma   sans(L)) ( ell_i ( x_i ) : { t_i }   )_i ) = delta_Sigma^(- 1) ; \[ ⟦ Gamma   x_i : A_i tack.r t_i gt.tri sans(L)   ( ell_j ( A_j )   )_j ⟧   \]_i ; alpha_(⟦ sans(L) ⟧ + Sigma_i ⟦ A_i ⟧)^(+) $

  ],
  caption: [
    Denotational semantics for $lambda_(sans("SSA"))$ regions
  ]
)
<fig:ssa-reg-sem>

== Metatheory
<metatheory>
We can now begin to state the metatheoretic properties of our denotational semantics. Before we do so, we establish the convention that whenever we have an equation involving the interpretation of a derivation (e.g., $⟦ cal(D) ⟧ = ⟦ cal(D)' ⟧$), we assume that all the derivations (e.g., $cal(D)$ and $cal(D)'$) exist and are well-formed.

We begin with weakening: as shown in Figure~#todo[Cross-reference: \@fig:ssa-ty-sem], weakenings are modelled, essentially, as projections from a larger product $⟦ Gamma ⟧$ to a smaller product $⟦ Delta ⟧$, while label-weakenings are modelled as injections from a smaller coproduct $⟦ sans(L) ⟧$ to a larger coproduct $⟦ sans(K) ⟧$; in particular, in both cases, the morphisms are pure. A simple induction can then be used to derive the following weakening lemmas:

#block[
Given $Gamma lt.eq Gamma'$ and $sans(L)' lt.eq sans(L)$, $sans(K)' lt.eq sans(K)$, we have

+ For all $Gamma lt.eq Delta$, $⟦ Gamma lt.eq Delta ⟧ = ⟦ Gamma lt.eq Gamma' ⟧ ; ⟦ Gamma' lt.eq Delta ⟧$ <itm:varwk>

+ For all $sans(L) lt.eq sans(K)$, $⟦ sans(L)' lt.eq sans(K) ⟧ = ⟦ sans(L)' lt.eq sans(L) ⟧ ; ⟦ sans(L) lt.eq sans(K) ⟧$ <itm:lbwk>

+ $⟦ Gamma tack.r_epsilon.alt a : A ⟧ = ⟦ Gamma lt.eq Gamma' ⟧ ; ⟦ Gamma' tack.r_epsilon.alt a : A ⟧$ <itm:expwk>

+ $⟦ Gamma tack.r r gt.tri sans(L) ⟧ = ⟦ Gamma lt.eq Gamma' ⟧ ; ⟦ Gamma' tack.r r gt.tri sans(L)' ⟧ ; ⟦ sans(L)' lt.eq sans(L) ⟧$ <itm:regwk>

+ For all $gamma : Gamma mapsto Delta$, $⟦ gamma : Gamma mapsto Delta ⟧ = ⟦ Gamma lt.eq Gamma' ⟧ ; ⟦ gamma : Gamma' mapsto Delta ⟧$ <itm:substwk>

+ For all $Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K)$, $⟦ Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) ⟧ = ⟦ Gamma lt.eq Gamma' ⟧ ⊗ ⟦ sans(L) ⟧ ; ⟦ Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K)' ⟧ ; ⟦ sans(K)' lt.eq sans(K) ⟧$ <itm:lbsubstwk>

<lem:wk>

]
#block[
#emph[Proof.] See Appendix~#todo[Cross-reference: \@proof:weakening.]~◻

]
We can now give a denotational semantics to substitutions in which a substitution $gamma : Gamma mapsto Delta$ is interpreted as a pure morphism from $⟦ Gamma ⟧$ to $⟦ Delta ⟧$, as in Figure~#todo[Cross-reference: \@fig:ssa-subst-sem.] We can now state the soundness of variable substitution as follows:

#block[
Given $⟦ gamma : Gamma mapsto Delta ⟧ : ⟦ Gamma ⟧ arrow.r ⟦ Delta ⟧$ pure, we have that

+ $⟦ Gamma tack.r_epsilon.alt \[ gamma \] a : A ⟧ = ⟦ gamma : Gamma mapsto Delta ⟧ ; ⟦ Delta tack.r_epsilon.alt a : A ⟧$ <itm:tm-subst-sound>

+ $⟦ Gamma tack.r \[ gamma \] r gt.tri sans(L) ⟧ = ⟦ gamma : Gamma mapsto Delta ⟧ ; ⟦ Delta tack.r r gt.tri sans(L) ⟧$

+ $⟦ \[ gamma \] rho : Delta mapsto Xi ⟧ = ⟦ gamma : Gamma mapsto Delta ⟧ ; ⟦ rho : Delta mapsto Xi ⟧$

+ $⟦ Gamma tack.r \[ gamma \] sigma : sans(L) arrow.r.squiggly sans(K) ⟧ = ⟦ gamma : Gamma mapsto Delta ⟧ ; ⟦ Delta tack.r sigma : sans(L) arrow.r.squiggly sans(K) ⟧$

<thm:subst-sound>

]
#block[
#emph[Proof.] See Appendix~#todo[Cross-reference: \@proof:soundness-subst.]~◻

]
In particular, this implies that the semantics of substitution composition $\[ gamma \] rho$ is just composition of the denotations of $gamma   rho$. We can derive the following important corollary:

#block[
Given $Gamma tack.r_tack.t a : A$, we have

+ Given $Gamma   x : A tack.r_tack.t b : B$, $ ⟦ Gamma tack.r_epsilon.alt \[ a \/ x \] b : B ⟧ = sans("let") ( ⟦ Gamma tack.r_tack.t a : A ⟧ ) ; ⟦ Gamma   x : A tack.r_epsilon.alt b : B ⟧ = ⟦ Gamma tack.r_epsilon.alt sans("let") #h(0em) x = a ; #h(0em) b : B ⟧ $

+ Given $Gamma   x : A tack.r r gt.tri sans(L)$, we have $ ⟦ Gamma tack.r \[ a \/ x \] r gt.tri sans(L) ⟧ = sans("let") ( ⟦ Gamma tack.r_tack.t a : A ⟧ ) ; ⟦ Gamma   x : A tack.r r gt.tri sans(L) ⟧ = ⟦ Gamma tack.r sans("let") #h(0em) x = a ; r gt.tri sans(L) ⟧ $

<corr:single-subst>

]
#block[
#emph[Proof.] Follows immediately from the fact that $ ⟦ x mapsto a^harpoon.tl : Gamma mapsto Gamma   x : A ⟧ = Delta_(⟦ Gamma ⟧) ; ⟦ Gamma ⟧ ⊗ ⟦ Gamma tack.r_tack.t a : A ⟧ = sans("let") ( ⟦ Gamma tack.r_tack.t a : A ⟧ ) $~◻

]
#figure([$ #box(stroke: black, inset: 3pt, [$ ⟦ gamma : Gamma mapsto Delta ⟧ : ⟦ Gamma ⟧ arrow.r_tack.t ⟦ Delta ⟧ $]) $ $ ⟦ dot.op : Gamma mapsto dot.op ⟧ = !_(⟦ Gamma ⟧) #h(2em) ⟦ gamma   x mapsto e : Gamma mapsto Delta   x : A ⟧ = Delta_(⟦ Gamma ⟧) ; ⟦ gamma : Gamma mapsto Delta ⟧ times.l ⟦ Gamma tack.r_tack.t e : A ⟧ $ $ #box(stroke: black, inset: 3pt, [$ ⟦ Gamma tack.r kappa : sans(L) arrow.r.squiggly sans(K) ⟧ : ⟦ Gamma ⟧ ⊗ ⟦ sans(L) ⟧ arrow.r ⟦ sans(K) ⟧ $]) $ $ ⟦ Gamma tack.r dot.op : dot.op arrow.r.squiggly sans(K) ⟧ = !_(⟦ Gamma ⟧) ⊗ upright(bold(0)) ; lambda ; 0_(sans(K))\
  ⟦ kappa   ell ( x ) mapsto r tack.r Gamma : sans(L)   ell ( A ) arrow.r.squiggly sans(K) ⟧ = delta ; \[ ⟦ kappa tack.r Gamma : sans(L) arrow.r.squiggly sans(K) ⟧   ⟦ Gamma   x : A tack.r r gt.tri sans(K) ⟧ \] $

  ],
  caption: [
    Denotational semantics for $lambda_(sans("SSA"))$ (label) substitutions
  ]
)
<fig:ssa-subst-sem>

We can now move on to stating the metatheoretic properties of label-substitutions in much the same manner. In particular, in Figure~#todo[Cross-reference: \@fig:ssa-subst-sem], we interpret label substitutions $Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K)$ as morphisms taking a copy of the context $⟦ Gamma ⟧$ and an element of the coproduct $⟦ sans(L) ⟧$ to an element of the coproduct $⟦ sans(K) ⟧$, with an arbitrary effect. Label substitution is then sound in general, as stated in the following theorem:

#block[
Given $Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K)$, we have

+ $⟦ Gamma tack.r \[ sigma \] r gt.tri sans(K) ⟧ = sans("let") ( ⟦ Gamma tack.r r gt.tri sans(L) ⟧ ) ; ⟦ Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) ⟧$

+ $⟦ Gamma tack.r \[ sigma \] sigma' : sans(M) arrow.r.squiggly sans(K) ⟧ = Delta_(⟦ Gamma ⟧) ⊗ ⟦ sans(L) ⟧ ; alpha ; ⟦ Gamma ⟧ ⊗ ⟦ Gamma tack.r sigma' : sans(M) arrow.r.squiggly sans(L) ⟧ ; ⟦ Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) ⟧$

]
#block[
#emph[Proof.] See Appendix~#todo[Cross-reference: \@proof:soundness-lsubst]~◻

]
== Equational Theory
<ssec:completeness>
Using the metatheory in the previous section, our goal is now to prove the equational theory given in Section~#todo[Cross-reference: \@sec:equations] sound with respect to any valid $lambda_(sans("SSA"))$ model. Stated more precisely, we have the following:

#block[
We have that

+ $Gamma tack.r_epsilon.alt a approx a' : A ==> ⟦ Gamma tack.r_epsilon.alt a : A ⟧ = ⟦ Gamma tack.r_epsilon.alt a' : A ⟧$ <itm:eqn-sound-expr>

+ $Gamma tack.r r approx r' gt.tri sans(L) ==> ⟦ Gamma tack.r r gt.tri sans(L) ⟧ = ⟦ Gamma tack.r r' gt.tri sans(L) ⟧$ <itm:eqn-sound-region>

+ $gamma approx gamma' : Gamma mapsto Delta ==> ⟦ gamma : Gamma mapsto Delta ⟧ = ⟦ gamma' : Gamma mapsto Delta ⟧$ <itm:eqn-sound-vsubst>

+ $sigma approx sigma' tack.r Gamma : sans(L) arrow.r.squiggly sans(K) ==> ⟦ Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) ⟧ = ⟦ Gamma tack.r sigma' : sans(L) arrow.r.squiggly sans(K) ⟧$ <itm:eqn-sound-lsubst>

]
#block[
#emph[Proof.] See Appendix~#todo[Cross-reference: \@proof:soundness-eqn]~◻

]
Now that we've proved the #emph[soundness] of our equational theory, what remains is to prove that it is #emph[complete], i.e., that every equation which holds in all $lambda_(sans("SSA"))$ models can be derived from it, or, stated more categorically, that our syntax quotiented by the equational theory forms an initial $lambda_(sans("SSA"))$ model. Our strategy for doing this is as follows:

+ We begin by constructing a category of expressions $sans("Th")^⊗ ( Gamma )$ and a category of regions $sans("Th") ( Gamma   sans(L) )$ quotiented by our equational theory, and constructing a functor from the former to the latter.

+ We then show that the category of expressions and the category of regions have the structure of an $lambda_(sans("SSA"))$ expression model and $lambda_(sans("SSA"))$ model, respectively, and hence that expressions may be interpreted in the former and both expressions and regions in the latter.

  To do so, we will first need some notation to talk about the behaviour of the equivalence classes of quotients. Suppose $S$ and $T$ are sets of terms. Then we will write $Gamma tack.r_epsilon.alt S : A$ to mean that for every $a in S$, we have $Gamma tack.r_epsilon.alt a : A$, and similarly we will write $Gamma tack.r_epsilon.alt S approx T : A$ when for all $a in S$ and $b in T$, we have $Gamma tack.r_epsilon.alt a approx b : A$. We generalize in the obvious fashion to regions as well as the case when only one side of an equivalence is a set of terms.

  Then, it will turn out that, for a distinguished variable $square.stroked.tiny$ and label $square.filled.medium$, $ Gamma   square.stroked.tiny : ⟨ Delta ⟩ tack.r_epsilon.alt ⟦ Delta tack.r_epsilon.alt a : A ⟧_(sans("Th")^⊗ ( Gamma )) : A\
  Gamma   square.stroked.tiny : ⟨ Delta ⟩ tack.r ⟦ Delta tack.r_epsilon.alt a : A ⟧_(sans("Th") ( Gamma   sans(L) )) gt.tri sans(L)   square.filled.medium ( A )\
  Gamma   square.stroked.tiny : ⟨ Delta ⟩ tack.r ⟦ Delta tack.r r gt.tri sans(K) ⟧_(sans("Th") ( Gamma   sans(L) )) gt.tri sans(L)   square.filled.medium ( ⟨ sans(K) ⟩ ) $ where packing of contexts into types $⟨ Delta ⟩$ is defined as in Appendix~#todo[Cross-reference: \@apx:records-enums.]

+ Finally, we refine this result to show that $ Gamma   square.stroked.tiny : \[ Delta \] tack.r_epsilon.alt ⟦ Delta tack.r_epsilon.alt a : A ⟧_(sans("Th")^⊗ ( Gamma )) approx ⟨ a ⟩ : A\
  Gamma   square.stroked.tiny : \[ Delta \] tack.r ⟦ Delta tack.r_epsilon.alt a : A ⟧_(sans("Th") ( Gamma   sans(L) )) approx sans("ret") #h(0em) ⟨ a ⟩ gt.tri sans(L)   square.filled.medium ( A )\
  Gamma   square.stroked.tiny : \[ Delta \] tack.r ⟦ Delta tack.r r gt.tri sans(K) ⟧_(sans("Th") ( Gamma   sans(L) )) approx ⟨ r ⟩ gt.tri sans(L)   square.filled.medium ( ⟨ sans(K) ⟩ ) $ where $sans("ret") #h(0em) a := sans("br") #h(0em) square.filled.medium #h(0em) a$. Since the packing operator $⟨ dot.op ⟩$ on terms and regions from Appendix~#todo[Cross-reference: \@apx:records-enums] is injective for pure contexts $sans("eff") ( Gamma ) = tack.t$, and hence in particular for $Gamma = dot.op$, $sans(L) = dot.op$, it follows that in this case the category of expressions and the category of regions are the initial distributive $lambda_(sans("SSA"))$ expression model and $lambda_(sans("SSA"))$ model respectively.

== Expressions
<expressions>
We'll begin by going over the entire proof of completeness for expressions, which is the simpler case. In particular, we may define the category $sans("Th")_epsilon.alt^⊗ ( Gamma )$ of expressions with effect $epsilon.alt$ as follows:

- Objects $bar.v sans("Th")^⊗ ( Gamma ) bar.v$ are types $A   B   C$

- Morphisms $sans("Th")^⊗ ( Gamma )_epsilon.alt ( A   B ) = { e divides Gamma   square.stroked.tiny : A tack.r_epsilon.alt e : B }$ quotiented by $Gamma   square.stroked.tiny : A tack.r_epsilon.alt e approx e' : B$

- Identity $( Gamma   square.stroked.tiny : A tack.r_tack.t square.stroked.tiny : A ) in sans("Th")^⊗ ( Gamma )_epsilon.alt ( A   A )$

- Composition $e ; e' = ( sans("let") #h(0em) square.stroked.tiny = e ; e' )$, which satisfies $ Gamma   square.stroked.tiny : A tack.r_epsilon.alt e : B   quad Gamma   square.stroked.tiny : B tack.r_epsilon.alt e' : C #h(2em) ==> #h(2em) Gamma   square.stroked.tiny : A tack.r_epsilon.alt e ; e' : C $ We may verify that this satisfies the axioms of a category w.r.t. our equational theory

In general, the category of expressions $sans("Th")^⊗ ( Gamma )$ is simply then given by $sans("Th")_top^⊗ ( Gamma )$, which can be viewed as the union of all $sans("Th")_epsilon.alt^⊗ ( Gamma )$.

We now need to equip $sans("Th")_epsilon.alt^⊗ ( Gamma )$ with the structure of a premonoidal category. Obviously, we wish to define the tensor product of types $A$ and $B$ to be simply $A ⊗ B$; we can then begin by defining projections $ Gamma   square.stroked.tiny : A ⊗ B tack.r_epsilon.alt pi_l := sans("let") #h(0em) ( x   y ) = square.stroked.tiny ; x : A #h(2em) Gamma   square.stroked.tiny : A ⊗ B tack.r_epsilon.alt sans("let") #h(0em) ( x   y ) = square.stroked.tiny ; y : B $ By simply using the pair constructor as a cartesian product $⟨ a   b ⟩ = ( a   b )$, this can be shown to endow $sans("Th")_tack.t^⊗ ( Gamma )$ with the structure of a cartesian category, allowing us to define the associators, symmetries, and unitors in the natural manner. If we then define tensor functors $ - ⊗ X : e mapsto sans("let") #h(0em) ( square.stroked.tiny   x ) = square.stroked.tiny ; ( e ; ( square.stroked.tiny   x ) ) #h(2em) X ⊗ - : e mapsto sans("let") #h(0em) ( x   square.stroked.tiny ) = square.stroked.tiny ; ( e ; ( x   square.stroked.tiny ) ) $ we find that $sans("Th")_epsilon.alt^⊗ ( Gamma )$ and hence in particular $sans("Th")^⊗ ( Gamma )$ is endowed with the structure of a Freyd category with pure subcategory $sans("Th")_tack.t^⊗ ( Gamma )$.

Similarly, we wish to show that $A + B$ is the coproduct of $A$ and $B$ in $sans("Th")_epsilon.alt^⊗ ( Gamma )$. Since we already have obvious injection morphisms $ Gamma   square.stroked.tiny : A tack.r_epsilon.alt iota_l := iota_l #h(0em) square.stroked.tiny : A + B #h(2em) Gamma   square.stroked.tiny : B tack.r_epsilon.alt iota_r := iota_r #h(0em) square.stroked.tiny : A + B $ we can define the coproduct of morphisms $Gamma   square.stroked.tiny : A tack.r_epsilon.alt a : C$ and $Gamma   square.stroked.tiny : B tack.r_epsilon.alt b : C$ to be simply given by $ Gamma   square.stroked.tiny : A + B tack.r_epsilon.alt \[ a   b \] := sans("case") #h(0em) square.stroked.tiny #h(0em) { iota_l #h(0em) square.stroked.tiny : a   iota_r #h(0em) square.stroked.tiny : b } : C $ It is straightforward to verify that this indeed induces a coproduct on $sans("Th")_epsilon.alt^⊗ ( Gamma )$ and hence on $sans("Th")^⊗ ( Gamma )$ All that remains is to show that $sans("Th")_epsilon.alt^⊗ ( Gamma )$ is in fact a #emph[distributive] Freyd category. To do so, we may define an inverse distributor morphism $ Gamma   square.stroked.tiny : A ⊗ ( B + C ) tack.r_epsilon.alt delta^(- 1) := sans("let") #h(0em) ( x   y ) = square.stroked.tiny ; sans("case") #h(0em) y #h(0em) { iota_l #h(0em) z : iota_l ( x   z )   iota_r #h(0em) z : iota_r ( x   z ) } : A ⊗ B + A ⊗ C $ which can easily be shown to be an inverse to the obvious distributor morphism. We may now note that $ ⟦ dot.op ⟧_(sans("Th")^⊗ ( Gamma )) = upright(bold(1))   quad ⟦ Delta   x : A ⟧_(sans("Th")^⊗ ( Gamma )) = ⟦ Delta ⟧_(sans("Th")^⊗ ( Gamma )) ⊗ A #h(2em) ==> #h(2em) ⟦ Delta ⟧_(sans("Th")^⊗ ( Gamma )) = ⟨ Gamma ⟩ $ Therefore, it follows that, as expected, that $Gamma   square.stroked.tiny : ⟨ Delta ⟩ tack.r_epsilon.alt ⟦ Delta tack.r_epsilon.alt a : A ⟧_(sans("Th")^⊗ ( Gamma )) : A$ and it remains to show that we in fact have $ Gamma   square.stroked.tiny : ⟨ Delta ⟩ tack.r_epsilon.alt ⟦ Delta tack.r_epsilon.alt a : A ⟧_(sans("Th")^⊗ ( Gamma )) approx \[ a \] : A $ which can be done by a relatively straightforward induction, implying, since $\[ dot.op \]$ is injective w.r.t. our equational theory for pure contexts, the following theorem:

#block[
We have that, for all pure $sans("eff") ( Gamma ) = tack.t$, $ Gamma tack.r_epsilon.alt e approx e' : A arrow.l.r.double ⟦ Gamma tack.r_epsilon.alt e : A ⟧_(sans("Th")^⊗ ( dot.op )) = ⟦ Gamma tack.r_epsilon.alt e' : A ⟧_(sans("Th")^⊗ ( dot.op )) $ In particular, this implies that $sans("Th") ( dot.op )$ is the initial $lambda_(sans("SSA"))$ expression model <thm:complete-expr>

]
#block[
#emph[Proof.] See Appendix~#todo[Cross-reference: \@proof:complete-expr]~◻

]
== Regions
<regions>
We define the category $sans("Th") ( Gamma   sans(L) )$ of regions as follows:

- Objects $bar.v sans("Th") ( Gamma   sans(L) ) bar.v$ types $A   B   C$

- Morphisms $sans("Th") ( Gamma   sans(L) ) ( A   B ) = { r divides Gamma   square.stroked.tiny : A tack.r r gt.tri sans(L)   square.filled.medium ( B ) }$ quotiented by $Gamma   square.stroked.tiny : A tack.r r approx r' gt.tri sans(L)   square.filled.medium ( B )$

- Identity $Gamma   square.stroked.tiny : A tack.r sans("ret") #h(0em) square.stroked.tiny gt.tri sans(L)   square.filled.medium ( A )$ where $sans("ret") #h(0em) a := sans("br") #h(0em) square.filled.medium #h(0em) a$

- Composition $r ; r' = \[ ( square.filled.medium ( square.stroked.tiny ) mapsto r' )^harpoon.tl \] r$

In particular, we may view $sans("ret")$ as an identity-on-objects functor $sans("Th")_tack.t^⊗ ( Gamma ) arrow.r sans("Th") ( Gamma   sans(L) )$ with action on morphisms given by given by $ Gamma   square.stroked.tiny : A tack.r_tack.t e : B #h(2em) mapsto #h(2em) Gamma   square.stroked.tiny ( A ) tack.r sans("ret") #h(0em) e gt.tri sans(L)   square.filled.medium ( B ) $ We will use this to equip $sans("Th") ( Gamma   sans(L) )$ with the structure of a Freyd category. In particular, taking our subcategory of pure morphisms to be the image of $sans("ret")$ in $sans("Th") ( Gamma   sans(L) )$, we may define the obvious tensor functors $ - ⊗ X : r mapsto sans("let") #h(0em) ( square.stroked.tiny   x ) = square.stroked.tiny ; ( r ; sans("ret") #h(0em) ( square.stroked.tiny   x ) ) #h(2em) X ⊗ - : r mapsto sans("let") #h(0em) ( x   square.stroked.tiny ) = square.stroked.tiny ; ( r ; sans("ret") #h(0em) ( x   square.stroked.tiny ) ) $ Our premonoidal structure is then completely described by requiring that $sans("ret")$ preserves all relevant structure, i.e., that we have $ alpha = sans("ret") #h(0em) alpha #h(2em) lambda = sans("ret") #h(0em) lambda #h(2em) rho = sans("ret") #h(0em) rho #h(2em) sigma = sans("ret") #h(0em) sigma #h(2em) Delta = sans("ret") #h(0em) Delta $ Just like for expressions, we can write the coproduct of $Gamma   square.stroked.tiny : A tack.r s gt.tri sans(L)   square.filled.medium ( C )$ and $Gamma   square.stroked.tiny : B tack.r t gt.tri sans(L)   square.filled.medium ( C )$ in $sans("Th") ( Gamma   sans(L) )$ as $ Gamma   square.stroked.tiny : A + B tack.r \[ s   t \] := sans("case") #h(0em) square.stroked.tiny #h(0em) { iota_l #h(0em) square.stroked.tiny : s   iota_r #h(0em) square.stroked.tiny : t } gt.tri sans(L)   square.filled.medium ( C ) $ with the obvious injections $iota_l := sans("ret") #h(0em) iota_l$ and $iota_r = sans("ret") #h(0em) iota_r$. It turns out that in this case $sans("ret")$ preserves coproducts as well, and we can therefore easily conclude that our category is distributive by taking inverse distributor $delta^(- 1) = sans("ret") #h(0em) delta^(- 1)$.

All that remains now is to take $sans("Th") ( Gamma   sans(L) )$ from an $lambda_(sans("SSA"))$ expression model to an $lambda_(sans("SSA"))$ model by giving it an Elgot structure. We do so by defining the fixpoint of a morphism $Gamma   square.stroked.tiny : A tack.r r gt.tri sans(L)   square.filled.medium ( B + A )$ as follows: $ Gamma   square.stroked.tiny : A tack.r r^dagger := sans("br") #h(0em) sans("go") #h(0em) square.stroked.tiny #h(0em) sans("where") #h(0em) sans("go") ( square.stroked.tiny : A ) : { r ; sans("case") #h(0em) square.stroked.tiny #h(0em) { iota_l #h(0em) x : sans("ret") #h(0em) x   iota_r #h(0em) y : sans("br") #h(0em) sans("go") #h(0em) y } } gt.tri sans(L)   square.filled.medium ( B ) $ where $sans("go")$ is an (arbitrary) fresh label. We can verify this indeed satisfies the axioms of an Elgot structure through a somewhat tedious calculation. We may now note that $ ⟦ dot.op ⟧_(sans("Th") ( Gamma   sans(L) )) & = upright(bold(1))   & ⟦ Delta   x : A ⟧_(sans("Th") ( Gamma   sans(L) )) & = ⟦ Delta ⟧_(sans("Th") ( Gamma   sans(L) )) ⊗ A & #h(2em) ==> #h(2em) ⟦ Delta ⟧_(sans("Th") ( Gamma   sans(L) )) & = ⟨ Gamma ⟩\
⟦ dot.op^(+) ⟧_(sans("Th") ( Gamma   sans(L) )) & = upright(bold(0))   & ⟦ sans(K)   ell ( A ) ⟧_(sans("Th") ( Gamma   sans(L) )) & = ⟦ sans(K) ⟧_(sans("Th") ( Gamma   sans(L) )) + A & #h(2em) ==> #h(2em) ⟦ sans(K) ⟧_(sans("Th") ( Gamma   sans(L) )) & = ⟨ sans(K) ⟩ $ and hence that $ Gamma   square.stroked.tiny : ⟨ Delta ⟩ tack.r ⟦ Delta tack.r_epsilon.alt a : A ⟧_(sans("Th") ( Gamma   sans(L) )) gt.tri sans(L)   square.filled.medium ( A ) #h(2em) Gamma   square.stroked.tiny : ⟨ Delta ⟩ tack.r ⟦ Delta tack.r r gt.tri sans(K) ⟧_(sans("Th") ( Gamma   sans(L) )) gt.tri sans(L)   square.filled.medium ( ⟨ sans(K) ⟩ ) $ as expected. It is relatively easy to derive that $ Gamma   square.stroked.tiny : ⟨ Delta ⟩ tack.r ⟦ Delta tack.r_epsilon.alt a : A ⟧_(sans("Th") ( Gamma   sans(L) )) approx sans("ret") #h(0em) ⟨ a ⟩ gt.tri sans(L)   square.filled.medium ( A ) $ by a relatively straightforward induction. A much more tedious induction is required to prove that $ Gamma   square.stroked.tiny : ⟨ Delta ⟩ tack.r ⟦ Delta tack.r r gt.tri sans(K) ⟧_(sans("Th") ( Gamma   sans(L) )) approx \[ r \] gt.tri sans(L)   square.filled.medium ( ⟨ sans(K) ⟩ ) $ since the case for $sans("where")$-statements is particularly complex. With a little bit more book-keeping (which can be found in the mechanization), we can state the completeness theorem as follows:

#block[
We have that, for all pure $sans("eff") ( Gamma ) = tack.t$, $ Gamma tack.r r approx r' gt.tri sans(L) arrow.l.r.double ⟦ Gamma tack.r r gt.tri sans(L) ⟧_(sans("Th") ( dot.op   dot.op )) = ⟦ Gamma tack.r r' gt.tri sans(L) ⟧_(sans("Th") ( dot.op   dot.op )) $ In particular, this implies that $sans("Th") ( dot.op   dot.op )$ is the initial $lambda_(sans("SSA"))$ model. <thm:complete-reg>

]
#block[
#emph[Proof.] See Appendix~#todo[Cross-reference: \@proof:complete-reg]~◻

]
