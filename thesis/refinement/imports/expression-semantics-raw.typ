// Mechanical transcription from:
// papers/isotope/complete-refinement-ssa.tex
// Repository commit: 9480278f2503902f0fa632d05d7f0c8faae893f3
// Section: Semantics of lambda_iter Expressions
// Source lines: 2255--2572
// Conversion: prose preserved verbatim; LaTeX presentation translated mechanically to Typst.

#import "/lib/prelude.typ": *

== Semantics of $lambda_(sans(i t e r))$ Expressions
<refall:semantics-of-lambda_ensuremathmathsfiter-expressions>
We now give the semantics of each of our term formers in
Figure~@refall:fig:expr-densem by induction on derivations; we write
$⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt a : A ⟧$
to denote the appropriate derivation/sub-derivation. Each of them
corresponds quite closely to the the underlying categorical structure.
In particular,

- We intepret a variable $x$ of type $A$ as the weakening
  $Gamma^(upright(bold(q))) mapsto x : A^1$; this discards all other
  variables from the input environment.

- Let-bindings and pairs are interpreted as sequencing, with, in the
  former case, the output of the first term being passed as an input to
  the second. In both cases, we use context-splitting to apportion the
  variables between the two terms.

- Units are interpreted as the weakening
  $Gamma^(upright(bold(q))) mapsto dot.op$, i.e., discarding all
  variables.

- Case statements are interpreted by passing the result of the
  discriminator into the coproduct of the branches, after
  context-splitting to apportion the variables between the discriminator
  and branches. We use the distributor to thread the variables into both
  branches of the coproduct, as discussed.

- Injections and $sans(a b o r t)$ are interpreted trivially as the
  injections and the zero morphism respectively, post-composed with
  their argument.

- To interpret iteration, after splitting the context, we interpret the
  initial value, and then feed that into the fixpoint of the body
  (computed using the Conway iteration operator) along with the
  remainder of the context.

We use the
$⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt a : A ⟧$
notation, rather than specifying a particular derivation, because
#emph[coherence] holds:

#block[
Given derivations $D$ for
$Gamma^(upright(bold(q))) tack.r_epsilon.alt a : A$ and $D'$ for
$Gamma^(upright(bold(q))) tack.r_(epsilon.alt') a : A$, we have
$⟦ D ⟧ = ⟦ D' ⟧$

]
Observe that the coherence theorem allows us to omit the effect
$epsilon.alt$, because the effect is a property of the semantics: the
same term with two different effect typings will have the same
denotation.

#figure([#fit-to-width([#block[
  $ #box(stroke: black, inset: 3pt, [$ ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt a : A ⟧ : cal(C)_epsilon.alt \( ⟦ Gamma^(upright(bold(q))) ⟧ \, ⟦ A ⟧ \) $])\
  ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt x : A ⟧ = ⟦ Gamma^(upright(bold(q))) mapsto x : A_epsilon.alt^1 ⟧ #h(2em) ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt f #h(0em) a : B ⟧ = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt a : A ⟧ ; ⟦ f ⟧\
  ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(l e t) #h(0em) x = a ; #h(0em) b : B ⟧ = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ; ⟦ Gamma^(upright(bold(q))_l) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_r) tack.r_epsilon.alt a : A ⟧ ; ⟦ Gamma^(upright(bold(q))_l) \, x : A tack.r_epsilon.alt b : B ⟧\
  ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt \( a \, b \) : A ⊗ B ⟧ = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ; ⟦ Gamma^(upright(bold(q))_l) tack.r_epsilon.alt a : A ⟧ times.l ⟦ Gamma^(upright(bold(q))_r) tack.r_epsilon.alt b : B ⟧ #h(2em) ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt \( \) : upright(bold(1)) ⟧ = ⟦ Gamma^(upright(bold(q))) mapsto dot.op ⟧ $
  $ ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(l e t) #h(0em) \( x \, y \) = a ; #h(0em) c : C ⟧ = & #h(0em) ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ; ⟦ Gamma^(upright(bold(q))_l) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_r) tack.r_epsilon.alt a : A ⊗ B ⟧ ; alpha ; ⟦ Gamma^(upright(bold(q))_l) \, x : A \, y : B tack.r_epsilon.alt c : C ⟧ $
  $ ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(c a s e) #h(0em) e #h(0em) { iota_l #h(0em) x : a \, iota_r #h(0em) y : b } : C ⟧ = & #h(0em) ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ; ⟦ Gamma^(upright(bold(q))_l) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_r) tack.r_epsilon.alt e : A + B ⟧ ; delta^(- 1)\
   & ; \[ ⟦ Gamma^(upright(bold(q))_l) \, x : A tack.r_epsilon.alt a : C ⟧ \, ⟦ Gamma^(upright(bold(q))_l) \, y : B tack.r_epsilon.alt b : C ⟧ \] $
  $ ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt iota_l #h(0em) a : A + B ⟧ = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt a : A ⟧ ; iota_l #h(2em) ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt iota_r #h(0em) b : A + B ⟧ = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt b : B ⟧ ; iota_r\
  ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(a b o r t) #h(0em) a : A ⟧ = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt a : upright(bold(0)) ⟧ ; 0_A $
  $ ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(i t e r) #h(0em) a #h(0em) { iota_r #h(0em) x : b } : B ⟧ & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ; ⟦ Gamma^(upright(bold(q))_l) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_r) tack.r_epsilon.alt a : A ⟧\
   & ; \( ⟦ Gamma tack.r upright(bold(q))_l = upright(bold(q))_l + upright(bold(q))_l ⟧ ⊗ ⟦ A ⟧ ; alpha ; ⟦ Gamma^(upright(bold(q))_l) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_l) \, x : A tack.r_epsilon.alt b : B + A ⟧ ; delta^(- 1) \)^dagger\
   & ; ⟦ Gamma^(upright(bold(q))_l) mapsto dot.op ⟧ ⊗ ⟦ B ⟧ ; rho $

  ]])],
  caption: [
    Denotational semantics for $lambda_(sans(i t e r))$ expressions
  ]
)
<refall:fig:expr-densem>

==== Weakening
<refall:weakening>
As a sanity check on our semantics, we can verify that it satisfies
#emph[weakening] by a straightforward induction, stated as follows:

#block[
Given $Gamma^(upright(bold(q))) mapsto Delta^(upright(bold(q))')$ and
$Delta^(upright(bold(q))') tack.r_epsilon.alt a : A$, we have that
$ ⟦ Gamma^(upright(bold(q))) mapsto Delta^(upright(bold(q))') ⟧ ; ⟦ Delta^(upright(bold(q))') tack.r_epsilon.alt a : A ⟧ = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt a : A ⟧ $

]
==== Substitution
<refall:substitution>
We proceed to give a semantics for substitution in
Figure~@refall:fig:subst-den. We split up the input context into subcontexts
for each #emph[used] variable, which are then simply interpreted using
their denotation. Unused variables are simply represented via the left
unitor. We can then state soundness of substitution in the following
manner, which is standard except that we prove an #emph[inequality]
whose direction is determined by the commutativity of the effects of the
term and of the substitution.

#figure([#fit-to-width([#block[
  $ #box(stroke: black, inset: 3pt, [$ ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sigma gt.tri Delta^(upright(bold(q))') ⟧ : cal(C)_epsilon.alt \( ⟦ Gamma^(upright(bold(q))) ⟧ \, ⟦ Delta^(upright(bold(q))') ⟧ \) $])\
  ⟦ dot.op tack.r_epsilon.alt dot.op gt.tri dot.op ⟧ = sans(i d)_I\
  ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sigma \, x mapsto a gt.tri Delta^(upright(bold(q))') \, x : A^q ⟧ = {⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ; ⟦ Gamma_(upright(bold(e))_l)^(upright(bold(q))_l) tack.r_epsilon.alt sigma gt.tri Delta^(upright(bold(q))') ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_r) tack.r_epsilon.alt a : A ⟧ upright(" if ") q eq.not 0\
  ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sigma gt.tri Delta^(upright(bold(q))') ⟧ ; lambda^(- 1) upright(" otherwise") $

  ]])],
  caption: [
    Semantics of $lambda_(sans(i t e r))$ substitutions
  ]
)
<refall:fig:subst-den>

#block[
Given
$Gamma^(upright(bold(q))) tack.r_eta sigma gt.tri Delta^(upright(bold(q')))$
and $Delta^(upright(bold(q))') tack.r_epsilon.alt a : A$, we have
$ eta harpoon.rt epsilon.alt arrow.r.double.long ⟦ Gamma^(upright(bold(q))) tack.r_eta sigma gt.tri Delta^(upright(bold(q'))) ⟧ ; ⟦ Delta^(upright(bold(q))') tack.r_epsilon.alt a : A ⟧ arrow.r.twohead ⟦ Gamma^(upright(bold(q))) tack.r_() \[ sigma \] a : A ⟧\
eta harpoon.lb epsilon.alt arrow.r.double.long ⟦ Gamma^(upright(bold(q))) tack.r_eta sigma gt.tri Delta^(upright(bold(q'))) ⟧ ; ⟦ Delta^(upright(bold(q))') tack.r_epsilon.alt a : A ⟧ gt.eq ⟦ Gamma^(upright(bold(q))) tack.r_() \[ sigma \] a : A ⟧ $

]
==== Soundness
<refall:soundness>
Now that we have given our terms a denotational semantics, we would like
to show that our refinement theory is #emph[sound] w.r.t. this
semantics. In particular, as we allow a refinement theory to be
parametrized by set of base refinements $cal(R)$, we need to be able to
express whether a model $cal(M)$ satisfies these refinements. To do so,
we introduce the notion of a model #emph[validating] a typed refinement
family as follows:

#block[
We say a model $cal(M)$ #emph[validates] a typed refinement family
$cal(R)$, written $cal(M) tack.r.double cal(R)$, if, for all
$\( Gamma^(upright(bold(q))) tack.r_() a arrow.r.twohead b : A \) in cal(R)$
we have that
$⟦ Gamma tack.r_epsilon.alt a : A ⟧ arrow.r.twohead ⟦ Gamma tack.r_epsilon.alt b : A ⟧$

]
We note that, for every model $cal(M)$, $cal(M) tack.r.double diameter$.
We can then phrase soundness as follows: if $cal(M)$ models $cal(R)$,
for every refinement in the #emph[theory] generated by $cal(R)$,
$sans(T h) \( cal(R) \)$, $cal(M)$ validates that refinement. Or, more
formally,

#block[
We have that
$cal(M) tack.r.double cal(R) arrow.l.r.double cal(M) tack.r.double sans(T h) \( cal(R) \)$.
That is, given $cal(M) tack.r.double cal(R)$ and
$Gamma^(upright(bold(q))) tack.r_(cal(R)) a arrow.r.twohead b : A$, we
have
$⟦ Gamma tack.r_epsilon.alt a : A ⟧_(cal(M)) arrow.r.twohead ⟦ Gamma tack.r_epsilon.alt b : A ⟧_(cal(M))$.

]
In particular, we hence have that, for every model $cal(M)$,
$cal(M) tack.r.double sans(T h) \( diameter \)$, validating our
equational theory.

==== Syntactic Models and Completeness
<refall:syntactic-models-and-completeness>
We now wish to show that our equational theory is #emph[complete] with
respect to our denotational semantics; that is, if some refinement holds
for every $cal(M) tack.r.double cal(R)$, then this refinement is in fact
contained in $sans(T h) \( cal(R) \)$. We will do this by constructing
an #emph[initial] model $sans(T m) \( cal(R) \)$, the #emph[syntactic
model], such that the following theorem holds:

#block[
If
$⟦ Gamma tack.r_() a : A ⟧_(sans(T m) \( cal(R) \)) arrow.r.twohead ⟦ Gamma tack.r_() b : A ⟧_(sans(T m) \( cal(R) \))$,
then $Gamma tack.r_(cal(R)) a arrow.r.twohead b : A$

]
It then follows from soundness and the existence of
$sans(T m) \( cal(R) \)$ that
$Gamma tack.r_(cal(R)) a arrow.r.twohead b : A$ #emph[if and only if]
for all models $cal(M) tack.r.double cal(R)$,
$⟦ Gamma tack.r_() a : A ⟧_(cal(M)) arrow.r.twohead ⟦ Gamma tack.r_() b : A ⟧_(cal(M))$,
as desired.

We now proceed to give a sketch of the construction of
$sans(T m) \( cal(R) \)$ and the proof of completeness; full details are
given in Appendix~#todo[Cross-reference: `refall:apx:completeness`]. As is standard, our syntactic model
$sans(T m) \( cal(R) \)$ will have types as objects. To construct
morphisms, we start with terms with a single free variable. We stratify
these terms by type and effect as follows:
$ sans(T e r m) \( cal(R) \)_epsilon.alt \( A \, B \) := { \( x \, a \) divides x : A^top tack.r_epsilon.alt a : B } $
We will quotient each $sans(T e r m)_epsilon.alt \( cal(R) \)$ by term
equivalence $approx_(cal(R))$, as well as by renaming the free variable
$x$, to define $sans(T m) \( cal(R) \)_epsilon.alt$; we will somewhat
suggestively write quotiented pairs $\( x \, a \)$ as lambda-expressions
$lambda x . a$, with $\( lambda x . a \) \( y \) = \[ y \/ x \] a$
yielding a term up to equivalence. The identity morphism is simply given
as $sans(i d)_A = \( lambda x . x \)$, while composition is given not by
substitution (since terms may be impure!) but rather by let-bindings as
follows:
$ \( lambda x . a \) ; \( lambda y . b \) := \( lambda x . sans(l e t) #h(0em) y = a ; #h(0em) b \) $
We can equip $sans(T m) \( cal(R) \)$ with the structure of a
poset-enriched category by using the refinement relation as a partial
order; it is trivial to see that this is well-defined. The rest of the
structure of a $lambda_(sans(i t e r))$-model is given in
Appendix~#todo[Cross-reference: `refall:apx:syn-model`]. To prove completeness, it then suffices to show
that $⟦ dot.op ⟧_(sans(T m) \( cal(R) \))$
#emph[reflects] refinement. The details of how to do so are given in
Appendix~#todo[Cross-reference: `refall:apx:packing`].
