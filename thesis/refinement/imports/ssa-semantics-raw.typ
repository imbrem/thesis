// Mechanical transcription from:
// papers/isotope/complete-refinement-ssa.tex
// Repository commit: 9480278f2503902f0fa632d05d7f0c8faae893f3
// Sections: SSA Typing and Semantics; Interconversion with lambda_iter
// Source lines: 2573--2955
// Conversion: prose preserved verbatim; LaTeX presentation translated mechanically to Typst.

#import "/lib/prelude.typ": *

= SSA Typing and Semantics
<refall:ssa-typing-and-semantics>
== Typing Rules
<refall:typing-rules-1>
We now turn back to the promises at the end of Section~@refall:sec:ssa-intro
and attempt to give typing rules and denotational semantics for
$lambda_(sans(S S A))$. Recall that the primitive syntactic element of
an $lambda_(sans(S S A))$ program is a #emph[region] $r$, which can be
viewed as a program fragment with a single entry point and multiple exit
points. Consequently, our primitive typing judgement will be of the form
$Gamma^(upright(bold(q))) tack.r_epsilon.alt r gt.tri sans(L)^(upright(bold(Q)))$,
which we will read as stating that “#emph[if] the variables in $Gamma$
are live on entry, with quantity $upright(bold(q))$, #emph[then]
executing the region $r$ jumps to one of the labels in $sans(L)$, with
#emph[leftover] quantities $upright(bold(Q))$.\" Here, $sans(L)$ is a
list of labels $ell_i$, annotated with a single parameter type (multiple
parameters are implemented as a single tuple parameter), and
$upright(bold(Q))$ is a list of quantity vectors $upright(bold(q))_i$
which we call the #emph[quantity matrix].

We may define a weakening judgement on annotated label contexts using
the rules in Figure~@refall:fig:label-wk; the judgement is with respect to a
particular context $Gamma$ used to interpret the quantity vectors in
$upright(bold(Q))$. In particular, weakening allows us to insert
arbitrary labels using skip, as well as weaken the quantities associated
with each using cons. As we can see, a label context is interpreted
w.r.t. a quantity matrix $upright(bold(Q))$, which also depends on the
set of live variables $Gamma$. To extend the set of live variables (e.g.
to type a let-binding), we need to zero-pad the quantity matrix to
obtain its #emph[lifting] $upright(bold(Q))^arrow.t$. In particular, we
define this inductively with $dot.op^arrow.t = dot.op$ and
$\( upright(bold(Q)) ; upright(bold(q)) \)^arrow.t = upright(bold(Q))^arrow.t ; \( upright(bold(q)) \, 0 \)$.
With this, we give typing rules for $lambda_(sans(S S A))$, which we do
in Figure~@refall:fig:ssa-typing.

- We begin with the typing rule for branches, br. This states that, if
  $o$ is a pure expression of type $A$, and
  $ell \( A \)^(upright(bold(q))_l)$ weakens to the label context
  $sans(L)^(upright(bold(Q)))$, where $upright(bold(q))_l$ is the
  quantities left over after typing $o$, then
  $sans(b r) #h(0em) ell #h(0em) o$ is a valid branch into
  $sans(L)^(upright(bold(Q)))$

- Let-bindings are typed using let$""_1$ and let$""_2$, which are
  exactly the same as the corresponding rule for expressions, except
  that we target a label-context, which needs to be lifted (i.e.
  $upright(bold(Q))$ replaced with $upright(bold(Q))^arrow.t$) in the
  premise to deal with the additional variable in the input context.

- Case terminators are typed using case, which is again the same as the
  rule for expressions modulo lifting, except for the fact that the
  discriminator $o$ is required to be pure.

- $sans(w h e r e)$-blocks are typed using where$""_(sans(n o n r e c))$
  and where$""_(sans(r e c))$, which we distinguish since the effect of
  a $sans(w h e r e_(r e c))$ subtree must be iterative. In particular,
  a $sans(w h e r e_(r e c))$ subtree is composed of an entry subtree
  $kappa$, which we take to target the compound label-context
  $sans(L)^(upright(bold(Q))) \, sans(R)^(upright(bold(Q))')$, and, for
  each #emph[sublabel] in $ell_i \( A_i \)^(upright(bold(q_i)))$ in
  $sans(R)^(upright(bold(Q))')$, an associated #emph[subregion] $t_i$
  which, with variables $Gamma^(upright(bold(q))_i)$ plus an argument
  $x_i : A_i$ live on entry, targets the exit labels
  $sans(L)^(upright(bold(Q)))$ or makes a recursive call to
  $sans(R)^(upright(bold(Q))')$. where$""_(sans(n o n r e c))$ simply
  removes the requirement that $epsilon.alt$ be iterative, in exchange
  requiring the $t_i$ to only jump to exit labels in
  $sans(L)^(upright(bold(Q)))$.

#figure([#figure([#block[
    \<$sans(L)$\> ::= $dot.op$ | $sans(L) \, ell \( A \)$

    ]],
    caption: [
    ]
  )

  #figure([#block[
    \<$upright(bold(Q))$\> ::= $dot.op$ |
    $upright(bold(Q)) ; upright(bold(q))$

    ]],
    caption: [
    ]
  )

  ],
  caption: [
    Grammar for label contexts
  ]
)
<refall:fig:label-grammar>

#figure([#block[
#rule-set(
  prooftree(rule(label: msc("nil"), $Gamma tack.r dot.op arrow.r.squiggly dot.op$)),
  prooftree(rule(label: msc("cons"), $Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(K)^(upright(bold(Q)))$, $Gamma^(upright(bold(q))') mapsto Gamma^(upright(bold(q)))$, $Gamma tack.r sans(L)^(upright(bold(Q))) \, ell \( A \)^(upright(bold(q))) arrow.r.squiggly sans(K)^(upright(bold(Q))) \, ell \( A \)^(upright(bold(q))')$)),
  prooftree(rule(label: msc("skip"), $Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(K)^(upright(bold(Q)))$, $\| Gamma \| = \| upright(bold(q)) \|$, $Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(K)^(upright(bold(Q))) \, ell \( A \)^(upright(bold(q)))$)),
)

  ]],
  caption: [
    Rules for weakening label contexts
  ]
)
<refall:fig:label-wk>

#figure([#block[
#rule-set(
  prooftree(rule(label: msc("br"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$, $Gamma^(upright(bold(q))_r) tack.r tack.t o : A$, $Gamma tack.r ell \( A \)^(upright(bold(q))_l) arrow.r.squiggly sans(L)^(upright(bold(Q)))$, $Gamma^(upright(bold(q))) tack.r epsilon.alt sans(b r) #h(0em) ell #h(0em) o gt.tri sans(L)^(upright(bold(Q)))$)),
  prooftree(rule(label: msc("let1"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$, $Gamma^(upright(bold(q))_r) tack.r epsilon.alt o : A$, $Gamma^(upright(bold(q))_l) \, x : A tack.r epsilon.alt t gt.tri sans(L)^(upright(bold(Q))^arrow.t)$, $Gamma^(upright(bold(q))) tack.r epsilon.alt sans(l e t) #h(0em) x = o ; t gt.tri sans(L)^(upright(bold(Q)))$)),
  prooftree(rule(label: msc("let2"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$, $Gamma^(upright(bold(q))_r) tack.r epsilon.alt o : A ⊗ B$, $Gamma^(upright(bold(q))_l) \, x : A \, y : B tack.r epsilon.alt t gt.tri sans(L)^(\( upright(bold(Q))^arrow.t \)^arrow.t)$, $Gamma^(upright(bold(q))) tack.r epsilon.alt sans(l e t) #h(0em) \( x \, y \) = o ; t gt.tri sans(L)^(upright(bold(Q)))$)),
  prooftree(rule(label: msc("case"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$, $Gamma^(upright(bold(q))_r) tack.r tack.t o : A + B$, $Gamma^(upright(bold(q))_l) \, x : A tack.r epsilon.alt tau_l gt.tri sans(L)^(upright(bold(Q))^arrow.t)$, $Gamma^(upright(bold(q))_l) \, y : B tack.r epsilon.alt tau_r gt.tri sans(L)^(upright(bold(Q))^arrow.t)$, $Gamma^(upright(bold(q))) tack.r epsilon.alt sans(c a s e) #h(0em) o #h(0em) { iota_l #h(0em) x : tau_l \, iota_r #h(0em) y : tau_r } gt.tri sans(L)^(upright(bold(Q)))$)),
  prooftree(rule(label: msc("wheremathsfnonrec"), $Gamma^(upright(bold(q))) tack.r epsilon.alt kappa gt.tri sans(L)^(upright(bold(Q))) \, sans(R)^(upright(bold(Q))')$, $forall ell_i \( A_i \)^(upright(bold(q))_i) in sans(R)^(upright(bold(Q))') . Gamma^(upright(bold(q))_i) \, x_i : A_i tack.r epsilon.alt t_i gt.tri sans(L)^(upright(bold(Q))^arrow.t)$, $Gamma^(upright(bold(q))) tack.r epsilon.alt kappa #h(0em) sans(w h e r e)_sans(n o n r e c) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i gt.tri sans(L)^(upright(bold(Q)))$)),
  prooftree(rule(label: msc("wheremathsfrec"), $Gamma^(upright(bold(q))) tack.r epsilon.alt kappa gt.tri sans(L)^(upright(bold(Q))) \, sans(R)^(upright(bold(Q))')$, $epsilon.alt in cal(E)^oo$, $forall ell_i \( A_i \)^(upright(bold(q))_i) in sans(R)^(upright(bold(Q))') . Gamma^(upright(bold(q))_i) \, x_i : A_i tack.r epsilon.alt t_i gt.tri sans(L)^(upright(bold(Q))^arrow.t) \, sans(R)^(upright(bold(Q))'^arrow.t)$, $Gamma^(upright(bold(q))) tack.r epsilon.alt kappa #h(0em) sans(w h e r e)_sans(r e c) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i gt.tri sans(L)^(upright(bold(Q)))$)),
)

  ]],
  caption: [
    Typing rules for $lambda_(sans(S S A))$
  ]
)
<refall:fig:ssa-typing>

== Denotational Semantics
<refall:denotational-semantics>
We give a denotational semantics for $lambda_(sans(S S A))$, targeting
an arbitrary $lambda_(sans(i t e r))$ model. We interpret a derivation
$Gamma^(upright(bold(q))) tack.r_epsilon.alt r gt.tri sans(L)^(upright(bold(Q)))$
as a morphism from the input state, the set of live variables
$⟦ Gamma^(upright(bold(q))) ⟧$, to the
output state, which consists of a label $ell_i$ in $sans(L)$, its
argument $A_i$, and leftover variables $upright(bold(q))_i$ in
$upright(bold(Q))$.

To represent this as a type, we can define the (context-dependent)
#emph[effective type] $\[ Gamma mapsto sans(L) \]$ of an annotated label
context with $\[ Gamma mapsto dot.op \] = upright(bold(0))$ and
$\[ Gamma mapsto sans(L)^(upright(bold(Q))) \, ell \( A \)^(upright(bold(q))) \] = \[ Gamma mapsto sans(L)^(upright(bold(Q))) \] + \[ Gamma^(upright(bold(q))) \] ⊗ A$.
Here, the label is encoded as the branch of the coproduct we end up in,
with each branch carrying the argument and any leftover variables as
data. We may now give a denotational semantics for label contexts and
label weakenings in Figure~@refall:fig:lwk-densem. It is easy to verify that we
can reassociate
$alpha^(+) : cal(C)_tack.t \( ⟦ sans(L)^(upright(bold(Q))) \, sans(R)^(upright(bold(Q))') ⟧ \( Gamma \) \, ⟦ sans(L)^(upright(bold(Q))) ⟧ \( Gamma \) + ⟦ sans(R)^(upright(bold(Q))') ⟧ \( Gamma \) \)$.
We also note that we can apply the associator "pointwise" to reassociate
$alpha^arrow.b : cal(C)_tack.t \( ⟦ \[ Gamma \, x : A mapsto sans(L)^(upright(bold(Q))^arrow.t) \] ⟧ \, ⟦ \[ Gamma mapsto sans(L)^(upright(bold(Q))) \] ⟧ \)$.
The semantics for regions is in Figure~@refall:fig:ssa-densem:

- Branches are interpreted by splitting the context, evaluating the
  argument, and then passing the remainder of the context and the result
  into the appropriate label weakening.

- The denotation of let- and case-statements is exactly the same as for
  expressions, except that we need to re-associate the output object
  from
  $⟦ sans(L)^(Q^arrow.t) ⟧ \( Gamma \, - \)$
  to $⟦ sans(L)^(upright(bold(Q))) ⟧$.

- Non-recursive $sans(w h e r e)$-subtrees are interpreted by the
  denotation of their entry subtree, reassociated to the sum of the exit
  labels $sans(L)^(upright(bold(Q)))$ and sublabels
  $sans(R)^(upright(bold(Q))')$. The exit labels are passed through
  as-is, and the sublabels $ell_i$ are piped to the appropriate
  subregion $t_i$.

- Recursive $sans(w h e r e)$-subtree is as above, except that we take
  the #emph[fixpoint] of the sum of the denotations of the subregions
  viewed as morphisms from
  $⟦ sans(R)^(upright(bold(Q))) ⟧ \( Gamma \)$
  to
  $⟦ sans(L)^(upright(bold(Q))) ⟧ \( Gamma \) + ⟦ sans(R)^(upright(bold(Q))) ⟧ \( Gamma \)$,
  feeding recursive calls back into the where-block's body.

#figure([#block[
  minipage=1.1,scale=0.9
  $ #box(stroke: black, inset: 3pt, [$ ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(K)^(upright(bold(Q))') ⟧ : cal(C)_tack.t \( ⟦ \[ Gamma mapsto sans(L)^(upright(bold(Q))) \] ⟧ \, ⟦ \[ Gamma mapsto sans(K)^(upright(bold(Q))') \] ⟧ \) $])\
  ⟦ Gamma tack.r dot.op arrow.r.squiggly dot.op ⟧ = sans(i d)_(upright(bold(0))) #h(2em) ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) \, ell \( A \)^(upright(bold(q))) arrow.r.squiggly sans(K)^(upright(bold(Q))') \, ell \( A \)^(upright(bold(q))') ⟧ = ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(K)^(upright(bold(Q))') ⟧ + ⟦ Gamma^(upright(bold(q))) mapsto Gamma^(upright(bold(q))') ⟧ ⊗ ⟦ A ⟧\
  ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(K)^(upright(bold(Q))') \, ell \( A \)^(upright(bold(q))) ⟧ = ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(K)^(upright(bold(Q))') ⟧ ; iota_l $

  ]],
  caption: [
    Denotational semantics for label contexts and label weakenings
  ]
)
<refall:fig:lwk-densem>

#figure([#block[
  minipage=1.1,scale=0.9
  $ #box(stroke: black, inset: 3pt, [$ ⟦ Gamma tack.r_epsilon.alt t gt.tri sans(L)^(upright(bold(Q))) ⟧ : cal(C)_epsilon.alt \( ⟦ Gamma^(upright(bold(q))) ⟧ \, \[ Gamma mapsto ⟦ sans(L)^(upright(bold(Q))) ⟧ \] \) $])\
  ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(b r) #h(0em) ell #h(0em) a gt.tri sans(L)^(upright(bold(Q))) ⟧ = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ; - ⊗ ⟦ Gamma^(upright(bold(q))_r) tack.r_tack.t a : A ⟧ ; iota_r ; ⟦ Gamma tack.r ell \( A \)^(upright(bold(q))_l) arrow.r.squiggly sans(L)^(upright(bold(Q))) ⟧\
  ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(l e t) #h(0em) x = o ; t gt.tri sans(L)^(upright(bold(Q))) ⟧ = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ; - ⊗ ⟦ Gamma^(upright(bold(q))_r) tack.r_epsilon.alt o : A ⟧ ; ⟦ Gamma^(upright(bold(q))_l) \, x : A tack.r_epsilon.alt t : sans(L)^(upright(bold(Q))^arrow.t) ⟧ ; alpha^arrow.b\
  ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(l e t) #h(0em) \( x \, y \) = o ; t gt.tri sans(L)^(upright(bold(Q))) ⟧ = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ; - ⊗ ⟦ Gamma^(upright(bold(q))_r) tack.r_epsilon.alt o : A ⊗ B ⟧ ; alpha\
  #h(2em) ; ⟦ Gamma^(upright(bold(q))_l) \, x : A \, y : B tack.r_epsilon.alt t : sans(L)^(\( upright(bold(Q))^arrow.t \)^arrow.t) ⟧ ; alpha^arrow.b ; alpha^arrow.b\
  ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(c a s e) #h(0em) o #h(0em) { iota_l #h(0em) x : tau_l \, iota_r #h(0em) y : tau_r } gt.tri sans(L)^(upright(bold(Q))) ⟧ = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ; - ⊗ ⟦ Gamma^(upright(bold(q))_r) tack.r_tack.t o : A + B ⟧ ; delta^(- 1)\
  #h(2em) ; \[ ⟦ Gamma^(upright(bold(q))_l) \, x : A tack.r_epsilon.alt tau_l : sans(L)^(upright(bold(Q))^arrow.t) ⟧ ; alpha^arrow.b \, ⟦ Gamma^(upright(bold(q))_l) \, y : B tack.r_epsilon.alt tau_r : sans(L)^(upright(bold(Q))^arrow.t) ⟧ ; alpha^arrow.b \]\
  ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt kappa #h(0em) sans(w h e r e)_(sans(n o n r e c)) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i gt.tri sans(L)^(upright(bold(Q))) ⟧ = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt kappa gt.tri sans(L)^(upright(bold(Q))) \, sans(R)^(upright(bold(Q))') ⟧ ; alpha^(+)\
  #h(2em) ; \[ sans(i d)_(⟦ \[ Gamma mapsto sans(L)^(upright(bold(Q))) \] ⟧) \, \[ ⟦ Gamma^(upright(bold(q))_i) \, x_i : A_i tack.r_epsilon.alt t_i : sans(L)^(upright(bold(Q))^arrow.t) ⟧ ; alpha^arrow.b \, \]_(ell_i \( A_i \)^(upright(bold(q))_i) in sans(R)^(upright(bold(Q))')) \]\
  ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt kappa #h(0em) sans(w h e r e)_(sans(r e c)) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i gt.tri sans(L)^(upright(bold(Q))) ⟧ = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt kappa gt.tri sans(L)^(upright(bold(Q))) \, sans(R)^(upright(bold(Q))') ⟧ ; alpha^(+)\
  #h(2em) ; \[ sans(i d)_(⟦ \[ Gamma mapsto sans(L)^(upright(bold(Q))) \] ⟧) \, \[ ⟦ Gamma^(upright(bold(q))_i) \, x_i : A_i tack.r_epsilon.alt t_i : sans(L)^(upright(bold(Q))^arrow.t) \, sans(R)^(upright(bold(Q))'^arrow.t) ⟧ ; alpha^arrow.b ; alpha^(+) \, \]_(ell_i \( A_i \)^(upright(bold(q))_i) in sans(R)^(upright(bold(Q))'))^dagger \] $

  ]],
  caption: [
    Denotational semantics for $lambda_(sans(S S A))$
  ]
)
<refall:fig:ssa-densem>

== Interconversion with $lambda_(sans(i t e r))$
<refall:ssec:interconversion>
When we say that $lambda_(sans(S S A))$ and $lambda_(sans(i t e r))$ are
#emph[equivalent], what we mean is that there are
#emph[semantics-preserving] functions $sans(S S A)$, $sans(E x p r)$ on
derivations satisfying
$ ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(S S A)_(e l l) \( Gamma^(upright(bold(q))) tack.r_epsilon.alt a : A \) gt.tri ell \( A \)^0 ⟧_(cal(M)) & = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt a : A ⟧_(cal(M)) ; alpha ; iota_r\
⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(E x p r) \( Gamma^(upright(bold(q))) tack.r_epsilon.alt r gt.tri sans(L)^(upright(bold(Q))) \) : \[ Gamma mapsto sans(L)^(upright(bold(Q))) \] ⟧_(cal(M)) & = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt r gt.tri sans(L)^(upright(bold(Q))) ⟧_(cal(M)) $
for arbitrary models $cal(M)$. It is easy enough to construct
$sans(E x p r)$: for each derivation, we simply pick a representative
$\( x \, a \) in ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt r gt.tri sans(L)^(upright(bold(Q))) ⟧_(sans(T h \( dot.op \)))$.
Since
$⟦ Gamma^(upright(bold(q))) ⟧_(sans(T h) \( dot.op \)) = \[ Gamma^(upright(bold(q))) \]$,
we may simply define
$sans(E x p r) \( Gamma^(upright(bold(q))) tack.r_epsilon.alt r gt.tri sans(L)^(upright(bold(Q))) \) := sans(l e t) #h(0em) Gamma = x ; #h(0em) a$
where the unpacking of a value $c : \[ Gamma^(upright(bold(q))) \]$ is
defined in the obvious recursive manner (see Appendix~@refall:apx:packing for
details). On the other hand, the function $sans(S S A)$ is just standard
expression compilation presented inductively (the details are in
Appendix~@refall:apx:ssa-roundtrip).
