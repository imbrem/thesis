// Verbatim mechanical transcription from:
// papers/isotope/denotational-semantics-of-ssa.tex
// Repository commit: afa82558acf643f53a3e038e635ed9520ace88c6
// Source sections: Type Theory and Syntactic Metatheory, lines 1222–1614

#import "/lib/prelude.typ": *
#show: chapter.with(title: $lambda_"SSA": "Type Theory"$)

= Type Theory
<sec:typing>
We now give a formal account of $lambda_(sans("SSA"))$, starting with
the types. Our types are first order, and consists of binary sums
$A + B$, products $A ⊗ B$, the unit type $upright(bold(1))$,
and the empty type $upright(bold(0))$, all parameterised over a set of
base types $X in cal(T)$. We write our set of types as
$sans("Ty") \( X \)$.

A (variable) #emph[context] $Gamma$ is a list of #emph[typing
hypotheses] $x : A$, where $x$ is a variable name and $A$ is the type of
that variable. Similarly, we define a #emph[label-context] to be a list
of #emph[labels] $ell \( A \)$, where $A$ is the parameter type that
must be passed on a jump to the label $ell$. The grammar for types,
contexts, and label-contexts is given in Figure~@fig:ssa-types.

#figure([#block[
  #block[
  \<$A \, B \, C$\> ::= $X$ | $A ⊗ B$ | $upright(bold(1))$ |
  $A + B$ | $upright(bold(0))$

  \<$Gamma$\> ::= $dot.op$ | $Gamma \, x : A$

  \<$sans(L)$\> ::= $dot.op$ | $sans(L) \, ell \( A \)$

  ]
  ]],
  caption: [
    Grammar for $lambda_(sans("SSA"))$ types, contexts, and
    label-contexts
  ]
)
<fig:ssa-types>

Our grammar in Figure~[fig:ssa-grammar] was implicitly parameterised over
a set of #emph[primitive instructions] $f in cal(I)$. In particular, for
each pair $A \, B in sans("Ty") \( X \)$ we specify a set of primitive
instructions $f in cal(I) \( A \, B \)$, with a subset of #emph[pure
instructions] $cal(I)_tack.t \( A \, B \)$. To allow us to write
$cal(I)_epsilon.alt$ for an #emph[effect]
$epsilon.alt in { top \, tack.t }$, we denote
$cal(I)_top \( A \, B \) := cal(I) \( A \, B \)$.. In general, we define
$cal(I)_epsilon.alt = union.big_(A \, B) cal(I)_epsilon.alt \( A \, B \)$,
and $cal(I) = union.big_epsilon.alt cal(I)_epsilon.alt$.

We'll call a tuple $S g = \( cal(T) \, cal(I) \)$ of types and
instructions over these types an
#emph[$lambda_(sans("SSA"))$-signature], and, for the rest of this
section, work over a fixed signature.

As shown in Figure~[fig:ssa-grammar], $lambda_(sans("SSA"))$ terms are
divided into two syntactic categories, each associated with a judgement:

- #emph[Expressions] $a \, b \, c \, e$, which are typed with the
  judgement $Gamma tack.r_epsilon.alt a : A$, which says that under the
  typing context $Gamma$, the expression $a$ has type $A$ and effect
  $epsilon.alt$. We say a term is #emph[pure] if it has effect $tack.t$;
  note that whether an expression is pure or not depends both on the
  expression itself and on the purity of the variables used in the
  expression; this is to allow reasoning about impure substitutions.

- #emph[Regions] $r \, s \, t$, which recursively define a
  lexically-scoped SSA program with a single entry and (potentially)
  multiple exits. This is typed with the judgement
  $Gamma tack.r r gt.closed sans(L)$, which states that given that $Gamma$
  is live at the unique entry point, $r$ will either loop forever or
  branch to one of the exit labels in $ell \( A \) in sans(L)$ with an
  argument of type $A$.

The typing rules for expressions are given in
Figure~@fig:ssa-expr-rules. In particular, expressions may be built up
from the following fairly standard primitives:

- A variable $x$ in the context $Gamma$, as typed by var.

- A #emph[primitive instruction] $f in cal(I)_epsilon.alt \( A \, B \)$
  applied to an expression $Gamma tack.r_epsilon.alt a : A$, typed by op

- Unary and binary #emph[let-bindings], typed by let$""_1$ and
  let$""_2$ respectively

- A #emph[pair] of expressions $Gamma tack.r_epsilon.alt a : A$,
  $Gamma tack.r_epsilon.alt b : B$, typed by pair. Operationally, we
  interpret this as executing $a$, and then $b$, and returning the pair
  of their values.

- An empty tuple $\( \)$, which types in any context by unit

- Injections, typed by inl and inr

- Pattern matching on sum types, typed by case. Operationally, we
  interpret this as executing $e$, and then, if $e$ is a left injection
  $iota_l #h(0em) x$, executing $a$ with its value ($x$), otherwise
  executing $b$.

- An operator $sans("abort") #h(0em) e$ allowing us to abort execution
  if given a value of the empty type. Since the empty type is a 0-ary
  sum type, $sans("abort")$ can be seen as a $sans("case")$ with no
  branches. Since the empty type is uninhabited, execution can never
  reach an $sans("abort")$. This can be viewed as a typesafe version
  of the `unreachable` instruction in LLVM IR.

Traditional presentations of SSA use a boolean type instead of sum
types. Naturally, booleans can be encoded with sum types as
$upright(bold(1)) + upright(bold(1))$. If-then-else is then a
$sans("case")$ which ignores the unit payloads, so that
$sans("if") #h(0em) e_1 #h(0em) { e_2 } #h(0em) sans("else") #h(0em) { e_3 } := sans("case") #h(0em) e_1 #h(0em) { iota_l #h(0em) \( \) : e_2 \, iota_r #h(0em) \( \) : e_3 }$.

#todo[Translate the following preserved LaTeX expression-typing rules into native Typst proof trees without changing them.]
#figure([\$\$\\begin{gathered}
      \\boxed{\\Gamma \\vdash\_{\\epsilon} a: {A}} \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{var}}}{\\Gamma(x) = A}{\\Gamma \\vdash\_{\\epsilon} x: {A}} \\qquad
      \\prftree\[r\]{{\\scriptsize\\textsf{op}}}{f \\in \\ensuremath{\\mathcal{I}}\_{\\epsilon}(A, B)}{\\Gamma \\vdash\_{\\epsilon} a: {A}}
        {\\Gamma \\vdash\_{\\epsilon} f\\;a: {B}} \\qquad
      \\prftree\[r\]{{\\scriptsize\\textsf{let\$\_1\$}}}
        {\\Gamma \\vdash\_{\\epsilon} a: {A}}
        {\\Gamma, x : A \\vdash\_{\\epsilon} b: {B}}
        {\\Gamma \\vdash\_{\\epsilon} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = a;\\;b}: {B}} \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{unit}}}{\\Gamma \\vdash\_{\\epsilon} (): {\\ensuremath{\\mathbf{1}}}} \\qquad
      \\prftree\[r\]{{\\scriptsize\\textsf{pair}}}{\\Gamma \\vdash\_{\\epsilon} a: {A}}{\\Gamma \\vdash\_{\\epsilon} b: {B}}
        {\\Gamma \\vdash\_{\\epsilon} (a, b): {A \\otimes B}} \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{let\$\_2\$}}}
        {\\Gamma \\vdash\_{\\epsilon} e: {A \\otimes B}}
        {\\Gamma, x : A, y : B \\vdash\_{\\epsilon} c: {C}}
        {\\Gamma \\vdash\_{\\epsilon} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;(x, y) = e;\\;c}: {C}} \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{inl}}}{\\Gamma \\vdash\_{\\epsilon} a: {A}}
        {\\Gamma \\vdash\_{\\epsilon} \\iota\_l\\;{a}: {A + B}} \\qquad
      \\prftree\[r\]{{\\scriptsize\\textsf{inr}}}{\\Gamma \\vdash\_{\\epsilon} b: {B}}
        {\\Gamma \\vdash\_{\\epsilon} \\iota\_r\\;{b}: {A + B}} \\qquad
      \\prftree\[r\]{{\\scriptsize\\textsf{abort}}}{\\Gamma \\vdash\_{\\epsilon} a: {\\ensuremath{\\mathbf{0}}}}
        {\\Gamma \\vdash\_{\\epsilon} \\ensuremath{\\mathsf{abort}}\\;{a}: {A}} \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{case}}}
        {\\Gamma \\vdash\_{\\epsilon} e: {A + B}}
        {\\Gamma, x : A \\vdash\_{\\epsilon} a: {C}}
        {\\Gamma, y : A \\vdash\_{\\epsilon} b: {C}}
        {\\Gamma \\vdash\_{\\epsilon} \\ensuremath{\\mathsf{case}}\\;e\\;\\{\\iota\_l\\;{x} :a, \\iota\_r\\;{y} :b\\}: {C}}
    
  \\end{gathered}\$\$

  ],
  caption: [
    Rules for typing $lambda_(sans("SSA"))$ expressions
  ]
)
<fig:ssa-expr-rules>

We now move on to #emph[regions], which can be typed as follows:

- A branch to a label $ell$ with pure argument $a$, typed with br.

- Unary and binary #emph[let-bindings], typed by let$""_1$ and
  let$""_2$ respectively

- Pattern matching on sum types, typed by case. Operationally, we
  interpret this as executing the expression $e$, and then, if $e$ is a
  left injection $iota_l #h(0em) x$, executing $r$ with its value ($x$),
  otherwise executing $s$.

- #emph[$sans("where")$-blocks] of the form
  “$r #h(0em) sans("where") #h(0em) \( ell_i \( x_i \) : { t_i } \)_i$\",
  which consist of a collection of mutually recursive regions
  $ell_i \( x_i \) : { t_i }$ and a #emph[terminator region] $r$ which
  may branch to one of $ell_i$ or an exit label.

#todo[Translate the following preserved LaTeX region-typing rules into native Typst proof trees without changing them.]
#figure([\$\$\\begin{gathered}
      \\boxed{\\Gamma \\vdash r \\rhd \\ensuremath{\\mathsf{L}}} \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{br}}}{\\Gamma \\vdash\_{\\bot} a: {A}}{\\ensuremath{\\mathsf{L}}\\;\\ell = A}
        {\\Gamma \\vdash \\ensuremath{\\mathsf{br}}\\;\\ell\\;a \\rhd \\ensuremath{\\mathsf{L}}} \\qquad
      \\prftree\[r\]{{\\scriptsize\\textsf{let\$\_1\$-r}}}
        {\\Gamma \\vdash\_{\\epsilon} a: {A}}
        {\\Gamma, x : A \\vdash r \\rhd \\ensuremath{\\mathsf{L}}}
        {\\Gamma \\vdash \\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = a; r} \\rhd \\ensuremath{\\mathsf{L}}} \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{let\$\_2\$-r}}}
        {\\Gamma \\vdash\_{\\epsilon} e: {A \\otimes B}}
        {\\Gamma, x : A, y : B \\vdash r \\rhd \\ensuremath{\\mathsf{L}}}
        {\\Gamma \\vdash \\ensuremath{\\ensuremath{\\mathsf{let}}\\;(x, y) = e; r} \\rhd \\ensuremath{\\mathsf{L}}} \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{case-r}}}
        {\\Gamma \\vdash\_{\\epsilon} e: {A + B}}
        {\\Gamma, x : A \\vdash r \\rhd \\ensuremath{\\mathsf{L}}}
        {\\Gamma, y : B \\vdash s \\rhd \\ensuremath{\\mathsf{L}}}
        {\\Gamma \\vdash \\ensuremath{\\mathsf{case}}\\;e\\;\\{\\iota\_l\\;{x} :r, \\iota\_r\\;{y} :s\\} \\rhd \\ensuremath{\\mathsf{L}}} \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{cfg}}}
        {\\Gamma \\vdash r \\rhd \\ensuremath{\\mathsf{L}}, (\\ell\_i(A\_i),)\_{i \\in I}}
        {\\forall i \\in I. \\Gamma, x\_i : A\_i \\vdash t\_i \\rhd \\ensuremath{\\mathsf{L}}, (\\ell\_j(A\_j),)\_{j \\in I}}
        {\\Gamma \\vdash r\\;\\ensuremath{\\mathsf{where}}\\;(\\ell\_i(x\_i) :\\{t\_i\\},)\_{i \\in I} \\rhd \\ensuremath{\\mathsf{L}}}
    
  \\end{gathered}\$\$

  ],
  caption: [
    Rules for typing $lambda_(sans("SSA"))$ regions
  ]
)
<fig:ssa-reg-rules>

== Metatheory
<metatheory>
We can now begin to state the syntactic metatheory of
$lambda_(sans("SSA"))$. One of the most important metatheorems, and a
basic sanity check of our type theory, is #emph[weakening];
essentially, if something typechecks in a context $Delta$, and $Gamma$
contains all the variables of $Delta$ (written $Gamma lt.eq Delta$,
pronounced "$Gamma$ #emph[weakens] $Delta$"), then it should typecheck
in the context $Gamma$ as well. Here, the context with fewer variables
appears on the #emph[right], allowing us to compose typing judgements
likeso
$ Gamma lt.eq Delta arrow.r.double.long Delta tack.r r gt.closed sans(L) arrow.r.double.long Gamma tack.r r gt.closed sans(L) $
As our theory has two types of context; we'd also like to define
#emph[label-weakening] $sans(L) lt.eq sans(K)$, which we should be able
to apply in the same manner:
$ Gamma tack.r r gt.closed sans(L) arrow.r.double.long sans(L) lt.eq sans(K) arrow.r.double.long Gamma tack.r r gt.closed sans(K) $
If a region $r$ typechecks with exit labels $sans(L)$, and $sans(K)$
contains every label in $sans(L)$, then $r$ should obviously also
typecheck in $sans(K)$. It follows that in the judgement
$sans(L) lt.eq sans(K)$ the context with fewer labels appears on the
#emph[left]-hand side of the judgement: this corresponds precisely to
the fact that label-weakening (injection into a coproduct) is
semantically dual to variable-weakening (projection from a product), and
hence the order is flipped.

We give the (standard) formal rules for weakening $Gamma lt.eq Delta$,
and their duals, in the first part of Figure @fig:ssa-meta-rules.

- wk-nil and lwk-nil say that the empty (label) context weakens itself,

- wk-skip says that if $Gamma$ weakens $Delta$, then $Gamma \, x : A$
  also weakens $Delta$ for arbitrary (fresh) $x$. Dually, lwk-skip says
  that if $sans(L)$ weakens $sans(K)$, then $sans(L)$ also weakens
  $sans(K) \, ell \( A \)$ for arbitrary (fresh) $ell$.

- wk-cons says that if $Gamma$ weakens $Delta$, then $Gamma$ with
  $x : A$ added weakens $Delta \, x : A$. Likewise, lwk-cons says that
  if $sans(L)$ weakens $sans(K)$, then $sans(L)$ with $ell \( A \)$
  added weakens $sans(K) \, ell \( A \)$.

It is easy to see that (label) weakening defined in this manner induces
a partial order on (label) contexts. Our weakening lemma is then as
follows:

#block[
Given $Gamma lt.eq Delta$, $epsilon.alt lt.eq epsilon.alt'$, we have
that:

+ If $Delta tack.r_epsilon.alt a : A$, then
  $Gamma tack.r_(epsilon.alt') a : A$

+ If $sans(L) lt.eq sans(K)$ and $Delta tack.r r gt.closed sans(L)$, then
  $Gamma tack.r r gt.closed sans(K)$

+ If $gamma : Delta mapsto Xi$, then $gamma : Gamma mapsto Xi$

+ If $Delta tack.r sigma : sans(L) arrow.r.squiggly sans(K)$, then
  $Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K)$

]
#block[
#emph[Proof.] These are formalized as:

+ `Term.Wf.wk` in `Typing/Term/Basic.lean`

+ `Region.Wf.wk` in `Typing/Region/Basic.lean`

+ Follows from `Term.Subst.Wf.comp` in `Typing/Term/Subst.lean`

+ Follows from `Region.Subst.Wf.vsubst` in `Typing/Region/LSubst.lean`

~◻

]
#todo[Translate the following preserved LaTeX weakening and substitution rules into native Typst proof trees without changing them.]
#figure([\$\$\\begin{gathered}
      \\boxed{\\Gamma \\leq \\Delta} \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{wk-nil}}}{}{\\cdot \\leq \\cdot} \\qquad
      \\prftree\[r\]{{\\scriptsize\\textsf{wk-skip}}}{\\Gamma \\leq \\Delta}{\\Gamma, x : A \\leq \\Delta} \\qquad
      \\prftree\[r\]{{\\scriptsize\\textsf{wk-cons}}}{\\Gamma \\leq \\Delta}
        {\\Gamma, x : A \\leq \\Delta, x : A} \\\\
      \\boxed{\\ensuremath{\\mathsf{L}} \\leq \\ensuremath{\\mathsf{K}}} \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{lwk-nil}}}{}{\\cdot \\leq \\cdot} \\qquad
      \\prftree\[r\]{{\\scriptsize\\textsf{lwk-skip}}}{\\ensuremath{\\mathsf{L}} \\leq \\ensuremath{\\mathsf{K}}}{\\ensuremath{\\mathsf{L}} \\leq \\ensuremath{\\mathsf{K}}, \\ell(A)} \\qquad
      \\prftree\[r\]{{\\scriptsize\\textsf{lwk-cons}}}{\\ensuremath{\\mathsf{L}} \\leq \\ensuremath{\\mathsf{K}}}
        {\\ensuremath{\\mathsf{L}}, \\ell(A) \\leq \\ensuremath{\\mathsf{K}}, \\ell(A)} \\\\
      \\boxed{\\gamma: \\Gamma \\mapsto \\Delta} \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{sb-nil}}}{}{\\cdot: \\Gamma \\mapsto \\cdot} \\qquad
      \\prftree\[r\]{{\\scriptsize\\textsf{sb-cons}}}{\\gamma: \\Gamma \\mapsto \\Delta}{\\Gamma \\vdash\_{\\bot} e: {A}}
        {\\gamma, x \\mapsto e: \\Gamma \\mapsto \\Delta, x : A}
         \\\\
      \\boxed{\\Gamma \\vdash \\sigma: \\ensuremath{\\mathsf{L}} \\rightsquigarrow \\ensuremath{\\mathsf{K}}} \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{ls-nil}}}{}{\\Gamma \\vdash \\cdot: \\cdot \\rightsquigarrow \\ensuremath{\\mathsf{K}}}
      \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{ls-cons}}}
        {\\Gamma \\vdash \\sigma: \\ensuremath{\\mathsf{L}} \\rightsquigarrow \\ensuremath{\\mathsf{K}}}{\\Gamma, x : A \\vdash r \\rhd \\ensuremath{\\mathsf{K}}}
        {\\Gamma \\vdash \\sigma: \\ensuremath{\\mathsf{L}} \\rightsquigarrow \\ensuremath{\\mathsf{K}}}
        {\\Gamma \\vdash \\sigma, \\ell(x) \\mapsto r: \\ensuremath{\\mathsf{L}}, \\ell(A) \\rightsquigarrow \\ensuremath{\\mathsf{K}}}
    
  \\end{gathered}\$\$

  ],
  caption: [
    Rules for typing $lambda_(sans("SSA"))$ weakening and substitution
  ]
)
<fig:ssa-meta-rules>

The validity of variable weakening hinges on the fact that all the
variables in $Delta$ are also available with the same type in $Gamma$,
i.e., if
$Delta tack.r_epsilon.alt x : A arrow.r.double.long Gamma tack.r_epsilon.alt x : A$,
then anything which can be typed in $Delta$ can be typed in $Gamma$. So
while weakening on #emph[terms] is just the identity, weakening on
#emph[derivations] is essentially replacing "variables from $Delta$"
with "variables from $Gamma$." Since none of our typing rules, other
than $sans("var")$, make use of variable names, we might ask whether we
can repeat essentially the same reasoning to reason about the
well-typedness of replacing variables in $Gamma$ with arbitrary pure
expressions of the same type (i.e., perform a substitution). An
assignment of such variables $gamma : x mapsto gamma_x$ is called a
#emph[substitution], which we can type with the judgement
$gamma : Gamma mapsto Delta$ as per the rules given in Figure
@fig:ssa-meta-rules. In particular,

- sb-nil says that the empty substitution takes every context to the
  empty context.

- sb-cons says that if $gamma$ takes $Gamma$ to $Delta$ and
  $Gamma tack.r_tack.t e : A$, then $gamma$ with the additional
  substitution $x mapsto e$ adjoined takes $Gamma$ to $Delta \, x : A$

To #emph[use] a substitution, we simply need to perform standard
capture-avoiding substitution (see Figure [fig:ssa-subst-def] in the
appendix). Substitution satisfies the #emph[substitution lemma] as
follows:

#block[
Given $gamma : Gamma mapsto Delta$, we have that:

+ $Delta tack.r_epsilon.alt a : A arrow.r.double.long Gamma tack.r_epsilon.alt \[ gamma \] a : A$

+ $Delta tack.r r gt.closed sans(L) arrow.r.double.long Gamma tack.r \[ gamma \] r gt.closed sans(L)$

+ $gamma_2 : Delta mapsto Xi arrow.r.double.long \[ gamma \] gamma_2 : Gamma mapsto Xi$

+ $sigma tack.r Gamma : sans(L) arrow.r.squiggly sans(K) arrow.r.double.long \[ gamma \] sigma tack.r Delta : sans(L) arrow.r.squiggly sans(K)$

]
#block[
#emph[Proof.] These are formalized as:

+ `Term.Wf.subst` in `Typing/Term/Subst.lean`

+ `Region.Wf.vsubst` in `Typing/Region/VSubst.lean`

+ `Term.Subst.Wf.comp` in `Typing/Term/Subst.lean`

+ `Region.Subst.Wf.vsubst` in `Typing/Region/LSubst.lean`

~◻

]
Note in particular that this allows us to take the #emph[composition]
$\[ gamma' \] gamma : Gamma' mapsto Delta$ of substitutions
$gamma' : Gamma' mapsto Gamma$ and $gamma : Gamma mapsto Delta$; the
composition associates as expected:
$\[ \[ gamma_1 \] gamma_2 \] gamma_3 = \[ gamma_1 \] \( \[ gamma_2 \] gamma_3 \)$,
and has identity $\[ sans("id") \] gamma = gamma$, yielding a category of
substitutions with variable contexts $Gamma$ as objects.

Given a substitution $gamma : Gamma mapsto Delta$ and context $Xi$
disjoint from $Gamma$ and $Delta$, we may define a "left extension"
operation $dot.op_Xi^harpoon.tl$ yielding
$gamma_Xi^harpoon.tl : Xi \, Gamma mapsto Xi \, Delta$ which appends the
identity substitution for each variable in $Xi$ in the obvious manner:
$ gamma_dot.op^harpoon.tl = gamma #h(2em) gamma_(Xi \, x : A)^harpoon.tl = x mapsto x \, gamma_Xi^harpoon.tl $
We may similarly define a "right extension" operation
$dot.op_Xi^harpoon.tr$ yielding
$gamma_Xi^harpoon.tr : Gamma \, Xi mapsto Delta \, Xi$ as follows:
$ gamma_dot.op^harpoon.tr = gamma #h(2em) gamma_(Xi \, x : A)^harpoon.tr = gamma_Xi^harpoon.tr \, x mapsto x $
In particular, we note that the identity substitution on $Gamma$ can be
written as $dot.op_Gamma^harpoon.tr$; in general, we have
$\[ gamma \] a = \[ Gamma_Xi^harpoon.tl \] a = \[ gamma_Xi^harpoon.tr \] a$.
We will usually infer $Xi$ from context.

One other particularly important form of substitution is that of
substituting an expression $a$ for an individual variable $x$, which we
will write $\[ a \/ x \] := \( x mapsto a \)^harpoon.tl$.

Finally, just as we can generalize weakening by substituting expressions
for variables via substitution, we can generalize label weakening by
substituting #emph[labels] for #emph[(parametrized) regions] via
#emph[label substitution]. In particular, a label-substitution
$sigma tack.r Gamma : sans(L) arrow.r.squiggly sans(K)$ maps every label
$ell \( A \) in sans(L)$ to a region
$Gamma \, x : A tack.r r gt.closed sans(K)$ parametrized by $x : A$. As
shown in Figure @fig:ssa-label-subst-def, we may then define
label-substitution recursively in the obvious manner, mapping
$sans("br") #h(0em) ell #h(0em) a$ to $\[ a \/ x \] r$ as a base case.
Composition of label-substitutions is pointwise. This allows us to state
#emph[label substitution] as follows:

#block[
Given $Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K)$, we have
that

+ $Gamma tack.r r gt.closed sans(L) arrow.r.double.long Gamma tack.r \[ sigma \] r gt.closed sans(K)$

+ $Gamma tack.r kappa : sans(L) arrow.r.squiggly sans(J) arrow.r.double.long Gamma tack.r \[ sigma \] kappa : sans(K) arrow.r.squiggly sans(J)$

]
#block[
#emph[Proof.] These are formalized as:

+ `Region.Wf.lsubst` in `Typing/Region/LSubst.lean`

+ `Region.Subst.Wf.comp` in `Typing/Region/LSubst.lean`

~◻

]
We may similarly define left and right extensions
$Gamma tack.r sigma_(sans(K))^harpoon.tl : sans(L) \, sans(J) arrow.r.squiggly sans(K) \, sans(J)$
and
$Gamma tack.r sigma_(sans(K))^harpoon.tr : sans(L) \, sans(J) arrow.r.squiggly sans(K) \, sans(J)$
and for label substitutions
$Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K)$ in the obvious
manner:
$ sigma_dot.op^harpoon.tr = sigma #h(2em) sigma_(sans(K) \, ell \( A \))^harpoon.tr = sigma_(sans(K))^harpoon.tr \, ell \( x \) mapsto sans("br") #h(0em) ell #h(0em) x\
sigma_dot.op^harpoon.tl = sigma #h(2em) sigma_(sans(K) \, ell \( A \))^harpoon.tl = ell \( x \) mapsto sans("br") #h(0em) ell #h(0em) x \, sigma_(sans(K))^harpoon.tl $
As for variable substitutions, we will often omit $sans(L)$ when it is
clear from the context. We also define the shorthand
$\[ ell \/ kappa \] = \[ \( kappa \( x \) mapsto sans("br") #h(0em) ell #h(0em) x \)^harpoon.tl \]$
for single-label substitutions.

#figure([$ \( sigma \, ell \( x \) mapsto r \) \( ell \, a \) = \[ a \/ x \] r #h(2em) \( sigma \, kappa \( x \) mapsto r \) \( ell \, a \) = sigma \( ell \, a \) #h(2em) \( dot.op \) \( ell \, a \) = sans("br") #h(0em) ell #h(0em) a\
  \
  \[ sigma \] \( sans("br") #h(0em) ell #h(0em) a \) = sigma \( ell \, a \) #h(2em) \[ sigma \] \( sans("let") #h(0em) x = a ; r \) = sans("let") #h(0em) x = a ; \[ sigma \] r\
  \[ sigma \] \( sans("let") #h(0em) \( x \, y \) = e ; r \) = sans("let") #h(0em) \( x \, y \) = e ; \[ sigma \] r\
  \[ sigma \] \( sans("case") #h(0em) e #h(0em) { iota_l #h(0em) x : r \, iota_r #h(0em) y : s } \) = sans("case") #h(0em) e #h(0em) { iota_l #h(0em) x : \[ sigma \] r \, iota_r #h(0em) y : \[ sigma \] s }\
  \[ sigma \] \( r #h(0em) sans("where") #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i \) = \( \[ sigma \] r \) #h(0em) sans("where") #h(0em) \( ell_i \( x_i \) : { \[ sigma \] t_i } \, \)_i\
  \
  \[ sigma \] \( dot.op \) = dot.op #h(2em) \[ sigma \] \( sigma' \, ell \( x \) mapsto r \) = \( \[ sigma \] sigma' \, ell \( x \) mapsto \[ sigma \] r \) $

  ],
  caption: [
    Capture-avoiding label substititon for $lambda_(sans("SSA"))$
    regions and label substitutions; in particular, we assume bound
    variables and labels are $alpha$-converted so as not to appear in
    $sigma$.
  ]
)
<fig:ssa-label-subst-def>
