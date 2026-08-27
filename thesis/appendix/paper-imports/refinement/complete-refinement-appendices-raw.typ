// Mechanical transcription from:
// papers/isotope/complete-refinement-ssa.tex
// Repository commit: 9480278f2503902f0fa632d05d7f0c8faae893f3
// Sections: all appendices
// Source lines: 3309--end
// Conversion: prose preserved verbatim; LaTeX presentation translated mechanically to Typst.

#import "/lib/prelude.typ": *
= Refinement Rules and Notation
<refall:refinement-rules-and-notation>
We begin by giving the congruence rules for $lambda_(sans(i t e r))$ in
Figure~@refall:fig:congruence-refinement, which completes our presentation of
$lambda_(sans(i t e r))$'s type theory. We now wish to go over some
basic derivable refinement rules, which we will make use of throughout
the rest of the appendix. We begin with some useful lemmas and
notational conventions:

- $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r arrow.l.r.double Gamma tack.r upright(bold(q)) = upright(bold(q))_r + upright(bold(q))_l$

- We will write $Gamma^0$ to mean the variable context $Gamma$ with
  every variable having the zero quantity $0$. In particular, we note
  that $Gamma tack.r upright(bold(q)) = 0 + upright(bold(q))$ and
  $Gamma tack.r upright(bold(q)) = 0 + upright(bold(q))$ are always
  derivable.

Recall that we define $a ; b := sans(l e t) #h(0em) x = a ; #h(0em) b$
for $x in.not sans(f v) \( b \)$. The following typing rule is hence
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
trivially derivable: \$\$\\prftree\[r\]{{\\scriptsize\\textsf{seq}}}
    {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l} \\vdash\_{\\epsilon} a: {A}}
    {0 \\leq \\ensuremath{\\mathsf{q}}(A)}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} b: {B}}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} a ; b: {B}}\$\$
We can easily convince ourselves that this satisfies some of the basic
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
properties of sequencing; for example, we have \$\$\\prftree\[r\]{}
    {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_c}
    {\\Gamma \\vdash \\ensuremath{\\mathbf{q}}\_c = \\ensuremath{\\mathbf{q}}\_r + \\ensuremath{\\mathbf{q}}\_m}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l} \\vdash\_{\\epsilon} a: {A}}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}\_m} \\vdash\_{\\epsilon} b: {B}}
    {0 \\leq \\ensuremath{\\mathsf{q}}(A), \\ensuremath{\\mathsf{q}}(B)}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} c: {C}}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} (a ; b) ; c \\approx a ; (b ; c) : {C}}\$\$

As stated in Section~@refall:ssec:refinement-theory, binding rules for the rest
of our calculus are derivable from the rest of
$lambda_(sans(i t e r))$'s refinement rules. We give these explicitly in
Figure~@refall:fig:derivable-binding, along with the $eta$-rule for unary
let-bindings, which is similarly derived from let$""_1$-$beta$. We note
the commutativity requirement for pair-right-bind, since on the
left-hand side $a$ executes before $b$, while on the right-hand side $b$
executes before $a$, hence the requirement that their effects commute.
We can also derive a simplified rule for uniformity, given below, by
simply choosing $q_l = q_c$ and $c = z$ in unif$""^p$:
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
\$\$\\begin{gathered}
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
    \\prftree\[r\]{{\\scriptsize\\textsf{simp-unif\$^p\$}}}
      {\\eta \\rightharpoonup\\epsilon}
      {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;y = s;\\;b} \\twoheadrightarrow^{p} \\ensuremath{\\mathsf{case}}\\;b\'\\;\\{\\iota\_l\\;{x} :\\iota\_l\\;{x}, \\iota\_r\\;{x} :\\iota\_r\\;{s}\\} : {B + S}}
      {
        \\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = a;\\;\\ensuremath{\\mathsf{iter}}\\;s\\;\\{ \\iota\_r\\;{y} :b \\}} \\twoheadrightarrow^{p} \\ensuremath{\\mathsf{iter}}\\;a\\;\\{ \\iota\_r\\;{x} :b\' \\} : {B}
      } \\\\
    \\text{where} \\qquad {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r} \\qquad
    \\ensuremath{\\mathsf{q}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}) = \\top \\qquad
    \\epsilon \\in \\ensuremath{\\mathcal{E}}^\\infty \\qquad {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} a: {A}}
    \\\\
    \\qquad {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\eta} s: {S}}
    \\qquad {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, y : S \\vdash\_{\\epsilon} b: {B + A}}
    \\qquad {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{} b\': {B + A}}
  
\\end{gathered}\$\$

We define #emph[pattern binding] $sans(l e t) #h(0em) P = a ; #h(0em) b$
of patterns $P : := x divides \( P \, P' \)$ inductively as follows
(with bindings of variables $x$ and pairs $\( x \, y \)$ defined as
normally):
$ sans(l e t) #h(0em) \( P \, y \) = a ; #h(0em) b & := sans(l e t) #h(0em) \( x \, y \) = a ; #h(0em) sans(l e t) #h(0em) P = x ; #h(0em) b & upright("for ") P in.not sans(V a r) \, x in.not sans(f v) \( b \)\
sans(l e t) #h(0em) \( x \, P \) = a ; #h(0em) b & := sans(l e t) #h(0em) \( x \, y \) = a ; #h(0em) sans(l e t) #h(0em) P = y ; #h(0em) b & upright("for ") P in.not sans(V a r) \, y in.not sans(f v) \( b \)\
sans(l e t) #h(0em) \( P \, P' \) = a ; #h(0em) b & := sans(l e t) #h(0em) \( x \, y \) = a ; #h(0em) sans(l e t) #h(0em) P = x ; #h(0em) sans(l e t) #h(0em) P' = y ; #h(0em) b & upright("for ") P \, P' in.not sans(V a r) $
By a straightforward case analysis, we may show that the following rule
is admissible:
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
\$\$\\prftree\[r\]{{\\scriptsize\\textsf{pattern-pair\'}}}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;(P, P\') = x;\\;a}: {B}}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;(P, P\') = a;\\;b} \\approx\\ensuremath{\\ensuremath{\\mathsf{let}}\\;(x, y) = a;\\;\\ensuremath{\\ensuremath{\\mathsf{let}}\\;P = x;\\;\\ensuremath{\\ensuremath{\\mathsf{let}}\\;P\' = y;\\;b}}} : {B}}\$\$
We extend pattern binding to other binding forms, for
$P in.not sans(V a r)$, in the obvious manner:
$ sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) P : b \, iota_r #h(0em) y : c } & := sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) x : sans(l e t) #h(0em) P = x ; #h(0em) b \, iota_r #h(0em) y : c } & upright("for ") x in.not sans(f v) \( b \)\
sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) x : b \, iota_r #h(0em) P : c } & := sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) x : b \, iota_r #h(0em) y : sans(l e t) #h(0em) P = y ; #h(0em) c } & upright("for ") y in.not sans(f v) \( c \)\
sans(i t e r) #h(0em) a #h(0em) { iota_r #h(0em) P : b } & := sans(i t e r) #h(0em) a #h(0em) { iota_r #h(0em) x : sans(l e t) #h(0em) P = x ; #h(0em) b } & upright("for ") x in.not sans(f v) \( b \) $

#figure([#block[
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
  minipage=1.1,scale=0.9 \$\$\\begin{gathered}
      \\prftree\[r\]{{\\scriptsize\\textsf{var}}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\mapsto x : A^q\_\\epsilon}
        {1 \\leq q}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} x \\twoheadrightarrow x : {A}} \\qquad
      \\prftree\[r\]{{\\scriptsize\\textsf{op}}}
        {f : A \\to\_\\epsilon B}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} a \\twoheadrightarrow a\' : {A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} f\\;a \\twoheadrightarrow f\\;a\' : {B}} \\\\
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
      \\prftree\[r\]{{\\scriptsize\\textsf{let\$\_1\$}}}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\ensuremath{\\mathcal{R}}} a \\twoheadrightarrow a\' : {A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\ensuremath{\\mathcal{R}}} b \\twoheadrightarrow b\' : {B}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = a;\\;b} \\twoheadrightarrow\\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = a\';\\;b\'} : {B}} \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{unit}}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\mapsto \\cdot}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} () \\twoheadrightarrow() : {\\ensuremath{\\mathbf{1}}}} \\qquad
      \\prftree\[r\]{{\\scriptsize\\textsf{pair}}}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l} \\vdash\_{\\ensuremath{\\mathcal{R}}} a \\twoheadrightarrow a\' : {A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\ensuremath{\\mathcal{R}}} b \\twoheadrightarrow b\' : {B}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} (a, b) \\twoheadrightarrow(a\', b\') : {A \\otimes B}} \\\\
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
      \\prftree\[r\]{{\\scriptsize\\textsf{let\$\_2\$}}}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\ensuremath{\\mathcal{R}}} a \\twoheadrightarrow a\' : {A \\otimes B}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A, y : B \\vdash\_{\\ensuremath{\\mathcal{R}}} c \\twoheadrightarrow c\' : {C}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;(x, y) = a;\\;c} \\twoheadrightarrow\\ensuremath{\\ensuremath{\\mathsf{let}}\\;(x, y) = a\';\\;c\'} : {C}}
    
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
  \\end{gathered}\$\$ \$\$\\begin{gathered}
      \\prftree\[r\]{{\\scriptsize\\textsf{inl}}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} a \\twoheadrightarrow a\' : {A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\iota\_l\\;{a} \\twoheadrightarrow\\iota\_l\\;{a\'} : {A + B}} \\qquad
      \\prftree\[r\]{{\\scriptsize\\textsf{inr}}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} b \\twoheadrightarrow b\' : {B}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\iota\_r\\;{b} \\twoheadrightarrow\\iota\_r\\;{b\'} : {A + B}} \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{case}}}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\ensuremath{\\mathcal{R}}} e \\twoheadrightarrow e\' : {A + B}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\ensuremath{\\mathcal{R}}} a \\twoheadrightarrow a\' : {C}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, y : B \\vdash\_{\\ensuremath{\\mathcal{R}}} b \\twoheadrightarrow b\' : {C}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\mathsf{case}}\\;e\\;\\{\\iota\_l\\;{x} :a, \\iota\_r\\;{y} :b\\} \\twoheadrightarrow\\ensuremath{\\mathsf{case}}\\;e\'\\;\\{\\iota\_l\\;{x} :a\', \\iota\_r\\;{y} :b\'\\} : {C}} \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{abort}}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} a \\twoheadrightarrow a\' : {\\ensuremath{\\mathbf{0}}}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\mathsf{abort}}\\;{a} \\twoheadrightarrow\\ensuremath{\\mathsf{abort}}\\;{a\'} : {C}}
    
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
  \\end{gathered}\$\$ \$\$\\begin{gathered}
      \\prftree\[r\]{{\\scriptsize\\textsf{iter}}}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
        {\\ensuremath{\\mathsf{q}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}) = \\top}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\ensuremath{\\mathcal{R}}} a \\twoheadrightarrow a\' : {A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\ensuremath{\\mathcal{R}}} b \\twoheadrightarrow b\' : {B + A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\mathsf{iter}}\\;a\\;\\{ \\iota\_r\\;{x} :b \\} \\twoheadrightarrow\\ensuremath{\\mathsf{iter}}\\;a\'\\;\\{ \\iota\_r\\;{x} :b\' \\} : {B}}
    
  \\end{gathered}\$\$

  ]],
  caption: [
    $lambda_(sans(i t e r))$ congruence rules
  ]
)
<refall:fig:congruence-refinement>

#figure([#block[
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
  minipage=1.1,scale=0.9 \$\$\\begin{gathered}
      \\prftree\[r\]{{\\scriptsize\\textsf{op-bind}}}
        {f : A \\to B}
        {\\Gamma \\vdash\_{} a: {A}}
        {\\Gamma \\vdash\_{\\ensuremath{\\mathcal{R}}} f\\;a \\approx\\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = a;\\;f\\;x} : {B}} 
        \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{pair-bind}}}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l} \\vdash\_{} a: {A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{} b: {B}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} (a, b) \\approx\\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = a;\\;\\ensuremath{\\ensuremath{\\mathsf{let}}\\;y = b;\\;(x, y)}} : {A \\otimes B}} 
        \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{pair-left-bind}}}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l} \\vdash\_{} a: {A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{} b: {B}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} (a, b) \\approx\\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = a;\\;(x, b)} : {A \\otimes B}} 
        \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{pair-right-bind}}}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l} \\vdash\_{\\epsilon} a: {A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\eta} b: {B}}
        {\\epsilon \\rightleftharpoons\\eta}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} (a, b) \\approx\\ensuremath{\\ensuremath{\\mathsf{let}}\\;y = b;\\;(a, y)} : {A \\otimes B}} 
        \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{inl-bind}}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{} a: {A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\iota\_l\\;{a} \\approx\\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = a;\\;\\iota\_l\\;{x}} : {A + B}} \\qquad
      \\prftree\[r\]{{\\scriptsize\\textsf{inr-bind}}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{} b: {B}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\iota\_r\\;{b} \\approx\\ensuremath{\\ensuremath{\\mathsf{let}}\\;y = b;\\;\\iota\_r\\;{y}} : {A + B}} 
        \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{abort-bind}}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{} a: {\\ensuremath{\\mathbf{0}}}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\mathsf{abort}}\\;{a} \\approx\\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = a;\\;\\ensuremath{\\mathsf{abort}}\\;{x}} : {C}} 
        \\\\
    
  \\end{gathered}\$\$

  ]],
  caption: [
    Derivable binding rules for $lambda_(sans(i t e r))$
  ]
)
<refall:fig:derivable-binding>

= Completeness
<refall:apx:completeness>
In this section, we give the details of the proof of completeness of our
refinement calculus w.r.t. our denotational semantics.

== Syntactic Model
<refall:apx:syn-model>
We begin by defining the syntactic category $sans(T m) \( cal(R) \)$ of
$lambda_(sans(i t e r))$-models of a signature $cal(S)$ quotiented by a
set of primitive rewrites $cal(R)$ as follows:

- Objects types $A \, B \, C in sans(T y) \( cal(X) \)$

- Morphisms
  $sans(T m)_epsilon.alt \( A \, B \) := { \( x \, a \) divides x : A tack.r_epsilon.alt a : B } \/ approx$,
  with quotiented pairs written as $lambda$-expressions $lambda x . a$,
  where $\( lambda x . a \) approx \( lambda x . b \)$ if and only if
  $x : A tack.r_(cal(R)) a approx \[ x \/ y \] b : B$.

  Equivalently, morphisms in $sans(T m)_epsilon.alt \( A \, B \)$ may be
  viewed as #emph[functions] $f : sans(V a r) arrow.r sans(T e r m)$,
  with $\( x \, a \) \( y \) := \[ y \/ x \] a$, satisfying the property
  that, for all $x \, y in sans(V a r)$,
  $x : A tack.r_epsilon.alt f \( x \) : B$
  $f \( y \) = \[ y \/ x \] f \( x \)$, quotiented up to equivalence
  $f approx g arrow.l.r.double x : A tack.r_(cal(R)) f \( x \) approx g \( x \) : B$.
  The equivalence between these two representations is given by the
  $eta$-law $f approx lambda x . f \( x \)$.

- Refinement on morphisms $f arrow.r.twohead g$ if and only if
  $x : A tack.r_(cal(R)) f \( x \) arrow.r.twohead g \( x \) : B$ (this
  is well-defined since, by definition, we quotient precisely the
  equivalence clases of $arrow.r.twohead_(cal(R))$)

- Identity morphisms $sans(i d)_A := \( lambda x . x \)$

- Composition
  $\( lambda x . a \) ; \( lambda y . b \) := \( lambda x . sans(l e t) #h(0em) y = a ; #h(0em) b \)$.
  We note that, for $a$ #emph[pure], this reduces to the usual
  substitution-based definition
  $\( lambda x . a \) ; \( lambda y . b \) = \( lambda x . \[ a \/ y \] b \)$.

- Tensor products $A ⊗ B$ with monoidal unit
  $upright(bold(1))$, and tensor functors
  $ \( lambda x . a \) ⊗ A := \( lambda z . sans(l e t) #h(0em) \( x \, y \) = z ; #h(0em) \( a \, y \) \) #h(2em) A ⊗ \( z \, b \) := \( lambda x . sans(l e t) #h(0em) \( y \, z \) = x ; #h(0em) \( y \, b \) \) \) $
  In general, we extend pattern binding to $lambda$-expressions, writing
  (for $x in.not sans(f v) \( a \)$),
  $ \( lambda P . a \) := \( lambda x . sans(l e t) #h(0em) P = x ; #h(0em) a \) $
  in which case we may rewrite the above as
  $ \( lambda x . a \) ⊗ A := \( lambda \( x \, y \) . \( a \, y \) \) #h(2em) A ⊗ \( lambda z . b \) := \( lambda \( y \, z \) . \( y \, b \) \) \) $
  In partiuclar, we hence have that
  $ \( lambda x . a \) times.l \( lambda y . b \) = \( lambda \( x \, y \) . \( a \, b \) \) #h(2em) \( lambda x . a \) times.r \( lambda y . b \) = \( lambda \( x \, y \) . sans(l e t) #h(0em) y' = b ; #h(0em) sans(l e t) #h(0em) x' = a ; #h(0em) \( x' \, y' \) \) $

- Associators, unitors, and symmetries
  $ alpha := \( lambda \( \( x \, y \) \, z \) . \( x \, \( y \, z \) \) \) #h(2em) alpha^(- 1) := \( lambda \( x \, \( y \, z \) \) . \( \( x \, y \) \, z \) \) #h(2em) sigma := \( lambda \( x \, y \) . \( y \, x \) \)\
  lambda := \( lambda \( x \, y \) . x \) #h(2em) lambda^(- 1) := \( lambda x . \( x \, \( \) \) \) #h(2em) rho := \( lambda \( x \, y \) . y \) #h(2em) rho^(- 1) := \( lambda y . \( \( \) \, y \) \) $

- Coproducts $A + B$ with initial object $upright(bold(0))$, zero
  morphisms $0 := \( x \, sans(a b o r t) #h(0em) x \)$, and injections
  and distributors
  $ iota_l := \( lambda x . iota_l #h(0em) x \) #h(2em) iota_r := \( lambda x . iota_r #h(0em) x \) #h(2em) \[ \( lambda x . a \) \, \( lambda y . b \) \] := \( lambda z . sans(c a s e) #h(0em) z #h(0em) { iota_l #h(0em) x : a \, iota_r #h(0em) y : b } \)\
  delta := \[ - ⊗ iota_l \, - ⊗ iota_r \] = \( lambda x . sans(c a s e) #h(0em) x #h(0em) { iota_l #h(0em) \( y_l \, y_r \) : \( y_l \, iota_l #h(0em) y_r \) \, iota_r #h(0em) \( z_l \, z_r \) : \( z_l \, iota_r #h(0em) z_r \) } \)\
  delta^(- 1) := \( lambda \( x_l \, x_r \) . sans(c a s e) #h(0em) x_r #h(0em) { iota_l #h(0em) y : iota_l #h(0em) \( x_l \, y \) \, iota_r #h(0em) z : iota_r #h(0em) \( x_r \, z \) } \) $
  In particular, this means that we have
  $ \( lambda x . a \) ; \[ \( lambda y . b \) \, \( lambda z . c \) \] & = \( lambda x . sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) y : b \, iota_r #h(0em) z : c } \)\
  \( lambda x . a \) + \( lambda y . b \) & = \( lambda z . sans(c a s e) #h(0em) z #h(0em) { iota_l #h(0em) x : iota_l #h(0em) a \, iota_r #h(0em) y : iota_r #h(0em) b } \)\
  \( lambda x . a \) ; \( lambda y . b \) + \( lambda z . c \) & = \( lambda x . sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) y : iota_l #h(0em) b \, iota_r #h(0em) z : iota_r #h(0em) c } \) $

- Iteration operator
  $\( lambda x . a \)^dagger := \( lambda y . sans(i t e r) #h(0em) y #h(0em) { iota_r #h(0em) x : a } \)$

- Discard and diagonal morphisms $!_A := \( lambda x . \( \) \)$ and
  $Delta_A := \( lambda x . \( x \, x \) \)$

We aim to prove the following lemma:

#block[
$sans(T m) \( cal(R) \)$ is a $lambda_(sans(i t e r))$-model.

]
#block[
#emph[Proof.] We begin by noting that
$ \( lambda x . a \) ; \( lambda P . b \) = \( lambda x . sans(l e t) #h(0em) P = a ; #h(0em) b \) $
In particular, this allows us to deduce the following useful identities:
$ \( lambda x . a \) ; alpha = \( lambda x . sans(l e t) #h(0em) \( \( y \, z \) \, w \) = a ; #h(0em) \( y \, \( z \, w \) \) \)\
\( lambda x . a \) ; alpha^(- 1) = \( lambda x . sans(l e t) #h(0em) \( y \, \( z \, w \) \) = a ; #h(0em) \( \( y \, z \) \, w \) \)\
\( lambda x . a \) ; sigma = \( lambda x . sans(l e t) #h(0em) \( y \, z \) = a ; #h(0em) \( z \, y \) \)\
\( lambda x . a \) ; lambda = \( lambda x . sans(l e t) #h(0em) \( y \, z \) = a ; #h(0em) y \) #h(2em) \( lambda x . a \) ; lambda^(- 1) = \( lambda x . \( a \, \( \) \) \)\
\( lambda x . a \) ; rho = \( lambda x . sans(l e t) #h(0em) \( y \, z \) = a ; #h(0em) z \) #h(2em) \( lambda x . a \) ; rho^(- 1) = \( lambda x . \( \( \) \, a \) \) $
We also note that
$ \( lambda P . a \) ⊗ A & = \( lambda \( x \, y \) . \( sans(l e t) #h(0em) P = x ; #h(0em) a \, y \) \) = \( lambda \( x \, y \) . sans(l e t) #h(0em) P = x ; #h(0em) \( a \, y \) \) = \( lambda \( P \, y \) . \( a \, y \) \)\
A ⊗ \( lambda P . b \) & = \( lambda \( x \, y \) . \( x \, sans(l e t) #h(0em) P = y ; #h(0em) b \) \) = \( lambda \( x \, y \) . sans(l e t) #h(0em) P = y ; #h(0em) \( x \, b \) \) = \( lambda \( x \, P \) . \( x \, b \) \) $
We now verify that:

- $sans(T m)_epsilon.alt \( cal(R) \)$ is a category: we have that
  $ \( lambda x . x \) ; \( lambda y . a \) & = \( lambda x . sans(l e t) #h(0em) y = x ; #h(0em) a \) = \( lambda x . \[ x \/ y \] a \) = \( lambda y . a \)\
  \( lambda x . a \) ; \( lambda y . y \) & = \( lambda x . sans(l e t) #h(0em) y = a ; #h(0em) y \) = \( lambda x . a \)\
  \( \( lambda x . a \) ; \( lambda y . b \) \) ; \( lambda z . c \) & = \( lambda x . sans(l e t) #h(0em) z = \( sans(l e t) #h(0em) y = a ; #h(0em) b \) ; #h(0em) c \) = \( lambda x . sans(l e t) #h(0em) y = a ; #h(0em) sans(l e t) #h(0em) z = b ; #h(0em) c \)\
   & = \( lambda x . a \) ; \( lambda y . sans(l e t) #h(0em) z = b ; #h(0em) c \) = \( lambda x . a \) ; \( \( lambda y . b \) ; \( lambda z . c \) \) $

- $sans(T m)_epsilon.alt \( cal(R) \)$ is binoidal: we have that
  $ \( lambda x . x \) ⊗ A & = \( lambda z . sans(l e t) #h(0em) \( x \, y \) = z ; #h(0em) \( x \, y \) \) = \( lambda z . z \) med\
  \( \( lambda x . a \) ; \( lambda y . b \) \) ⊗ A & = \( lambda \( x \, z \) . \( sans(l e t) #h(0em) y = a ; #h(0em) b \, z \) \) = \( lambda \( x \, z \) . sans(l e t) #h(0em) y = a ; #h(0em) \( b \, z \) \)\
   & = \( lambda \( x \, z \) . sans(l e t) #h(0em) \( y \, z' \) = \( a \, z \) ; #h(0em) \( b \, z' \) \)\
   & = \( lambda \( x \, z \) . \( a \, z \) \) ; \( lambda \( y \, z' \) . \( b \, z' \) \)\
   & = \( \( lambda x . a \) ⊗ A \) ; \( \( lambda y . b \) ⊗ A \)\
  A ⊗ \( lambda y . y \) & = \( lambda z . sans(l e t) #h(0em) \( x \, y \) = z ; #h(0em) \( x \, y \) \) = \( lambda z . z \)\
  A ⊗ \( \( lambda y . a \) ; \( lambda z . b \) \) & = \( lambda \( x \, y \) . \( x \, sans(l e t) #h(0em) z = a ; #h(0em) b \) \) = \( lambda \( x \, y \) . sans(l e t) #h(0em) z = a ; #h(0em) \( x \, b \) \)\
   & = \( lambda \( x \, y \) . sans(l e t) #h(0em) \( x' \, z \) = \( x \, a \) ; #h(0em) \( x' \, b \) \)\
   & = \( lambda \( x \, y \) . \( x \, a \) \) ; \( lambda \( x' \, z \) . \( x' \, b \) \)\
   & = \( A ⊗ \( lambda y . a \) \) ; \( A ⊗ \( lambda z . b \) \) $

- $sans(T m)_epsilon.alt \( cal(R) \)$ is symmetric premonoidal:

  - Pentagon equation: we have that
    $  & alpha_(\( A ⊗ B \) \, C \, D) ; alpha_(A \, B \, \( C ⊗ D \))\
     & = \( lambda \( \( x_12 \, x_3 \) \, x_4 \) . \( x_12 \, \( x_3 \, x_4 \) \) \) ; \( lambda \( \( x_1 \, x_2 \) \, x_34 \) . \( x_1 \, \( x_2 \, x_34 \) \) \)\
     & = \( lambda \( \( x_12 \, x_3 \) \, x_4 \) . sans(l e t) #h(0em) \( \( x_1 \, x_2 \) \, x_34 \) = \( x_12 \, \( x_3 \, x_4 \) \) ; #h(0em) \( x_1 \, \( x_2 \, x_34 \) \) \)\
     & = \( lambda \( \( x_12 \, x_3 \) \, x_4 \) . sans(l e t) #h(0em) \( x_1 \, x_2 \) = x_12 ; #h(0em) \( x_1 \, \( x_2 \, \( x_3 \, x_4 \) \) \) \)\
     & = \( lambda \( \( \( x_1 \, x_2 \) \, x_3 \) \, x_4 \) . \( x_1 \, \( x_2 \, \( x_3 \, x_4 \) \) \) \)\
     & = \( lambda \( \( \( x_1 \, x_2 \) \, x_3 \) \, x_4 \) . sans(l e t) #h(0em) \( z_1 \, \( \( z_2 \, z_3 \) \, z_4 \) \) = \( x_1 \, \( \( x_2 \, x_3 \) \, x_4 \) \) ; #h(0em) \( z_1 \, \( z_2 \, \( z_3 \, z_4 \) \) \) \)\
     & = \( lambda \( \( \( x_1 \, x_2 \) \, x_3 \) \, x_4 \) . \( x_1 \, \( \( x_2 \, x_3 \) \, x_4 \) \) \) ; \( lambda \( z_1 \, \( \( z_2 \, z_3 \) \, z_4 \) \) . \( z_1 \, \( z_2 \, \( z_3 \, z_4 \) \) \) \)\
     & = \( lambda \( \( \( x_1 \, x_2 \) \, x_3 \) \, x_4 \) . sans(l e t) #h(0em) \( \( y_1 \, y_23 \) \, y_4 \) = \( \( x_1 \, \( x_2 \, x_3 \) \) \, x_4 \) ; #h(0em) \( y_1 \, \( y_23 \, y_4 \) \) \) ;\
     & #h(2em) \( lambda \( z_1 \, \( \( z_2 \, z_3 \) \, z_4 \) \) . \( z_1 \, \( z_2 \, \( z_3 \, z_4 \) \) \) \)\
     & = \( lambda \( \( \( x_1 \, x_2 \) \, x_3 \) \, x_4 \) . \( \( x_1 \, \( x_2 \, x_3 \) \) \, x_4 \) \) ; \( lambda \( \( y_1 \, y_23 \) \, y_4 \) . \( y_1 \, \( y_23 \, y_4 \) \) \) ;\
     & #h(2em) \( lambda \( z_1 \, \( \( z_2 \, z_3 \) \, z_4 \) \) . \( z_1 \, \( z_2 \, \( z_3 \, z_4 \) \) \) \)\
     & = alpha_(A \, B \, C) ⊗ D ; alpha_(A \, B ⊗ C \, D) ; A ⊗ alpha_(B \, C \, D) $

  - Triangle equation: we have that
    $ alpha_(A \, upright(bold(1)) \, B) ; X ⊗ lambda_B & = \( lambda \( \( x \, y \) \, z \) . \( x \, \( y \, z \) \) \) ; \( lambda \( x' \, y' \) . y' \)\
     & = \( lambda \( \( x \, y \) \, z \) . sans(l e t) #h(0em) \( x' \, y' \) = \( x \, \( y \, z \) \) ; #h(0em) y' \)\
     & = \( lambda \( \( x \, y \) \, z \) . \( y \, z \) \) = \( lambda \( x \, y \) . y \) ⊗ B\
     & = rho_A ⊗ B $

  - Hexagon equation: we have that
    $  & alpha_(A \, B \, C) ; sigma_(A \, B ⊗ C) ; alpha_(B \, C \, A)\
     & = \( lambda \( \( x_1 \, x_2 \) \, x_3 \) . \( x_1 \, \( x_2 \, x_3 \) \) \) ; \( lambda \( y_1 \, y_23 \) . \( y_23 \, y_1 \) \) ; \( lambda \( \( z_2 \, z_3 \) \, z_1 \) . \( z_2 \, \( z_3 \, z_1 \) \) \)\
     & = \( lambda \( \( x_1 \, x_2 \) \, x_3 \) . \( \( x_2 \, x_3 \) \, x_1 \) \) ; \( lambda \( \( z_2 \, z_3 \) \, z_1 \) . \( z_2 \, \( z_3 \, z_1 \) \) \)\
     & = \( lambda \( \( x_1 \, x_2 \) \, x_3 \) . \( x_2 \, \( x_3 \, x_1 \) \) \)\
     & = \( lambda \( \( x_1 \, x_2 \) \, x_3 \) . \( x_2 \, \( x_1 \, x_3 \) \) \) ; \( lambda \( z_2 \, \( z_1 \, z_3 \) \) . \( z_2 \, \( z_3 \, z_1 \) \) \)\
     & = \( lambda \( \( x_1 \, x_2 \) \, x_3 \) . \( \( x_2 \, x_1 \) \, x_3 \) \) ; \( lambda \( \( y_2 \, y_1 \) \, y_3 \) . \( y_2 \, \( y_1 \, y_3 \) \) \) ; \( lambda \( z_2 \, \( z_1 \, z_3 \) \) . \( z_2 \, \( z_3 \, z_1 \) \) \)\
     & = sigma_(A \, B) ⊗ C ; alpha_(B \, A \, C) ; B ⊗ sigma_(A \, C) $

- $sans(T m)_epsilon.alt \( cal(R) \)$ has chosen coproducts and an
  initial object: see formalization.

- $sans(T m)_epsilon.alt \( cal(R) \)$ is distributive: we have that
  $ delta_(X \, Y \, Z) ; delta_(X \, Y \, Z)^(- 1) & = \[ X ⊗ iota_l \, X ⊗ iota_r \] ; \( lambda \( x \, w \) . sans(c a s e) #h(0em) w #h(0em) { iota_l #h(0em) y : iota_l #h(0em) \( x \, y \) \, iota_r #h(0em) z : iota_r #h(0em) \( x \, z \) } \)\
   & = \[ \( lambda \( x \, y \) . \( x \, iota_l #h(0em) y \) \) ; \( lambda \( x \, w \) . sans(c a s e) #h(0em) w #h(0em) { iota_l #h(0em) y : iota_l #h(0em) \( x \, y \) \, iota_r #h(0em) z : iota_r #h(0em) \( x \, z \) } \) \,\
   & quad #h(0em) #h(0em) \( lambda \( x \, z \) . \( x \, iota_r #h(0em) z \) \) ; \( lambda \( x \, w \) . sans(c a s e) #h(0em) w #h(0em) { iota_l #h(0em) y : iota_l #h(0em) \( x \, y \) \, iota_r #h(0em) z : iota_r #h(0em) \( x \, z \) } \) \]\
   & = \[ \( lambda \( x \, y \) . sans(c a s e) #h(0em) iota_l #h(0em) y #h(0em) { iota_l #h(0em) y : iota_l #h(0em) \( x \, y \) \, iota_r #h(0em) z : iota_r #h(0em) \( x \, z \) } \) \,\
   & quad #h(0em) #h(0em) \( lambda \( x \, z \) . sans(c a s e) #h(0em) iota_r #h(0em) z #h(0em) { iota_l #h(0em) y : iota_l #h(0em) \( x \, y \) \, iota_r #h(0em) z : iota_r #h(0em) \( x \, z \) } \) \]\
   & = \[ \( lambda \( x \, y \) . iota_l #h(0em) \( x \, y \) \) \, \( lambda \( x \, z \) . iota_r #h(0em) \( x \, z \) \) \] = \[ iota_l \, iota_r \] = sans(i d)_(\( X ⊗ Y \) + \( X ⊗ Z \)) $
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
  and \$\$\\begin{aligned}
      \\delta^{-1}\_{X, Y, Z} ; \\delta\_{X, Y, Z}
      &= (\\lambda (x, w) .  \\ensuremath{\\mathsf{case}}\\;w\\;\\{\\iota\_l\\;{y} :\\iota\_l\\;{(x, y)}, \\iota\_r\\;{z} :\\iota\_r\\;{(x, z)}\\})
        ; \[X \\otimes \\iota\_l, X \\otimes \\iota\_r\] \\\\
      &= (\\lambda (x, w) . \\ensuremath{\\ensuremath{\\mathsf{let}}\\;w\' = \\ensuremath{\\mathsf{case}}\\;w\\;\\{\\iota\_l\\;{y} :\\iota\_l\\;{(x, y)}, \\iota\_r\\;{z} :\\iota\_r\\;{(x, z)}\\};\\; 
        \\\\ & \\quad\\;\\;
        \\ensuremath{\\mathsf{case}}\\;w\'\\;\\{\\iota\_l\\;{(x, y)} :(x, \\iota\_l\\;{y}), \\iota\_r\\;{(x, z)} :(x, \\iota\_r\\;{z})\\}}) \\\\
      &= (\\lambda (x, w) . \\ensuremath{\\mathsf{case}}\\;w\\;\\{\\iota\_l\\;{y} :\\ensuremath{\\mathsf{case}}\\;\\iota\_l\\;{(x, y)}\\;\\{\\iota\_l\\;{(x, y)} :(x, \\iota\_l\\;{y}), \\iota\_r\\;{(x, z)} :(x, \\iota\_r\\;{z})\\} \\\\ & \\quad\\;\\;, \\iota\_r\\;{z} :\\ensuremath{\\mathsf{case}}\\;\\iota\_r\\;{(x, z)}\\;\\{\\iota\_l\\;{(x, y)} :(x, \\iota\_l\\;{y}), \\iota\_r\\;{(x, z)} :(x, \\iota\_r\\;{z})\\}\\}
      ) \\\\
      &= (\\lambda (x, w) . \\ensuremath{\\mathsf{case}}\\;w\\;\\{\\iota\_l\\;{y} :(x, \\iota\_l\\;{y}), \\iota\_r\\;{z} :(x, \\iota\_r\\;{z})\\}) \\\\
      &= (\\lambda (x, w) . (x, \\ensuremath{\\mathsf{case}}\\;w\\;\\{\\iota\_l\\;{y} :\\iota\_l\\;{y}, \\iota\_r\\;{z} :\\iota\_r\\;{z}\\}))
      = (\\lambda (x, w) . (x, w)) = \\ensuremath{\\mathsf{id}}\_{X \\otimes (Y + Z)}
    
  \\end{aligned}\$\$

- $sans(T m)_epsilon.alt \( cal(R) \)$ has an iteration operator: we
  have that
  $ \( lambda x . a \)^dagger & = \( lambda y . sans(i t e r) #h(0em) y #h(0em) { iota_r #h(0em) x : a } \)\
   & = \( lambda y . sans(l e t) #h(0em) x = y ; #h(0em) sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) z : z \, iota_r #h(0em) y : sans(i t e r) #h(0em) y #h(0em) { iota_r #h(0em) x : a } } \)\
   & = \( lambda x . sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) z : z \, iota_r #h(0em) y : sans(i t e r) #h(0em) y #h(0em) { iota_r #h(0em) x : a } } \)\
   & = \( lambda x . sans(l e t) #h(0em) w = a ; #h(0em) sans(c a s e) #h(0em) w #h(0em) { iota_l #h(0em) z : z \, iota_r #h(0em) y : sans(i t e r) #h(0em) y #h(0em) { iota_r #h(0em) x : a } } \)\
   & = \( lambda x . a \) ; \( lambda w . sans(c a s e) #h(0em) w #h(0em) { iota_l #h(0em) z : z \, iota_r #h(0em) y : sans(i t e r) #h(0em) y #h(0em) { iota_r #h(0em) x : a } } \)\
   & = \( lambda x . a \) ; \[ \( lambda z . z \) \, \( lambda x . a \)^dagger \] = \( lambda x . a \) ; \[ sans(i d) \, \( lambda x . a \)^dagger \]\
   $

- $sans(T m)_epsilon.alt \( cal(R) \)$ is an Elgot category: it suffices
  to show that our iteration operator satisfies:

  - Naturality: we have that
    $ \( \( lambda x . a \) ; \( lambda y . b \) + \( lambda z . z \) \)^dagger & = \( lambda x . sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) y : iota_l #h(0em) b \, iota_r #h(0em) z : iota_r #h(0em) z } \)^dagger\
     & = \( lambda w . sans(i t e r) #h(0em) w #h(0em) { iota_r #h(0em) x : sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) y : iota_l #h(0em) b \, iota_r #h(0em) z : iota_r #h(0em) z } } \)\
     & = \( lambda w . sans(i t e r) #h(0em) w #h(0em) { iota_r #h(0em) x : sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) y : iota_l #h(0em) b \, iota_r #h(0em) z : iota_r #h(0em) z } } \)\
     & = \( lambda w . sans(l e t) #h(0em) y = sans(i t e r) #h(0em) w #h(0em) { iota_r #h(0em) x : a } ; #h(0em) b \)\
     & = \( lambda x . a \)^dagger ; \( lambda y . b \) $

  - Codiagonal: we have that
    $ \( \( lambda x . a \)^dagger \)^dagger & = \( lambda z . sans(i t e r) #h(0em) z #h(0em) { iota_r #h(0em) y : sans(i t e r) #h(0em) y #h(0em) { iota_r #h(0em) x : a } } \)\
     & = \( lambda z . sans(i t e r) #h(0em) z #h(0em) { iota_r #h(0em) x : sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) y : y \, iota_r #h(0em) w : iota_r #h(0em) w } } \)\
     & = \( lambda x . sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) y : y \, iota_r #h(0em) w : iota_r #h(0em) w } \)^dagger\
     & = \( \( lambda x . a \) ; \[ \( lambda y . y \) \, \( lambda w . iota_r #h(0em) w \) \] \)^dagger = \( \( lambda x . a \) ; \[ sans(i d) \, iota_r \] \)^dagger $

  - Directed Uniformity: assume that
    $ \( lambda x . a \) ; \( lambda y . b \) arrow.r.twohead^p \( lambda y . b' \) ; sans(i d) + \( lambda x . a \) $
    Unfolding both sides of this refinement, we hence have that
    $ \( lambda x . sans(l e t) #h(0em) y = a ; #h(0em) b \) arrow.r.twohead^p \( lambda y . sans(c a s e) #h(0em) b' #h(0em) { iota_l #h(0em) z : iota_l #h(0em) z \, iota_r #h(0em) x : iota_r #h(0em) a } \) $
    We therefore, by unif$""^p$, have that
    $ \( lambda x . a \) ; \( lambda y . b \)^dagger & = \( lambda x . sans(i t e r) #h(0em) a #h(0em) { iota_r #h(0em) y : b } \) = \( lambda z . sans(l e t) #h(0em) x = z ; #h(0em) sans(i t e r) #h(0em) a #h(0em) { iota_r #h(0em) y : b } \)\
     & arrow.r.twohead^p \( lambda z . sans(i t e r) #h(0em) z #h(0em) { iota_r #h(0em) y : b' } \) = \( lambda y . b' \)^dagger $
    as desired.

  - Dinaturality: we have that

    #block[
    If $\( - \)^dagger$ is an iteration operator which satisfies
    naturality and codiagonal and is $cal(K)$-uniform for $cal(K)$
    cocartesian, then it also satisfies dinaturality.

    ]
    #block[
    #emph[Proof.] See Lemma 31 of
    #cite(<goncharov-18-guarded-traced>, form: "prose")~◻

    ]
    Since all $sans(T m)_epsilon.alt \( cal(R) \)$ for
    $epsilon.alt in cal(E)^oo$ are
    $sans(T m)_tack.t \( cal(R) \)$-uniform, and
    $sans(T m)_tack.t \( cal(R) \)$ is cocartesian,
    $sans(T m)_epsilon.alt \( cal(R) \)$ must in fact satisfy
    dinaturality as desired.

- Strength: fix $z : A tack.r_() a : B + A$. We have that
  $ x : C \, y : A & tack.r_(cal(R)) sans(l e t) #h(0em) \( x \, z \) = \( x \, y \) ; #h(0em) sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) w_l : iota_l #h(0em) \( x \, w_l \) \, iota_r #h(0em) w_r : iota_r #h(0em) \( x \, w_r \) }\
   & approx sans(c a s e) #h(0em) \( sans(l e t) #h(0em) z = y ; #h(0em) a \) #h(0em) { iota_l #h(0em) w_l : iota_l #h(0em) \( x \, w_l \) \, iota_r #h(0em) w_r : iota_r #h(0em) \( x \, w_r \) }\
   & approx sans(c a s e) #h(0em) \( sans(l e t) #h(0em) z = y ; #h(0em) a \) #h(0em) { iota_l #h(0em) w_l : iota_l #h(0em) \( x \, w_l \) \, iota_r #h(0em) y : iota_r #h(0em) \( x \, y \) } $
  Hence, by uniformity, as $\( v_l \, v_(r') \)$ is pure, we have
  $  & \( C ⊗ \( lambda z . a \) ; delta^(- 1) \)^dagger\
   & = \( lambda \( x \, z \) . sans(l e t) #h(0em) \( x' \, w \) = \( x \, a \) ; #h(0em) sans(c a s e) #h(0em) w #h(0em) { iota_l #h(0em) w_l : iota_l #h(0em) \( x' \, w_l \) \, iota_r #h(0em) w_r : iota_r #h(0em) \( x' \, w_r \) } \)^dagger\
   & = \( lambda \( x \, z \) . sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) w_l : iota_l #h(0em) \( x \, w_l \) \, iota_r #h(0em) w_r : iota_r #h(0em) \( x \, w_r \) } \)^dagger\
   & = \( lambda v . sans(i t e r) #h(0em) v #h(0em) { iota_r #h(0em) \( x \, z \) : sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) w_l : iota_l #h(0em) \( x \, w_l \) \, iota_r #h(0em) w_r : iota_r #h(0em) \( x \, w_r \) } } \)\
   & = \( lambda \( x \, y \) . sans(l e t) #h(0em) y = y ; #h(0em) sans(i t e r) #h(0em) \( x \, y \) #h(0em) { iota_r #h(0em) \( x \, z \) : sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) w_l : iota_l #h(0em) \( x \, w_l \) \, iota_r #h(0em) w_r : iota_r #h(0em) \( x \, w_r \) } } \)\
   & = \( lambda \( x \, y \) . sans(l e t) #h(0em) w = sans(i t e r) #h(0em) y #h(0em) { iota_r #h(0em) y : sans(l e t) #h(0em) z = y ; #h(0em) a } ; #h(0em) \( x \, w \) \)\
   & = \( lambda \( x \, y \) . sans(l e t) #h(0em) w = sans(i t e r) #h(0em) y #h(0em) { iota_r #h(0em) z : a } ; #h(0em) \( x \, w \) \)\
   & = \( lambda \( x \, y \) . \( x \, sans(i t e r) #h(0em) y #h(0em) { iota_r #h(0em) z : a } \) \)\
   & = C ⊗ \( lambda z . a \)^dagger $

Hence, to show that we have a valid $lambda_(sans(i t e r))$-model, it
suffices to prove that, given
$\( lambda x . a \) : sans(T m)_epsilon.alt \( cal(R) \) \( A \, B \)$

- If $A$ is relevant,
  $ Delta_A ; Delta_A ⊗ A ; alpha & = \( lambda x . \( x \, x \) \) ; \( lambda \( y \, z \) . \( \( y \, y \) \, z \) ; \( lambda \( \( w_1 \, w_2 \) \, w_3 \) . \( w_1 \, \( w_2 \, w_3 \) \) \)\
   & = \( lambda x . \( \( x \, x \) \, x \) \) ; \( lambda \( \( w_1 \, w_2 \) \, w_3 \) . \( w_1 \, \( w_2 \, w_3 \) \) \)\
   & = \( lambda x . \( x \, \( x \, x \) \) \) = \( lambda x . \( x \, x \) \) ; \( lambda \( y \, z \) . \( y \, \( z \, z \) \) \)\
   & = Delta_A ; A ⊗ Delta_A $ and
  $ Delta_A ; sigma_(A \, A) & = \( lambda x . \( x \, x \) \) ; \( lambda \( y \, z \) . \( z \, y \) \)\
   & = \( lambda x . sans(l e t) #h(0em) \( y \, z \) = \( x \, x \) ; #h(0em) \( z \, y \) \) = \( lambda x . \( x \, x \) \) = Delta_A $
  as desired

- If $0 lt.eq sans(q)^p \( epsilon.alt \)$ and $A \, B$ affine, by
  let$""_1$-$beta^p$,
  $ \( lambda x . a \) ; !_B & = \( lambda x . sans(l e t) #h(0em) y = a ; #h(0em) \( \) \) arrow.r.twohead^p \( lambda x . \( \) \) = !_A $

- If $0 lt.eq sans(q)^p \( epsilon.alt \)$ and $A$ relevant, $B$ affine,
  by elim$""^p$,
  $ Delta_A ; \( f ; !_B \) ⊗ A & = \( lambda x . sans(l e t) #h(0em) \( y \, z \) = \( x \, x \) ; #h(0em) \( sans(l e t) #h(0em) w = f \( y \) ; #h(0em) \( \) \, z \) \)\
   & = \( lambda x . \( f \( x \) ; \( \) \, x \) \) = \( lambda x . sans(l e t) #h(0em) y = \( f \( x \) ; \( \) \) ; #h(0em) \( \( \) \, x \) \)\
   & arrow.r.twohead^p \( lambda x . sans(l e t) #h(0em) y = \( \) ; #h(0em) \( \( \) \, x \) \) = \( lambda x . \( \( \) \, x \) \) = rho^(- 1) $

- If $omega^(+) lt.eq sans(q)^p \( epsilon.alt \)$ and $A \, B$
  relevant, by let$""_1$-$beta^p$,
  $ \( lambda x . a \) ; Delta_B & = \( lambda x . a \) ; \( lambda y . \( y \, y \) \) = \( lambda x . sans(l e t) #h(0em) y = a ; #h(0em) \( y \, y \) \) = \( lambda x . \( a \, a \) \)\
   & = \( lambda x . \( sans(l e t) #h(0em) y = x ; #h(0em) \[ y \/ x \] a \, sans(l e t) #h(0em) z = x ; #h(0em) \[ z \/ x \] a \) \)\
   & = \( lambda x . sans(l e t) #h(0em) y = x ; #h(0em) sans(l e t) #h(0em) z = x ; #h(0em) \( \[ y \/ x \] a \, \[ z \/ x \] a \) \)\
   & = \( lambda x . sans(l e t) #h(0em) \( y \, z \) = \( x \, x \) ; #h(0em) \( \[ y \/ x \] a \, \[ z \/ x \] a \) \)\
   & = \( lambda x . \( x \, x \) \) ; \( lambda \( y \, z \) . \( \[ y \/ x \] a \, \[ z \/ x \] a \) \) = Delta_A ; \( lambda x . a \) times.l \( lambda x . a \) $

~◻

]
== Packing and Unpacking
<refall:apx:packing>
Given an annotated context $Gamma^(upright(bold(q)))$, we can
recursively define the #emph[packing]
$Gamma^(upright(bold(q))) tack.r_tack.t sans(p a c k) \( Gamma^(upright(bold(q))) \) : \[ Gamma^(upright(bold(q))) \]$
of its variables in the obvious manner; namely
$ sans(p a c k) \( dot.op \) := \( \) #h(2em) sans(p a c k) \( Gamma^(upright(bold(q))) \, x : A^q \) = \( sans(p a c k) \( Gamma^(upright(bold(q))) \) \, x^q \) #h(2em) x^q := cases(delim: "{", x & upright("if ") q eq.not 0, \( \) & upright("otherwise")) $
We can similarly #emph[unpack] a context's effective type
$a : \[ sans(Gamma)^(upright(bold(q))) \]$, which we write
$sans(l e t) #h(0em) Gamma = a ; #h(0em) b$, inductively in the obvious
manner:
$ \( sans(l e t) #h(0em) dot.op = a ; #h(0em) b \) := \( a ; b \) #h(2em) \( sans(l e t) #h(0em) Gamma \, x : A = a ; #h(0em) b \) := \( sans(l e t) #h(0em) \( g \, x \) = a ; #h(0em) sans(l e t) #h(0em) Gamma = g ; #h(0em) b \) $
We can show this satisfies the following typing rule by induction on
$Delta^(upright(bold(q))')$.
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
\$\$\\prftree\[r\]{{\\scriptsize\\textsf{unpack}}}
    {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l} \\vdash\_{\\epsilon} a: {\[\\Delta^{\\ensuremath{\\mathbf{q}}\'}\]}}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r}, \\Delta^{\\ensuremath{\\mathbf{q}}\'} \\vdash\_{\\epsilon} b: {B}}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;\\Gamma = a;\\;b}: {B}}\$\$
In particular, we proceed as follows:

- Given $a : \[ dot.op \]$, this follows directly from the derived rule
  seq.

- Given $a : \[ Delta^(upright(bold(q))') \, x : A^q \]$, we have that
  $Gamma^(upright(bold(q))_r) \, x : A^q \, Delta^(upright(bold(q))') tack.r_epsilon.alt b : B$.
  Hence,

  - If $q eq.not 0$, then $\[ A^q \] = A$, so by weakening
    $Gamma^(upright(bold(q))) \, x : A tack.r_epsilon.alt sans(l e t) #h(0em) Gamma = a' ; #h(0em) b : B$
    and therefore
    $Gamma^(upright(bold(q))) \, g : \[ Delta^(upright(bold(q))') \]^0 \, x : \[ A^q \] tack.r_epsilon.alt sans(l e t) #h(0em) Gamma = a' ; #h(0em) b : B$

  - If $q = 0$, then $x$ cannot be used in $b$, so
    $Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(l e t) #h(0em) Gamma = a' ; #h(0em) b : B$,
    and hence, as $\[ A^0 \] = upright(bold(1))$ has unrestricted
    linearity,
    $Gamma^(upright(bold(q))) \, g : \[ Delta^(upright(bold(q))') \]^0 \, x : \[ A^q \] tack.r_epsilon.alt sans(l e t) #h(0em) Gamma = a' ; #h(0em) b : B$
    by weakening.

  By induction, we may hence derive
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
  \$\$\\prftree\[r\]{{\\scriptsize\\textsf{unpack}}}
      {\\Gamma^0, g: \[\\Delta^{\\ensuremath{\\mathbf{q}}\'}\], x : \[A^q\]^0 \\vdash\_{\\epsilon} g: {\[\\Delta^{\\ensuremath{\\mathbf{q}}\'}\]}}
      {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, g: \[\\Delta^{\\ensuremath{\\mathbf{q}}\'}\]^0, x : \[A^q\], \\Delta^{\\ensuremath{\\mathbf{q}}\'} \\vdash\_{\\epsilon} b: {B}}
      {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, g: \[\\Delta^{\\ensuremath{\\mathbf{q}}\'}\], x : \[A^q\] \\vdash\_{\\epsilon} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;\\Gamma = g;\\;b}: {B}}\$\$
  Therefore, since
  $\[ Delta^(upright(bold(q))') \, x : A^q \] = \[ Delta^(upright(bold(q))') \] ⊗ \[ A^q \]$,
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
  we may derive \$\$\\prftree\[r\]{{\\scriptsize\\textsf{let\$\_2\$}}}
      {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} a: {\[\\Delta^{\\ensuremath{\\mathbf{q}}\'}, x : A^q\]}}
      {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, g: \[\\Delta^{\\ensuremath{\\mathbf{q}}\'}\], x : \[A^q\] \\vdash\_{\\epsilon} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;\\Gamma = g;\\;b}: {B}}
      {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;(g, x) = a;\\;\\ensuremath{\\ensuremath{\\mathsf{let}}\\;\\Gamma = g;\\;b}}: {B}}\$\$
  as desired.

We prove that packing and unpacking are mutually inverse up to $approx$
by induction:

#block[
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
The following rules are derivable: \$\$\\begin{gathered}
  \\prftree\[r\]{{\\scriptsize\\textsf{unpack-pack}}}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}}, \\Delta^{\\ensuremath{\\mathbf{q}}\'} \\vdash\_{\\epsilon} a: {A}}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}}, \\Delta^{\\ensuremath{\\mathbf{q}}\'} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;\\Delta = \\ensuremath{\\mathsf{pack}}(\\Delta^{\\ensuremath{\\mathbf{q}}\'});\\;a} \\approx a : {A}}
    \\\\
  \\prftree\[r\]{{\\scriptsize\\textsf{pack-unpack}}}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} b: {\[\\Delta^{\\ensuremath{\\mathbf{q}}\'}\]}}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;\\Delta = b;\\;\\ensuremath{\\mathsf{pack}}(\\Delta^{\\ensuremath{\\mathbf{q}}\'})} \\approx b : {\[\\Delta^{\\ensuremath{\\mathbf{q}}\'}\]}}
  
\\end{gathered}\$\$

]
#block[
#emph[Proof.] We proceed by $Delta^(upright(bold(q))')$

- $\( dot.op \)$: the results follow by elim and term, respectively.

- $\( Gamma^(upright(bold(q))) \, x : B^q \)$: we have by induction that

  - We have
    $ Gamma^(upright(bold(q))) \, Delta^(upright(bold(q))') \, x : B^q & tack.r_(cal(R)) sans(l e t) #h(0em) Delta^(upright(bold(q))') \, x : B^q = sans(p a c k) \( \( Delta^(upright(bold(q))') \, x : B^q \) ; #h(0em) a\
     & approx sans(l e t) #h(0em) \( g \, y \) = \( sans(p a c k) \( Delta^(upright(bold(q))') \) \, x^q \) ; #h(0em) \[ y \/ x \] a\
     & approx sans(l e t) #h(0em) g = sans(p a c k) \( Delta^(upright(bold(q))') \) ; #h(0em) sans(l e t) #h(0em) y = x^q ; #h(0em) \[ y \/ x \] a\
     & approx sans(l e t) #h(0em) y = x^q ; #h(0em) \[ y \/ x \] a approx a : A $
    since if $q eq.not 0$,
    $sans(l e t) #h(0em) y = x^q ; #h(0em) \[ y \/ x \] a approx sans(l e t) #h(0em) y = x ; #h(0em) \[ y \/ x \] a approx a$,
    whereas if $q = 0$ $x in.not sans(f v) \( a \)$ so
    $sans(l e t) #h(0em) y = x^q ; #h(0em) \[ y \/ x \] a approx sans(l e t) #h(0em) y = x ; #h(0em) a approx a$.

  - We have
    $ Gamma^(upright(bold(q))) & tack.r_(cal(R)) sans(l e t) #h(0em) Delta^(upright(bold(q))') \, x : A^q = b ; #h(0em) sans(p a c k) \( Delta^(upright(bold(q))') \, x : B^q \)\
     & approx sans(l e t) #h(0em) \( g \, x \) = b ; #h(0em) sans(l e t) #h(0em) Delta^(upright(bold(q))') = g ; #h(0em) \( sans(p a c k) \( Delta^(upright(bold(q))') \) \, x^q \)\
     & approx sans(l e t) #h(0em) \( g \, x \) = b ; #h(0em) sans(l e t) #h(0em) w = \( sans(l e t) #h(0em) Delta^(upright(bold(q))') = g ; #h(0em) sans(p a c k) \( Delta^(upright(bold(q))') \) \) ; #h(0em) \( w \, x^q \)\
     & approx sans(l e t) #h(0em) \( g \, x \) = b ; #h(0em) sans(l e t) #h(0em) w = g ; #h(0em) \( w \, x^q \) approx sans(l e t) #h(0em) \( g \, x \) = b ; #h(0em) \( g \, x^q \) & approx \( g \, x \) $
    since if $q eq.not 0$ $\( g \, x^q \) := \( g \, x \)$, whereas if
    $q = 0$ since $x$ is pure and of type $upright(bold(1))$, by
    $upright(bold(t e r m))$,
    $\( g \, x^q \) := \( g \, \( \) \) approx \( g \, x \)$.

~◻

]
To show completeness, it hence suffices to prove the following lemma:

#block[
Given $Gamma^(upright(bold(q))) tack.r_() a : A$, we have that, for all
$\( lambda x . a_x \) in ⟦ Gamma^(upright(bold(q))) tack.r_() a : A ⟧_(sans(T m) \( cal(R) \))$,
$ Gamma^(upright(bold(q))) tack.r_(cal(R)) sans(l e t) #h(0em) x = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) a_x approx a : A $

]
#block[
#emph[Proof.] Throughout this proof, given morphism
$f in sans(T m) \( cal(R) \) \( A \, B \)$, we will use $f \( x \)$ as a
stand-in for an arbitrary member of the appropriate equivalence class.
We note that (for arbitrary types)
$ sans(l e t) #h(0em) x = a ; #h(0em) \( f ; g \) \( x \) approx sans(l e t) #h(0em) y = \( sans(l e t) #h(0em) x = a ; #h(0em) f \( x \) \) ; #h(0em) g \( y \) $
and hence that, if
$sans(l e t) #h(0em) x = a ; #h(0em) f \( x \) approx a'$,
$sans(l e t) #h(0em) x = a ; #h(0em) \( f ; g \) \( x \) = sans(l e t) #h(0em) x = a' ; #h(0em) g \( x \)$.
In particular, we hence have that

- Given $b$ pure and
  $sans(l e t) #h(0em) x = a ; #h(0em) f \( x \) = a'$,
  $sans(l e t) #h(0em) y = b ; #h(0em) g \( y \) = b'$, we have
  $ sans(l e t) #h(0em) z = \( a \, b \) ; #h(0em) \( \( f ⊗ g \) ; h \) \( z \) approx sans(l e t) #h(0em) z = \( a' \, b' \) ; #h(0em) h \( z \) $

- Given $a$ pure,
  $  & sans(l e t) #h(0em) z = \( a \, b \) ; #h(0em) \( delta^(- 1) ; f \) \( z \)\
   & approx sans(c a s e) #h(0em) b #h(0em) { iota_l #h(0em) y_l : sans(l e t) #h(0em) z_l = iota_l #h(0em) \( a \, y_l \) ; #h(0em) f \( z_l \) \, iota_r #h(0em) y_r : sans(l e t) #h(0em) z_r = iota_r #h(0em) \( a \, y_r \) ; #h(0em) f \( z_r \) }\
   & approx sans(c a s e) #h(0em) b #h(0em) { iota_l #h(0em) y_l : sans(l e t) #h(0em) z_l = \( a \, y_l \) ; #h(0em) iota_l ; f \( z_l \) \, iota_r #h(0em) y_r : sans(l e t) #h(0em) z_r = \( a \, y_r \) ; #h(0em) iota_r ; f \( z_r \) } $
  In particular, this implies that
  $  & sans(l e t) #h(0em) z = \( a \, b \) ; #h(0em) \( delta^(- 1) ; \[ f \, g \] \) \( z \)\
   & approx sans(c a s e) #h(0em) b #h(0em) { iota_l #h(0em) y_l : sans(l e t) #h(0em) z_l = \( a \, y_l \) ; #h(0em) f \( z_l \) \, iota_r #h(0em) y_r : sans(l e t) #h(0em) z_r = \( a \, y_r \) ; #h(0em) g \( z_r \) } $

We begin by showing that
$ ⟦ Gamma^(upright(bold(q))) mapsto dot.op ⟧ approx \( lambda x . \( \) \) $
which we do by a straightforward induction on the derivation
$Gamma^(upright(bold(q))) mapsto dot.op$:

- ($dot.op mapsto dot.op$): we have
  $⟦ dot.op mapsto dot.op ⟧ = sans(i d)_(upright(bold(1))) = \( lambda x : upright(bold(1)) . x \) = \( lambda x . \( \) \)$
  as desired.

- ($Gamma^(upright(bold(q))) \, x : A^q mapsto dot.op$): we have that
  $ ⟦ Gamma^(upright(bold(q))) \, x : A^q mapsto dot.op ⟧ & = \[ Gamma^(upright(bold(q))) \] ⊗ !_(A^q) ; rho ; ⟦ Gamma^(upright(bold(q))) mapsto dot.op ⟧ = \( lambda \( x \, y \) . \( \( \) \, \( \) \) \) ; \( lambda \( z \, w \) . z \) ; \( lambda u . \( \) \)\
   & = \( lambda \( x \, y \) . \( \) \) ; \( lambda u . \( \) \) = \( lambda \( x \, y \) . \( \) \) = \( lambda u . \( \) \) $

It follows immediately that
$ Gamma^(upright(bold(q))) tack.r_tack.t sans(l e t) #h(0em) x = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) ⟦ Gamma^(upright(bold(q))) mapsto dot.op ⟧ \( x \) approx sans(l e t) #h(0em) x = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) \( \) approx \( \) : upright(bold(1)) $
We may therefore show that
$ Gamma^(upright(bold(q))) tack.r_tack.t sans(l e t) #h(0em) x = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) ⟦ Gamma^(upright(bold(q))) mapsto y : A^1 ⟧ \( x \) approx \( \( \) \, y \) \) : \[ y : A^1 \] $
We proceed by induction on the derivation
$Gamma^(upright(bold(q))) mapsto y : A^1$:

- ($Gamma^(upright(bold(q))) \, y : A^q mapsto y : A^1$): we have that
  $ ⟦ Gamma^(upright(bold(q))) \, y : A^q mapsto y : A^1 ⟧ & = ⟦ Gamma^(upright(bold(q))) mapsto dot.op ⟧ ⊗ sans(i d) = \( lambda x . \( \) \) ⊗ \( lambda y . y \) = \( lambda \( x \, y \) . \( \( \) \, y \) \) $
  It follows that
  $ Gamma^(upright(bold(q))) \, y : A^q & tack.r_tack.t sans(l e t) #h(0em) x = sans(p a c k) \( Gamma^(upright(bold(q))) \, y : A^q \) ; #h(0em) ⟦ Gamma^(upright(bold(q))) \, y : A^q mapsto y : A^1 ⟧ \( x \)\
   & approx sans(l e t) #h(0em) x = \( sans(p a c k) \( Gamma^(upright(bold(q))) \, y \) \) ; #h(0em) \( lambda \( z \, w \) . \( \( \) \, w \) \) \( x \)\
   & approx sans(l e t) #h(0em) \( z \, w \) = \( sans(p a c k) \( Gamma^(upright(bold(q))) \, y \) \) ; #h(0em) \( \( \) \, w \)\
   & approx \( \( \) \, y \) : \[ y : A^1 \] $

- ($Gamma^(upright(bold(q))) \, z : B^q mapsto y : A^1$): we have that
  $ ⟦ Gamma^(upright(bold(q))) \, z : B^q mapsto y : A^1 ⟧ & = \[ Gamma^(upright(bold(q))) \] ⊗ !_(B^q) ; rho ; ⟦ Gamma^(upright(bold(q))) mapsto y : A^1 ⟧\
   & = \( lambda \( x \, y \) . \( x \, \( \) \) \) ; \( lambda \( z \, w \) . z \) ; ⟦ Gamma^(upright(bold(q))) mapsto y : A^1 ⟧\
   & = \( lambda \( x \, y \) . x \) ; ⟦ Gamma^(upright(bold(q))) mapsto y : A^1 ⟧\
   & = \( lambda \( x \, y \) . ⟦ Gamma^(upright(bold(q))) mapsto y : A^1 ⟧ \( x \) \) $
  It follows by induction that
  $ Gamma^(upright(bold(q))) \, z : B^q & tack.r_tack.t sans(l e t) #h(0em) x = sans(p a c k) \( Gamma^(upright(bold(q))) \, z : B^q \) ; #h(0em) ⟦ Gamma^(upright(bold(q))) \, y : A^q mapsto y : A^1 ⟧ \( x \)\
   & approx sans(l e t) #h(0em) x = sans(p a c k) \( Gamma^(upright(bold(q))) \, z^q \) ; #h(0em) lambda \( w \, u \) . ⟦ Gamma^(upright(bold(q))) mapsto y : A^1 ⟧ \( w \)\
   & approx sans(l e t) #h(0em) w = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) ⟦ Gamma^(upright(bold(q))) mapsto y : A^1 ⟧ \( w \) approx \( \( \) \, y \) : \[ y : A^1 \] $

Similarly, we have that
$ Gamma^(upright(bold(q))) tack.r_tack.t sans(l e t) #h(0em) x = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q_r)) ⟧ \( x \) approx \( sans(p a c k) \( Gamma^(upright(bold(q))_l) \) \, sans(p a c k) \( Gamma^(upright(bold(q))_r) \) \) : \[ Gamma^(upright(bold(q))_l) \] ⊗ \[ Gamma^(upright(bold(q))_r) \] $
We proceed by induction on the derivation
$Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q_r))$:

- $\( dot.op tack.r dot.op = dot.op + dot.op \)$: we have that
  $ dot.op & tack.r_tack.t sans(l e t) #h(0em) x = sans(p a c k) \( dot.op \) ; #h(0em) ⟦ dot.op tack.r dot.op = dot.op + dot.op ⟧ \( x \) approx sans(l e t) #h(0em) x = \( \) ; #h(0em) rho^(- 1) \( x \)\
   & approx sans(l e t) #h(0em) x = \( \) ; #h(0em) \( x \, \( \) \) approx \( \( \) \, \( \) \) approx \( sans(p a c k) \( dot.op \) \, sans(p a c k) \( dot.op \) \) : \[ sans(p a c k) \( dot.op \) \] ⊗ \[ sans(p a c k) \( dot.op \) \] $
  as desired.

- $\( Gamma \, x : A tack.r upright(bold(q)) \, q = upright(bold(q))_l \, q + upright(bold(q))_r \, 0 \)$:
  we have that
  $ Gamma^(upright(bold(q))) \, x : A^q & tack.r_tack.t sans(l e t) #h(0em) w = sans(p a c k) \( Gamma^(upright(bold(q))) \, x : A^q \) ; #h(0em) ⟦ Gamma \, x : A tack.r upright(bold(q)) \, q = upright(bold(q))_l \, q + upright(bold(q))_r \, 0 ⟧ \( w \)\
   & approx sans(l e t) #h(0em) w = \( sans(p a c k) \( Gamma^(upright(bold(q))) \) \, x^q \) ; #h(0em) \( ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ⊗ rho^(- 1) ; sigma^(sans(m i d)) \) \( w \)\
   & approx sans(l e t) #h(0em) w = \( sans(p a c k) \( Gamma^(upright(bold(q))) \) \, x^q \) ; #h(0em) \( \( lambda \( y \, z \) . \( ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ \( y \) \, \( z \, \( \) \) \) \) ; sigma^(sans(m i d)) \) \( w \)\
   & approx sans(l e t) #h(0em) y = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) sans(l e t) #h(0em) z = x^q ; #h(0em) sans(l e t) #h(0em) u = \( ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ \( y \) \, \( z \, \( \) \) \) ; #h(0em) sigma^(sans(m i d)) \( u \)\
   & approx sans(l e t) #h(0em) y = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) sans(l e t) #h(0em) u = \( ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ \( y \) \, \( x^q \, \( \) \) \) ; #h(0em) sigma^(sans(m i d)) \( u \)\
   & approx sans(l e t) #h(0em) u = \( \( sans(l e t) #h(0em) y = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) \( ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ \( y \) \) \, \( x^q \, \( \) \) \) ; #h(0em) sigma^(sans(m i d)) \( u \)\
   & approx sans(l e t) #h(0em) \( \( u_1 \, u_2 \) \, \( u_3 \, u_4 \) = \( \( sans(p a c k) \( Gamma^(upright(bold(q))_l) \) \, sans(p a c k) \( Gamma^(upright(bold(q))_r) \) \) \, \( x^q \, \( \) \) \) ; #h(0em) \( \( u_1 \, u_3 \) \, \( u_2 \, u_4 \) \)\
   & approx \( sans(p a c k) \( Gamma^(upright(bold(q))_l) \) \, x^q \) \, \( sans(p a c k) \( Gamma^(upright(bold(q))_r) \) \, \( \) \) \)\
   & approx \( sans(p a c k) \( Gamma^(upright(bold(q))_l) \, x : A^q \) \, sans(p a c k) \( Gamma^(upright(bold(q))_r) \, x : A^0 \) \) : \[ Gamma^(upright(bold(q))_l) \, x : A^q \] ⊗ \[ Gamma^(upright(bold(q))_r) \, x : A^0 \] $
  as desired.

- $\( Gamma \, x : A tack.r upright(bold(q)) \, q = upright(bold(q))_l \, 0 + upright(bold(q))_r \, q \)$:
  we have that
  $ Gamma^(upright(bold(q))) \, x : A^q & tack.r_tack.t sans(l e t) #h(0em) w = sans(p a c k) \( Gamma^(upright(bold(q))) \, x : A^q \) ; #h(0em) ⟦ Gamma \, x : A tack.r upright(bold(q)) \, q = upright(bold(q))_l \, 0 + upright(bold(q))_r \, q ⟧ \( w \)\
   & approx sans(l e t) #h(0em) w = \( sans(p a c k) \( Gamma^(upright(bold(q))) \) \, x^q \) ; #h(0em) \( ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ⊗ lambda^(- 1) ; sigma^(sans(m i d)) \) \( w \)\
   & approx sans(l e t) #h(0em) w = \( sans(p a c k) \( Gamma^(upright(bold(q))) \) \, x^q \) ; #h(0em) \( \( lambda \( y \, z \) . \( ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ \( y \) \, \( \( \) \, z \) \) \) ; sigma^(sans(m i d)) \) \( w \)\
   & approx sans(l e t) #h(0em) y = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) sans(l e t) #h(0em) z = x^q ; #h(0em) sans(l e t) #h(0em) u = \( ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ \( y \) \, \( \( \) \, z \) \) ; #h(0em) sigma^(sans(m i d)) \( u \)\
   & approx sans(l e t) #h(0em) y = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) sans(l e t) #h(0em) u = \( ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ \( y \) \, \( \( \) \, x^q \) \) ; #h(0em) sigma^(sans(m i d)) \( u \)\
   & approx sans(l e t) #h(0em) u = \( \( sans(l e t) #h(0em) y = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) \( ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ \( y \) \) \, \( \( \) \, x^q \) \) ; #h(0em) sigma^(sans(m i d)) \( u \)\
   & approx sans(l e t) #h(0em) \( \( u_1 \, u_2 \) \, \( u_3 \, u_4 \) = \( \( sans(p a c k) \( Gamma^(upright(bold(q))_l) \) \, sans(p a c k) \( Gamma^(upright(bold(q))_r) \) \) \, \( \( \) \, x^q \) \) ; #h(0em) \( \( u_1 \, u_3 \) \, \( u_2 \, u_4 \) \)\
   & approx \( sans(p a c k) \( Gamma^(upright(bold(q))_l) \) \, \( \) \) \, \( sans(p a c k) \( Gamma^(upright(bold(q))_r) \) \, x^q \) \)\
   & approx \( sans(p a c k) \( Gamma^(upright(bold(q))_l) \, x : A^0 \) \, sans(p a c k) \( Gamma^(upright(bold(q))_r) \, x : A^q \) \) : \[ Gamma^(upright(bold(q))_l) \, x : A^0 \] ⊗ \[ Gamma^(upright(bold(q))_r) \, x : A^q \] $
  as desired.

- $\( Gamma \, x : A tack.r upright(bold(q)) \, q = upright(bold(q))_l \, q + upright(bold(q))_r \, q \)$:
  we have that
  $ Gamma^(upright(bold(q))) \, x : A^q & tack.r_tack.t sans(l e t) #h(0em) w = sans(p a c k) \( Gamma^(upright(bold(q))) \, x : A^q \) ; #h(0em) ⟦ Gamma \, x : A tack.r upright(bold(q)) \, q = upright(bold(q))_l \, q + upright(bold(q))_r \, q ⟧ \( w \)\
   & approx sans(l e t) #h(0em) w = \( sans(p a c k) \( Gamma^(upright(bold(q))) \) \, x^q \) ; #h(0em) \( ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ⊗ Delta_() ; sigma^(sans(m i d)) \) \( w \)\
   & approx sans(l e t) #h(0em) w = \( sans(p a c k) \( Gamma^(upright(bold(q))) \) \, x^q \) ; #h(0em) \( \( lambda \( y \, z \) . \( ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ \( y \) \, \( z \, z \) \) \) ; sigma^(sans(m i d)) \) \( w \)\
   & approx sans(l e t) #h(0em) y = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) sans(l e t) #h(0em) z = x^q ; #h(0em) sans(l e t) #h(0em) u = \( ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ \( y \) \, \( z \, z \) \) ; #h(0em) sigma^(sans(m i d)) \( u \)\
   & approx sans(l e t) #h(0em) y = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) sans(l e t) #h(0em) u = \( ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ \( y \) \, \( x^q \, x^q \) \) ; #h(0em) sigma^(sans(m i d)) \( u \)\
   & approx sans(l e t) #h(0em) u = \( \( sans(l e t) #h(0em) y = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) \( ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ \( y \) \) \, \( x^q \, x^q \) \) ; #h(0em) sigma^(sans(m i d)) \( u \)\
   & approx sans(l e t) #h(0em) \( \( u_1 \, u_2 \) \, \( u_3 \, u_4 \) = \( \( sans(p a c k) \( Gamma^(upright(bold(q))_l) \) \, sans(p a c k) \( Gamma^(upright(bold(q))_r) \) \) \, \( x^q \, x^q \) \) ; #h(0em) \( \( u_1 \, u_3 \) \, \( u_2 \, u_4 \) \)\
   & approx \( sans(p a c k) \( Gamma^(upright(bold(q))_l) \) \, x^q \) \, \( sans(p a c k) \( Gamma^(upright(bold(q))_r) \) \, x^q \) \)\
   & approx \( sans(p a c k) \( Gamma^(upright(bold(q))_l) \, x : A^q \) \, sans(p a c k) \( Gamma^(upright(bold(q))_r) \, x : A^q \) \) : \[ Gamma^(upright(bold(q))_l) \, x : A^q \] ⊗ \[ Gamma^(upright(bold(q))_r) \, x : A^q \] $
  as desired.

We now wish to show that, given
$f in sans(T m) \( cal(R) \) \( A \, B \)$,
$ Gamma^(upright(bold(q))) tack.r_(cal(R)) sans(l e t) #h(0em) x = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) ⟦ Gamma^(upright(bold(q))) tack.r_() a : A ⟧_(sans(T m) \( cal(R) \)) \( x \) approx a : A $
We proceed by induction on the derivation
$Gamma^(upright(bold(q))) tack.r_() a : A$:

- $\( Gamma^(upright(bold(q))) tack.r_() x : A \)$: we have that
  $ Gamma^(upright(bold(q))) & tack.r_tack.t sans(l e t) #h(0em) y = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) ⟦ Gamma^(upright(bold(q))) tack.r_() x : A ⟧ \( y \)\
   & approx sans(l e t) #h(0em) y = sans(p a c k) \( Gamma \)^(upright(bold(q))) ; #h(0em) \( ⟦ Gamma^(upright(bold(q))) mapsto x : A^1 ⟧ ; lambda \) \( y \)\
   & approx sans(l e t) #h(0em) y = \( sans(l e t) #h(0em) z = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) ⟦ Gamma^(upright(bold(q))) mapsto x : A^1 ⟧ \( z \) \) ; #h(0em) \( lambda \( w \, u \) . u \) \( y \)\
   & approx sans(l e t) #h(0em) \( w \, u \) = \( x \, \( \) \) ; #h(0em) u approx x : A $
  as desired.

- ($Gamma^(upright(bold(q))) tack.r_epsilon.alt f #h(0em) a : B$): we
  have that
  $ Gamma^(upright(bold(q))) & tack.r_tack.t sans(l e t) #h(0em) x = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) ⟦ Gamma^(upright(bold(q))) tack.r_() f #h(0em) a : B ⟧ \( x \)\
   & approx sans(l e t) #h(0em) x = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) \( ⟦ Gamma^(upright(bold(q))) tack.r_() a : A ⟧ ; \( lambda y . f #h(0em) y \) \) \( x \)\
   & approx sans(l e t) #h(0em) x = \( sans(l e t) #h(0em) y = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) ⟦ Gamma^(upright(bold(q))) tack.r_() a : A ⟧ \) ; #h(0em) f #h(0em) x\
   & approx sans(l e t) #h(0em) x = a ; #h(0em) f #h(0em) x approx f #h(0em) a : B $

- $\( Gamma^(upright(bold(q))) tack.r_() sans(l e t) #h(0em) x = a ; #h(0em) b : B \)$:
  we have
  $ Gamma^(upright(bold(q))) & tack.r_tack.t sans(l e t) #h(0em) y = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) ⟦ Gamma^(upright(bold(q))) tack.r_() sans(l e t) #h(0em) x = a ; #h(0em) b : B ⟧ \( y \)\
   & approx sans(l e t) #h(0em) y = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) \( ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ; \[ Gamma^(upright(bold(q))_l) \] ⊗ ⟦ Gamma^(upright(bold(q))_r) tack.r_epsilon.alt a : A ⟧ ; ⟦ Gamma^(upright(bold(q))_l) \, x : A tack.r_epsilon.alt b : B ⟧ \) \( y \)\
   & approx sans(l e t) #h(0em) y = \( sans(p a c k) \( Gamma^(upright(bold(q))_l) \) \, sans(p a c k) \( Gamma^(upright(bold(q))_r) \) \) ; #h(0em) \( \[ Gamma^(upright(bold(q))_l) \] ⊗ ⟦ Gamma^(upright(bold(q))_r) tack.r_epsilon.alt a : A ⟧ ; ⟦ Gamma^(upright(bold(q))_l) \, x : A tack.r_epsilon.alt b : B ⟧ \) \( y \)\
   & approx sans(l e t) #h(0em) y = \( sans(p a c k) \( Gamma^(upright(bold(q))_l) \) \, a \) \) ; #h(0em) \( ⟦ Gamma^(upright(bold(q))_l) \, x : A tack.r_epsilon.alt b : B ⟧ \) \( y \)\
   & approx sans(l e t) #h(0em) x = a ; #h(0em) sans(l e t) #h(0em) y = \( sans(p a c k) \( Gamma^(upright(bold(q))_l) \) \, x \) \) ; #h(0em) \( ⟦ Gamma^(upright(bold(q))_l) \, x : A tack.r_epsilon.alt b : B ⟧ \) \( y \)\
   & approx sans(l e t) #h(0em) x = a ; #h(0em) sans(l e t) #h(0em) y = \( sans(p a c k) \( Gamma^(upright(bold(q))_l) \, x : A \) \) \) ; #h(0em) \( ⟦ Gamma^(upright(bold(q))_l) \, x : A tack.r_epsilon.alt b : B ⟧ \) \( y \)\
   & approx sans(l e t) #h(0em) x = a ; #h(0em) b : B $

- $\( Gamma^(upright(bold(q))) tack.r_() \( \) : upright(bold(1)) \)$:
  we have
  $ Gamma^(upright(bold(q))) & tack.r_tack.t sans(l e t) #h(0em) x = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) ⟦ Gamma^(upright(bold(q))) tack.r_() \( \) : upright(bold(1)) ⟧ \( x \)\
   & approx sans(l e t) #h(0em) x = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) \( ⟦ Gamma^(upright(bold(q))) mapsto dot.op ⟧ \) \( x \)\
   & approx sans(l e t) #h(0em) x = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) \( \) approx \( \) $

- $\( Gamma^(upright(bold(q))) tack.r_() \( a \, b \) : A ⊗ B \)$:
  we have that
  $ Gamma^(upright(bold(q))) & tack.r_tack.t sans(l e t) #h(0em) x = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) ⟦ Gamma^(upright(bold(q))) tack.r_() \( a \, b \) : A ⊗ B ⟧ \( x \)\
   & approx sans(l e t) #h(0em) x = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) \( ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ; ⟦ Gamma^(upright(bold(q))_l) tack.r_() a : A ⟧ times.l ⟦ Gamma^(upright(bold(q))_r) tack.r_() b : B ⟧ \) \( x \)\
   & approx sans(l e t) #h(0em) x = \( sans(l e t) #h(0em) y = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ \) ; #h(0em) \( ⟦ Gamma^(upright(bold(q))_l) tack.r_() a : A ⟧ times.l ⟦ Gamma^(upright(bold(q))_r) tack.r_() b : B ⟧ \) \( x \)\
   & approx sans(l e t) #h(0em) x = \( sans(p a c k) \( Gamma^(upright(bold(q))_l) \) \, sans(p a c k) \( Gamma^(upright(bold(q))_r) \) \) ; #h(0em) \( ⟦ Gamma^(upright(bold(q))_l) tack.r_() a : A ⟧ times.l ⟦ Gamma^(upright(bold(q))_r) tack.r_() b : B ⟧ \) \( x \)\
   & approx \( sans(l e t) #h(0em) x = sans(p a c k) \( Gamma^(upright(bold(q))_l) \) ; #h(0em) ⟦ Gamma^(upright(bold(q))_l) tack.r_() a : A ⟧ \( x \) \, sans(l e t) #h(0em) y = sans(p a c k) \( Gamma^(upright(bold(q))_r) \) ; #h(0em) ⟦ Gamma^(upright(bold(q))_r) tack.r_() b : B ⟧ \( y \) \) approx \( a \, b \) : A ⊗ B $

- $\( Gamma^(upright(bold(q))) tack.r_() sans(l e t) #h(0em) \( x \, y \) = a ; #h(0em) c : C \)$:
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
  we have that \$\$\\begin{aligned}
      \\Gamma^{\\ensuremath{\\mathbf{q}}} &\\vdash\_\\bot
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = \\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}});\\;\\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;(x, y) = a;\\;c}: {C}}\\rrbracket(z)} \\\\
        &\\approx
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = \\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}});\\; \\\\ & \\qquad 
          (\\llbracket{\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}\\rrbracket
          ; \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}}\\rrbracket \\otimes \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} a: {A \\otimes B}}\\rrbracket
          ; \\alpha
          ; \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A, y : B \\vdash\_{\\epsilon} c: {C}}\\rrbracket
          )(z)
        } \\\\
        &\\approx
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = (\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), \\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_r}));\\;\\\\ & \\qquad ( 
          \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}}\\rrbracket \\otimes \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} a: {A \\otimes B}}\\rrbracket
          ; \\alpha
          ; \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A, y : B \\vdash\_{\\epsilon} c: {C}}\\rrbracket
          )(z)
        } \\\\
        &\\approx
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = (\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), 
          \\ensuremath{\\ensuremath{\\mathsf{let}}\\;w = \\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_r});\\;
              \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} a: {A \\otimes B}(w)}\\rrbracket
            }
          )
          ;\\;\\\\ & \\qquad (
          \\alpha
          ; \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A, y : B \\vdash\_{\\epsilon} c: {C}}\\rrbracket
          )(z)
        } \\\\
        &\\approx
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = (\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), a)
          ;\\;(
          \\alpha
          ; \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A, y : B \\vdash\_{\\epsilon} c: {C}}\\rrbracket
          )(z)
        }\\\\
        &\\approx
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;(z\_1, (z\_2, z\_3)) = (\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), a)
          ;\\;\\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = ((z\_1, z\_2), z\_3);\\;\\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A, y : B \\vdash\_{\\epsilon} c: {C}}\\rrbracket(z)}
        } \\\\
        &\\approx
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;(z\_2, z\_3) = a;\\;\\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = ((\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), z\_2), z\_3);\\;\\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A, y : B \\vdash\_{\\epsilon} c: {C}}\\rrbracket(z)}
        } \\\\
        &\\approx
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;(z\_2, z\_3) = a;\\;\\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = \\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, z\_2 : A, z\_3 : B);\\;\\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A, y : B \\vdash\_{\\epsilon} c: {C}}\\rrbracket(z)}
        }\\\\
        &\\approx
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;(z\_2, z\_3) = a;\\;\[z\_3/y\]\[z\_2/x\]c}
        \\approx
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;(x, y) = a;\\;c} : C
      
  \\end{aligned}\$\$

- $\( Gamma^(upright(bold(q))) tack.r_() iota_l #h(0em) a : A + B \)$:
  we have that
  $ Gamma^(upright(bold(q))) & tack.r_tack.t sans(l e t) #h(0em) x = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) ⟦ Gamma^(upright(bold(q))) tack.r_() iota_l #h(0em) a : A + B ⟧ \( x \)\
   & approx sans(l e t) #h(0em) x = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) \( ⟦ Gamma^(upright(bold(q))) tack.r_() a : A ⟧ ; iota_l \) \( x \)\
   & approx sans(l e t) #h(0em) x = \( sans(l e t) #h(0em) y = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) ⟦ Gamma^(upright(bold(q))) tack.r_() a : A ⟧ \) ; #h(0em) iota_l #h(0em) x\
   & approx sans(l e t) #h(0em) x = a ; #h(0em) iota_l #h(0em) x approx iota_l #h(0em) a : A + B $

- $\( Gamma^(upright(bold(q))) tack.r_() iota_r #h(0em) b : A + B \)$:
  we have that
  $ Gamma^(upright(bold(q))) & tack.r_tack.t sans(l e t) #h(0em) x = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) ⟦ Gamma^(upright(bold(q))) tack.r_() iota_r #h(0em) b : A + B ⟧ \( x \)\
   & approx sans(l e t) #h(0em) x = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) \( ⟦ Gamma^(upright(bold(q))) tack.r_() b : B ⟧ ; iota_r \) \( x \)\
   & approx sans(l e t) #h(0em) x = \( sans(l e t) #h(0em) y = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) ⟦ Gamma^(upright(bold(q))) tack.r_() b : B ⟧ \) ; #h(0em) iota_r #h(0em) x\
   & approx sans(l e t) #h(0em) x = b ; #h(0em) iota_r #h(0em) x approx iota_r #h(0em) b : A + B $

- $\( Gamma^(upright(bold(q))) tack.r_() sans(c a s e) #h(0em) e #h(0em) { iota_l #h(0em) x : a \, iota_r #h(0em) y : b } : C \)$:
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
  we have that \$\$\\begin{aligned}
      \\Gamma^{\\ensuremath{\\mathbf{q}}} &\\vdash\_\\bot
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = \\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}});\\;\\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{} \\ensuremath{\\mathsf{case}}\\;e\\;\\{\\iota\_l\\;{x} :a, \\iota\_r\\;{y} :b\\}: {C}}\\rrbracket(z)}
        \\\\ &\\approx 
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = \\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}});\\;(\\llbracket{\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}\\rrbracket
          ; \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}}\\rrbracket \\otimes \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} e: {A + B}}\\rrbracket
          ; \\delta^{-1} \\\\ & \\qquad
          ; \[
            \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\epsilon} a: {C}}\\rrbracket,
            \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, y : B \\vdash\_{\\epsilon} b: {C}}\\rrbracket
          \])(z)}
        \\\\ &\\approx
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = (\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), \\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_r}));\\;(
          \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}}\\rrbracket \\otimes \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} e: {A + B}}\\rrbracket
          ; \\delta^{-1} \\\\ & \\qquad
          ; \[
            \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\epsilon} a: {C}}\\rrbracket,
            \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, y : B \\vdash\_{\\epsilon} b: {C}}\\rrbracket
          \])(z)}
        \\\\ &\\approx
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = (\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), 
          \\ensuremath{\\ensuremath{\\mathsf{let}}\\;w = \\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_r});\\;
            \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} e: {A + B}}\\rrbracket(w)});\\;(  \\\\ & \\qquad
          \\delta^{-1}
          ; \[
            \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\epsilon} a: {C}}\\rrbracket,
            \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, y : B \\vdash\_{\\epsilon} b: {C}}\\rrbracket
          \])(z)}
        \\\\ &\\approx
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = (\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), e);\\;(
          \\delta^{-1}
          ; \[
            \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\epsilon} a: {C}}\\rrbracket,
            \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, y : B \\vdash\_{\\epsilon} b: {C}}\\rrbracket
          \])(z)}
        \\\\ &\\approx
        \\ensuremath{\\mathsf{case}}\\;e \\\\ & \\qquad\\;\\;\\{\\iota\_l\\;{x} :\\ensuremath{\\ensuremath{\\mathsf{let}}\\;w = (\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), x);\\;
            \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\epsilon} a: {C}}\\rrbracket(w)} \\\\ & \\qquad, \\iota\_r\\;{y} :\\ensuremath{\\ensuremath{\\mathsf{let}}\\; = (\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), y);\\;
            \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, y : B \\vdash\_{\\epsilon} b: {C}}\\rrbracket}\\}
        \\\\ &\\approx
        \\ensuremath{\\mathsf{case}}\\;e \\\\ & \\qquad\\;\\{\\iota\_l\\;{x} :\\ensuremath{\\ensuremath{\\mathsf{let}}\\;w = \\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A));\\;
            \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\epsilon} a: {C}}\\rrbracket(w)} \\\\ & \\qquad, \\iota\_r\\;{y} :\\ensuremath{\\ensuremath{\\mathsf{let}}\\; = \\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), y : B);\\;
            \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, y : B \\vdash\_{\\epsilon} b: {C}}\\rrbracket}\\}
        \\\\ &\\approx
        \\ensuremath{\\mathsf{case}}\\;e\\;\\{\\iota\_l\\;{x} :a, \\iota\_r\\;{y} :b\\} : C
      
  \\end{aligned}\$\$

- $\( Gamma^(upright(bold(q))) tack.r_() sans(a b o r t) #h(0em) a : A \)$:
  we have that
  $ Gamma^(upright(bold(q))) & tack.r_tack.t sans(l e t) #h(0em) x = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) ⟦ Gamma^(upright(bold(q))) tack.r_() sans(a b o r t) #h(0em) a : A ⟧ \( x \)\
   & approx sans(l e t) #h(0em) x = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) \( ⟦ Gamma^(upright(bold(q))) tack.r_() a : upright(bold(0)) ⟧ ; 0_A \) \( x \)\
   & approx sans(l e t) #h(0em) x = \( sans(l e t) #h(0em) y = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) ⟦ Gamma^(upright(bold(q))) tack.r_() a : upright(bold(0)) ⟧ \) ; #h(0em) sans(a b o r t) #h(0em) x\
   & approx sans(l e t) #h(0em) x = a ; #h(0em) sans(a b o r t) #h(0em) x approx sans(a b o r t) #h(0em) a : A $

- $\( Gamma^(upright(bold(q))) tack.r_() sans(i t e r) #h(0em) a #h(0em) { iota_r #h(0em) x : b } : B \)$:
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
  we begin by noting that \$\$\\begin{aligned}
      \\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, y : A &\\vdash\_\\bot
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;w = (\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), y);\\; \\\\ & \\qquad
          (
            \\llbracket{\\Gamma \\vdash \\ensuremath{\\mathbf{q}}\_l = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_l}\\rrbracket \\otimes A 
            ; \\alpha
            ; \[\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}\] 
              \\otimes \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\epsilon} b: {B + A}}\\rrbracket
            ; \\delta^{-1}
          )(w)
        } \\\\
        % &\\approx
        % \\letexpr{w}{(\\letexpr{z}{(\\ms{pack}(\\Gamma^{\\mb{q}\_l}), y)}
        %   {(\\dnt{\\qsp{\\Gamma}{\\mb{q}\_l}{\\mb{q}\_l}{\\mb{q}\_l}} \\otimes A)(z)})}{ \\\\ & \\qquad (
        %   \\alpha
        %   ; \[\\Gamma^{\\mb{q}\_l}\] 
        %     \\otimes \\dnt{\\hasty{\\Gamma^{\\mb{q}\_l}, x : A}{\\epsilon}{b}{B + A}}
        %   ; \\delta^{-1}
        % )(w)} \\\\      
        &\\approx
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;w = ((\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), \\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l})), y);\\; (
          \\alpha
          ; \[\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}\] 
            \\otimes \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\epsilon} b: {B + A}}\\rrbracket
          ; \\delta^{-1}
        )(w)} \\\\  
        &\\approx
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;w = (\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), (\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), y));\\; (
          \[\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}\] \\otimes \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\epsilon} b: {B + A}}\\rrbracket
          ; \\delta^{-1}
        )(w)} \\\\  
        &\\approx
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;w = (\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), 
            \\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = (\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), y);\\;\\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\epsilon} b: {B + A}}\\rrbracket(z)}
          );\\;\\delta^{-1}(w)} \\\\
        &\\approx
        \\ensuremath{\\mathsf{case}}\\;(\\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = (\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), y);\\;\\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\epsilon} b: {B + A}}\\rrbracket(z)}
          )) \\\\ & \\qquad\\;\\{\\iota\_l\\;{w\_l} :\\iota\_l\\;{(\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), w\_l)}, \\iota\_r\\;{w\_r} :(\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), w\_r)\\} \\\\
        &\\approx
        \\ensuremath{\\mathsf{case}}\\;(\\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = (\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, y : A^q);\\;\\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\epsilon} b: {B + A}}\\rrbracket(z)}
          )) \\\\ & \\qquad\\;\\{\\iota\_l\\;{w\_l} :\\iota\_l\\;{(\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), w\_l)}, \\iota\_r\\;{w\_r} :(\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), w\_r)\\} \\\\
        &\\approx
        \\ensuremath{\\mathsf{case}}\\;\[y/x\]b\\;\\{\\iota\_l\\;{w\_l} :\\iota\_l\\;{(\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), w\_l)}, \\iota\_r\\;{w\_r} :(\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), w\_r)\\}
      
  \\end{aligned}\$\$ It follows by uniformity, since
  $\( sans(p a c k) \( Gamma^(upright(bold(q))_l) \) \, y \)$ is pure,
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
  that \$\$\\begin{aligned}
        \\Gamma^{\\ensuremath{\\mathbf{q}}} &\\vdash\_\\bot
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;y = a;\\;\\ensuremath{\\mathsf{iter}}\\;(\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), y)\\;\\{ \\iota\_r\\;{w} : \\\\ & \\qquad
          (
            \\llbracket{\\Gamma \\vdash \\ensuremath{\\mathbf{q}}\_l = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_l}\\rrbracket \\otimes A 
            ; \\alpha
            ; \[\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}\] 
              \\otimes \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\epsilon} b: {B + A}}\\rrbracket
            ; \\delta^{-1}
          )(w)
         \\}} \\\\
        &\\approx
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;u = \\ensuremath{\\mathsf{iter}}\\;a\\;\\{ \\iota\_r\\;{x} :b \\};\\;(\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), u)}
      
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
  \\end{aligned}\$\$ and therefore that \$\$\\begin{aligned}
      \\Gamma^{\\ensuremath{\\mathbf{q}}} &\\vdash\_\\bot
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = \\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}});\\;\\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{} \\ensuremath{\\mathsf{iter}}\\;a\\;\\{ \\iota\_r\\;{x} :b \\}: {B}}\\rrbracket(x)}
        \\\\ &\\approx 
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = \\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}});\\;(
            \\llbracket{\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}\\rrbracket
            ; \[\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}\] \\otimes \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} a: {A}}\\rrbracket
            ;
        \\\\ & \\qquad    
          (
            \\llbracket{\\Gamma \\vdash \\ensuremath{\\mathbf{q}}\_l = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_l}\\rrbracket \\otimes A 
            ; \\alpha
            ; \[\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}\] 
              \\otimes \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\epsilon} b: {B + A}}\\rrbracket
            ; \\delta^{-1}
          )^\\dagger  
          ;
        \\\\ & \\qquad
          \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l} \\mapsto \\cdot}\\rrbracket \\otimes B
          ; \\rho
        )(z)}
        % \\\\ &\\approx 
        % \\letexpr{z}{
        %     (\\letexpr{y}{\\ms{pack}(\\Gamma^{\\mb{q}})}
        %        {\\dnt{\\qsp{\\Gamma}{\\mb{q}}{\\mb{q}\_l}{\\mb{q}\_r}}})}
        %   {(
        %     \[\\Gamma^{\\mb{q}\_l}\] \\otimes \\dnt{\\hasty{\\Gamma^{\\mb{q}\_r}}{\\epsilon}{a}{A}} ;
        % \\\\ & \\qquad    
        %   (
        %     \\dnt{\\qsp{\\Gamma}{\\mb{q}\_l}{\\mb{q}\_l}{\\mb{q}\_l}} \\otimes A 
        %     ; \\alpha
        %     ; \[\\Gamma^{\\mb{q}\_l}\] 
        %       \\otimes \\dnt{\\hasty{\\Gamma^{\\mb{q}\_l}, x : A}{\\epsilon}{b}{B + A}}
        %     ; \\delta^{-1}
        %   )^\\dagger  
        %   ;
        % \\\\ & \\qquad
        %   \\dnt{\\cwk{\\Gamma^{\\mb{q}\_l}}{\\cdot}} \\otimes B
        %   ; \\rho
        % )(z)}
        \\\\ &\\approx 
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = 
            (\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), \\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_r}));\\;(
            \[\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}\] \\otimes \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} a: {A}}\\rrbracket ;
        \\\\ & \\qquad    
          (
            \\llbracket{\\Gamma \\vdash \\ensuremath{\\mathbf{q}}\_l = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_l}\\rrbracket \\otimes A 
            ; \\alpha
            ; \[\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}\] 
              \\otimes \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\epsilon} b: {B + A}}\\rrbracket
            ; \\delta^{-1}
          )^\\dagger  
          ;
        \\\\ & \\qquad
          \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l} \\mapsto \\cdot}\\rrbracket \\otimes B
          ; \\rho
        )(z)}
        % \\\\ &\\approx 
        % \\letexpr{z}{
        %     (\\ms{pack}(\\Gamma^{\\mb{q}\_l}), 
        %       \\letexpr{y}{\\ms{pack}(\\Gamma^{\\mb{q}\_r})}
        %         {\\dnt{\\hasty{\\Gamma^{\\mb{q}\_r}}{\\epsilon}{a}{A}}})}
        %   {(
        % \\\\ & \\qquad    
        %   (
        %     \\dnt{\\qsp{\\Gamma}{\\mb{q}\_l}{\\mb{q}\_l}{\\mb{q}\_l}} \\otimes A 
        %     ; \\alpha
        %     ; \[\\Gamma^{\\mb{q}\_l}\] 
        %       \\otimes \\dnt{\\hasty{\\Gamma^{\\mb{q}\_l}, x : A}{\\epsilon}{b}{B + A}}
        %     ; \\delta^{-1}
        %   )^\\dagger  
        %   ;
        % \\\\ & \\qquad
        %   \\dnt{\\cwk{\\Gamma^{\\mb{q}\_l}}{\\cdot}} \\otimes B
        %   ; \\rho
        % )(z)}
        \\\\ &\\approx 
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = 
            (\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), a);\\;(
        \\\\ & \\qquad    
          (
            \\llbracket{\\Gamma \\vdash \\ensuremath{\\mathbf{q}}\_l = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_l}\\rrbracket \\otimes A 
            ; \\alpha
            ; \[\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}\] 
              \\otimes \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\epsilon} b: {B + A}}\\rrbracket
            ; \\delta^{-1}
          )^\\dagger  
          ;
        \\\\ & \\qquad
          \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l} \\mapsto \\cdot}\\rrbracket \\otimes B
          ; \\rho
        )(z)}
        \\\\ &\\approx 
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = (
            \\ensuremath{\\ensuremath{\\mathsf{let}}\\;y = (\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), a);\\;
              \\\\ & \\qquad \\qquad
              (
                \\llbracket{\\Gamma \\vdash \\ensuremath{\\mathbf{q}}\_l = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_l}\\rrbracket \\otimes A 
                ; \\alpha
                ; \[\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}\] 
                  \\otimes \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\epsilon} b: {B + A}}\\rrbracket
                ; \\delta^{-1}
              )^\\dagger(y)
            }
          );\\; \\\\ & \\qquad (
          \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l} \\mapsto \\cdot}\\rrbracket \\otimes B
          ; \\rho
        )(z)}
        \\\\ &\\approx 
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = (
            \\ensuremath{\\ensuremath{\\mathsf{let}}\\;y = a;\\;\\ensuremath{\\mathsf{iter}}\\;(\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), y)\\;\\{ \\iota\_r\\;{w} : \\\\ & \\qquad \\qquad
              (
                \\llbracket{\\Gamma \\vdash \\ensuremath{\\mathbf{q}}\_l = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_l}\\rrbracket \\otimes A 
                ; \\alpha
                ; \[\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}\] 
                  \\otimes \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\epsilon} b: {B + A}}\\rrbracket
                ; \\delta^{-1}
              )(w)
             \\}}
          );\\; \\\\ & \\qquad (
          \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l} \\mapsto \\cdot}\\rrbracket \\otimes B
          ; \\rho
        )(z)}
        \\\\ &\\approx 
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = (
            \\ensuremath{\\ensuremath{\\mathsf{let}}\\;u = \\ensuremath{\\mathsf{iter}}\\;a\\;\\{ \\iota\_r\\;{x} :b \\};\\;(\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), u)}
          );\\;(
          \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l} \\mapsto \\cdot}\\rrbracket \\otimes B
          ; \\rho
        )(z)}
        \\\\ &\\approx 
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;u = \\ensuremath{\\mathsf{iter}}\\;a\\;\\{ \\iota\_r\\;{x} :b \\};\\;\\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = (\\ensuremath{\\mathsf{pack}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}), u);\\;(
          \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_l} \\mapsto \\cdot}\\rrbracket \\otimes B
          ; \\rho
        )(z)}}
        \\\\ &\\approx 
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;u = \\ensuremath{\\mathsf{iter}}\\;a\\;\\{ \\iota\_r\\;{x} :b \\};\\;\\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = ((), u);\\;\\rho(z)}}
        \\\\ &\\approx 
        \\ensuremath{\\ensuremath{\\mathsf{let}}\\;u = \\ensuremath{\\mathsf{iter}}\\;a\\;\\{ \\iota\_r\\;{x} :b \\};\\;u}
        \\approx \\ensuremath{\\mathsf{iter}}\\;a\\;\\{ \\iota\_r\\;{x} :b \\} : B
      
  \\end{aligned}\$\$ as desired.

~◻

]
Completeness follows directly from the above lemma, since, given
$  & ⟦ Gamma^(upright(bold(q))) tack.r_() a : A ⟧_(sans(T m) \( cal(R) \)) arrow.r.twohead ⟦ Gamma^(upright(bold(q))) tack.r_() b : A ⟧_(sans(T m) \( cal(R) \))\
 & arrow.r.double.long forall \( lambda x . a_x \) in ⟦ Gamma^(upright(bold(q))) tack.r_() a : A ⟧_(sans(T m) \( cal(R) \)) \, \( lambda x . b_x \) in ⟦ Gamma^(upright(bold(q))) tack.r_() b : A ⟧_(sans(T m) \( cal(R) \)) . x : \[ Gamma^(upright(bold(q))) \] tack.r_(cal(R)) a_x arrow.r.twohead b_x : A\
 & arrow.r.double.long Gamma^(upright(bold(q))) tack.r_(cal(R)) sans(l e t) #h(0em) x = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) a_x arrow.r.twohead sans(l e t) #h(0em) x = sans(p a c k) \( Gamma^(upright(bold(q))) \) ; #h(0em) b_x : A\
 & arrow.r.double.long Gamma^(upright(bold(q))) tack.r_(cal(R)) a arrow.r.twohead b : A $
as desired.

= Compiling Expressions to SSA
<refall:apx:ssa-roundtrip>
In this section, we give a compilation function $sans(S S A)_ell$ that
compiles a $lambda_(sans(i t e r))$ terms to an SSA program returning
its result as an argument to output label $ell$. We will then show that
this function is #emph[semantics-preserving], i.e. that it satisfies
the following property:
$ ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(S S A)_ell \( Gamma^(upright(bold(q))) tack.r_epsilon.alt a : A \) gt.tri ell \( A \)^(upright(bold(0))) ⟧ = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt a : A ⟧ ; alpha ; iota_r $
Here, the associator $alpha$ takes $⟦ A ⟧$
to
$⟦ Gamma^(upright(bold(0))) ⟧ ⊗ ⟦ A ⟧$
(the latter being a tensor product of monoidal units), which $iota_r$
then takes to
$⟦ \[ Gamma mapsto ell \( A \)^(upright(bold(0))) \] ⟧ = upright(bold(0)) + ⟦ Gamma^(upright(bold(0))) ⟧ ⊗ ⟦ A ⟧$.
We will do so by requiring the slightly stronger property that, for all
$Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$,
we have
$ ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(S S A)_ell \( Gamma^(upright(bold(q))_r) tack.r_epsilon.alt a : A \) gt.tri ell \( A \)^(upright(bold(q))_l) ⟧ = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ; ⟦ Gamma^(upright(bold(q))_l) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_r) tack.r_epsilon.alt a : A ⟧ ; iota_r $
As this transformation is complicated to state and verify for general
expressions, we will instead define #emph[ANF], and, after showing how
every expression can be compiled to an equivalent expression in ANF,
define $sans(S S A)_ell$ by induction over such expressions.

== ANF Expressions
<refall:anf-expressions>
We begin by defining ANF expressions $P \, Q \, R$ using the grammar in
Figure~@refall:fig:anf-syntax; these are treated as a subset of
$lambda_(sans(i t e r))$ expressions. In particular, an ANF program
consists of a sequence of instructions of the form
$sans(l e t) #h(0em) x = I ; #h(0em) P$ (along with destructurings
$sans(l e t) #h(0em) \( x \, y \) = o ; #h(0em) P$), where each
instruction $I$ either calls into a sub-program or returns the value of
an operation $o$. Our goal is to define a function $sans(A N F) \( a \)$
on terms such that, for all well-typed terms $a$,
$ Gamma^(upright(bold(q))) tack.r_(cal(R)) sans(A N F) \( a \) approx a : A $
Rather than do so directly, we will instead define a transformation
$sans(l e t)_(sans(A N F)) #h(0em) x = a ; P$ which, given an ANF
program $P$ and a term $a$, returns an ANF program such that
$ Gamma^(upright(bold(q))) tack.r_(cal(R)) sans(l e t)_(sans(A N F)) #h(0em) x = a ; P approx sans(l e t) #h(0em) x = a ; #h(0em) P : A $
We can then define
$sans(A N F) \( a \) := sans(l e t)_(sans(A N F)) #h(0em) x = a ; x$;
note that we trivially have that, for any $a$,
$sans(l e t)_(sans(A N F)) #h(0em) x = a ; x approx sans(l e t) #h(0em) x = a ; #h(0em) x approx a arrow.r.double.long sans(A N F) \( x \) approx a$
by definition. We can now proceed to define
$sans(l e t)_(sans(A N F)) #h(0em) x = a ; P$ by induction on terms $a$
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
as follows: \$\$\\begin{aligned}
  (\\ensuremath{\\mathsf{let}}\_{\\ensuremath{\\mathsf{ANF}}}\\;x = o; P) &:= (\\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = o;\\;P}) \\text{ where } o \\text{ is a valid instruction} \\\\
  (\\ensuremath{\\mathsf{let}}\_{\\ensuremath{\\mathsf{ANF}}}\\;x = f\\;a; P) &:= (\\ensuremath{\\mathsf{let}}\_{\\ensuremath{\\mathsf{ANF}}}\\;x\_a = a; \\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = f\\;x;\\;P}) \\\\
  (\\ensuremath{\\mathsf{let}}\_{\\ensuremath{\\mathsf{ANF}}}\\;x = \\ensuremath{\\ensuremath{\\mathsf{let}}\\;y = a;\\;b}; P) &:= (\\ensuremath{\\mathsf{let}}\_{\\ensuremath{\\mathsf{ANF}}}\\;y = a; \\ensuremath{\\mathsf{let}}\_{\\ensuremath{\\mathsf{ANF}}}\\;x = b; P) \\\\
  (\\ensuremath{\\mathsf{let}}\_{\\ensuremath{\\mathsf{ANF}}}\\;x = (a, b); P) &:= (\\ensuremath{\\mathsf{let}}\_{\\ensuremath{\\mathsf{ANF}}}\\;x\_a = a; \\ensuremath{\\mathsf{let}}\_{\\ensuremath{\\mathsf{ANF}}}\\;x\_b = b; \\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = (a, b);\\;P}) \\\\
  (\\ensuremath{\\mathsf{let}}\_{\\ensuremath{\\mathsf{ANF}}}\\;x = \\iota\_l\\;{a}; P) &:= (\\ensuremath{\\mathsf{let}}\_{\\ensuremath{\\mathsf{ANF}}}\\;x\_a = a; \\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = \\iota\_l\\;{x\_a};\\;P}) \\\\
  (\\ensuremath{\\mathsf{let}}\_{\\ensuremath{\\mathsf{ANF}}}\\;x = \\iota\_r\\;{a}; P) &:= (\\ensuremath{\\mathsf{let}}\_{\\ensuremath{\\mathsf{ANF}}}\\;x\_a = a; \\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = \\iota\_r\\;{x\_a};\\;P}) \\\\
  (\\ensuremath{\\mathsf{let}}\_{\\ensuremath{\\mathsf{ANF}}}\\;x = \\ensuremath{\\mathsf{case}}\\;e\\;\\{\\iota\_l\\;{y} :a, \\iota\_r\\;{z} :b\\}; P) 
    &:= (\\ensuremath{\\mathsf{let}}\_{\\ensuremath{\\mathsf{ANF}}}\\;x\_e = e; \\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = \\ensuremath{\\mathsf{case}}\\;x\_e \\\\ & \\qquad\\;\\{\\iota\_l\\;{y} :\\ensuremath{\\mathsf{ANF}}(a), \\iota\_r\\;{z} :\\ensuremath{\\mathsf{ANF}}(b)\\};\\;P}) \\\\
  (\\ensuremath{\\mathsf{let}}\_{\\ensuremath{\\mathsf{ANF}}}\\;x = \\ensuremath{\\mathsf{abort}}\\;{a}; P) &:= (\\ensuremath{\\mathsf{let}}\_{\\ensuremath{\\mathsf{ANF}}}\\;x\_a = a; \\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = \\ensuremath{\\mathsf{abort}}\\;{x\_a};\\;P}) \\\\
  (\\ensuremath{\\mathsf{let}}\_{\\ensuremath{\\mathsf{ANF}}}\\;x = \\ensuremath{\\mathsf{iter}}\\;a\\;\\{ \\iota\_r\\;{y} :b \\}; P) 
    &:= (\\ensuremath{\\mathsf{let}}\_{\\ensuremath{\\mathsf{ANF}}}\\;x\_a = a; \\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = \\ensuremath{\\mathsf{iter}}\\;x\_a\\;\\{ \\iota\_r\\;{y} :\\ensuremath{\\mathsf{ANF}}(b) \\};\\;P})
\\end{aligned}\$\$ We can trivially verify each case by simply applying
the binding rule for each term-former, followed by the inductive
hypothesis. For example, we have that
$ Gamma^(upright(bold(q))) & tack.r_tack.t sans(l e t) #h(0em) x = sans(i t e r) #h(0em) a #h(0em) { iota_r #h(0em) y : b } ; #h(0em) P approx sans(l e t) #h(0em) x = \( sans(l e t) #h(0em) x_a = a ; #h(0em) sans(i t e r) #h(0em) x_a #h(0em) { iota_r #h(0em) y : b } \) ; #h(0em) P & \( sans("iter-bind") \)\
 & approx sans(l e t) #h(0em) x_a = a ; #h(0em) sans(l e t) #h(0em) x = sans(i t e r) #h(0em) x_a #h(0em) { iota_r #h(0em) y : b } ; #h(0em) P & \( sans("let-let") ""_1 \)\
 & approx sans(l e t)_(sans(A N F)) #h(0em) x_a = a ; sans(l e t) #h(0em) x = sans(i t e r) #h(0em) x_a #h(0em) { iota_r #h(0em) y : b } ; #h(0em) P & \( upright("by induction") \)\
 & approx sans(l e t)_(sans(A N F)) #h(0em) x_a = a ; sans(l e t) #h(0em) x = sans(i t e r) #h(0em) x_a #h(0em) { iota_r #h(0em) y : sans(A N F) \( b \) } ; #h(0em) P & \( upright("by induction") \)\
 & approx sans(l e t)_(sans(A N F)) #h(0em) x = sans(i t e r) #h(0em) a #h(0em) { iota_r #h(0em) y : b } ; P & \( upright("by definition") \) $

#figure([#block[
  \<$I \, J$\> ::= $o$ |
  $sans(c a s e) #h(0em) o #h(0em) { iota_l #h(0em) x : P \, iota_r #h(0em) y : Q }$
  | $sans(i t e r) #h(0em) o #h(0em) { iota_r #h(0em) x : P }$

  \<$P \, Q \, R$\> ::= $o$ | $sans(l e t) #h(0em) x = I ; #h(0em) P$ |
  $sans(l e t) #h(0em) \( x \, y \) = o ; #h(0em) P$

  \<$q$\> ::= $0$ | $1$ | $omega^(+)$ | $1^(?)$ | $omega$

  \<$Gamma$\> ::= $dot.op$ | $Gamma \, x : A$

  \<$upright(bold(q))$\> ::= $dot.op$ | $upright(bold(q)) \, q$

  ]],
  caption: [
    Syntax for $lambda_(sans(i t e r))$ terms in ANF
  ]
)
<refall:fig:anf-syntax>

== ANF to SSA
<refall:anf-to-ssa>
We begin by stating a few metatheoretic results:

#block[
Given a label-weakening
$Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))')$,

- If
  $Gamma tack.r sans(L)'^(upright(bold(Q))') arrow.r.squiggly sans(L)''^(upright(bold(Q))'')$,
  then
  $Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)''^(upright(bold(Q))'')$
  with
  $ ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)''^(upright(bold(Q))'') ⟧ = ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧ ; ⟦ l w k Gamma sans(L)'^(upright(bold(Q))') sans(L)''^(upright(bold(Q))'') ⟧ $

- If
  $Gamma^(upright(bold(q))) tack.r_epsilon.alt s gt.tri sans(L)^(upright(bold(Q)))$
  and , we have that
  $Gamma^(upright(bold(q))) tack.r_epsilon.alt s gt.tri sans(L)'^(upright(bold(Q))')$
  with
  $ ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt s gt.tri sans(L)'^(upright(bold(Q))') ⟧ = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt s gt.tri sans(L)^(upright(bold(Q))) ⟧ ; ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧ $

]
#block[
#emph[Proof.] We begin by noting that, via a straightforward induction,
we have that
$ ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)''^(upright(bold(Q))'') ⟧ = ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧ ; ⟦ l w k Gamma sans(L)'^(upright(bold(Q))') sans(L)''^(upright(bold(Q))'') ⟧ $
and
$ ⟦ Gamma \, x : A tack.r sans(L)^(upright(bold(Q))^arrow.t) arrow.r.squiggly sans(L)'^(upright(bold(Q))'^arrow.t) ⟧ ; alpha^arrow.b = alpha^arrow.b ; ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧ $
We now proceed by induction on the derivation of
$Gamma^(upright(bold(q))) tack.r_epsilon.alt s gt.tri sans(L)^(upright(bold(Q)))$:

- ($Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(b r) #h(0em) ell #h(0em) a gt.tri sans(L)^(upright(bold(Q)))$):
  we have
  $  & ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(b r) #h(0em) ell #h(0em) a gt.tri sans(L)'^(upright(bold(Q))') ⟧\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ; ⟦ Gamma^(upright(bold(q))_l) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_r) tack.r_epsilon.alt a : A ⟧ ; iota_r ; ⟦ Gamma tack.r ell \( A \)^(upright(bold(q))_l) arrow.r.squiggly sans(L)'^(upright(bold(q'))) ⟧\
   & approx ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ; ⟦ Gamma^(upright(bold(q))_l) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_r) tack.r_epsilon.alt a : A ⟧ ; iota_r ; ⟦ Gamma tack.r ell \( A \)^(upright(bold(q))_l) arrow.r.squiggly sans(L)^(upright(bold(q))) ⟧ ; ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧\
   & approx ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(b r) #h(0em) ell #h(0em) a gt.tri sans(L)^(upright(bold(Q))) ⟧ ; ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧ $

- ($Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(l e t) #h(0em) x = o ; t gt.tri sans(L)^(upright(bold(Q)))$):
  we have by induction that
  $  & ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(l e t) #h(0em) x = o ; t gt.tri sans(L)'^(upright(bold(Q))') ⟧\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ; ⟦ Gamma^(upright(bold(q))_l) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_r) tack.r_epsilon.alt o : A ⟧ ; ⟦ Gamma^(upright(bold(q))_l) \, x : A tack.r_epsilon.alt t gt.tri sans(L)'^(upright(bold(Q))') ⟧\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ; ⟦ Gamma^(upright(bold(q))_l) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_r) tack.r_epsilon.alt o : A ⟧ ; ⟦ Gamma^(upright(bold(q))_l) \, x : A tack.r_epsilon.alt t gt.tri sans(L)^(upright(bold(Q))) ⟧ ; ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧\
   & = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(l e t) #h(0em) x = o ; t gt.tri sans(L)^(upright(bold(Q))) ⟧ ; ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧ $

- ($Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(l e t) #h(0em) \( x \, y \) = o ; t gt.tri sans(L)^(upright(bold(Q)))$):
  we have by induction that
  $  & ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(l e t) #h(0em) x = o ; t gt.tri sans(L)'^(upright(bold(Q))') ⟧\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ; ⟦ Gamma^(upright(bold(q))_l) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_r) tack.r_epsilon.alt o : A ⊗ B ⟧ ; alpha ; ⟦ Gamma^(upright(bold(q))_l) \, x : A \, y : B tack.r_epsilon.alt t gt.tri sans(L)'^(upright(bold(Q))') ⟧\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ; ⟦ Gamma^(upright(bold(q))_l) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_r) tack.r_epsilon.alt o : A ⊗ B ⟧ ; alpha ; ⟦ Gamma^(upright(bold(q))_l) \, x : A \, y : B tack.r_epsilon.alt t gt.tri sans(L)^(upright(bold(Q))) ⟧ ; ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧\
   & = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(l e t) #h(0em) \( x \, y \) = o ; t gt.tri sans(L)^(upright(bold(Q))) ⟧ ; ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧ $

- ($Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(c a s e) #h(0em) o #h(0em) { iota_l #h(0em) x : tau_l \, iota_r #h(0em) y : tau_r } gt.tri sans(L)^(upright(bold(Q)))$):
  we have by induction that
  $  & ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(c a s e) #h(0em) o #h(0em) { iota_l #h(0em) x : tau_l \, iota_r #h(0em) y : tau_r } gt.tri sans(L)'^(upright(bold(Q))') ⟧\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ; ⟦ Gamma^(upright(bold(q))_l) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_r) tack.r_epsilon.alt o : A + B ⟧ ;\
   & #h(2em) \[ ⟦ Gamma^(upright(bold(q))_l) \, x : A tack.r_epsilon.alt tau_l : sans(L)'^(upright(bold(Q))'^arrow.t) ⟧ ; alpha^arrow.b \, ⟦ Gamma^(upright(bold(q))_l) \, y : B tack.r_epsilon.alt tau_r : sans(L)'^(upright(bold(Q))'^arrow.t) ⟧ ; alpha^arrow.b \]\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ; ⟦ Gamma^(upright(bold(q))_l) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_r) tack.r_epsilon.alt o : A + B ⟧ ; \[\
   & #h(2em) ⟦ Gamma^(upright(bold(q))_l) \, x : A tack.r_epsilon.alt tau_l : sans(L)^(upright(bold(Q))^arrow.t) ⟧ ; ⟦ Gamma \, x : A tack.r sans(L)^(upright(bold(Q))^arrow.t) arrow.r.squiggly sans(L)'^(upright(bold(Q))'^arrow.t) ⟧ ; alpha^arrow.b \,\
   & #h(2em) ⟦ Gamma^(upright(bold(q))_l) \, y : B tack.r_epsilon.alt tau_r : sans(L)^(upright(bold(Q))^arrow.t) ⟧ ; ⟦ Gamma \, y : B tack.r sans(L)^(upright(bold(Q))^arrow.t) arrow.r.squiggly sans(L)'^(upright(bold(Q))'^arrow.t) ⟧ ; alpha^arrow.b \]\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r ⟧ ; ⟦ Gamma^(upright(bold(q))_l) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_r) tack.r_epsilon.alt o : A + B ⟧ ; \[\
   & #h(2em) ⟦ Gamma^(upright(bold(q))_l) \, x : A tack.r_epsilon.alt tau_l : sans(L)^(upright(bold(Q))^arrow.t) ⟧ ; alpha^arrow.b ; ⟦ Gamma tack.r sans(L)^(upright(bold(Q))^arrow.t) arrow.r.squiggly sans(L)^(upright(bold(Q))'^arrow.t) ⟧ \, ⟦ Gamma^(upright(bold(q))_l) \, y : B tack.r_epsilon.alt tau_r : sans(L)^(upright(bold(Q))^arrow.t) ⟧ ; alpha^arrow.b ; ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧ \]\
   & = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(c a s e) #h(0em) o #h(0em) { iota_l #h(0em) x : tau_l \, iota_r #h(0em) y : tau_r } gt.tri sans(L)^(upright(bold(Q))) ⟧ ; ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧ $

- ($Gamma^(upright(bold(q))) tack.r_epsilon.alt kappa #h(0em) sans(w h e r e)_(sans(n o n r e c)) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i gt.tri sans(L)^(upright(bold(Q)))$):
  we have
  $  & ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt kappa #h(0em) sans(w h e r e)_(sans(n o n r e c)) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i gt.tri sans(L)'^(upright(bold(Q))') ⟧\
   & = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt kappa gt.tri sans(L)'^(upright(bold(Q))') \, sans(R)^(upright(bold(Q))'') ⟧ ; alpha^(+) ; \[ sans(i d)_(⟦ \[ Gamma mapsto sans(L)'^(upright(bold(Q))') \] ⟧) \, \[ ⟦ Gamma^(upright(bold(q))_i) \, x_i : A_i tack.r_epsilon.alt t_i : sans(L)'^(upright(bold(Q))'^arrow.t) ⟧ ; alpha^arrow.b \, \]_(ell_i \( A_i \)^(upright(bold(q))_i) in sans(R)^(upright(bold(Q))'')) \]\
   & = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt kappa gt.tri sans(L)'^(upright(bold(Q))') \, sans(R)^(upright(bold(Q))'') ⟧ ; ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) \, sans(R)^(upright(bold(Q))'') arrow.r.squiggly sans(L)'^(upright(bold(Q))') \, sans(R)^(upright(bold(Q))'') ⟧ ; alpha^(+) ;\
   & #h(2em) \[ sans(i d)_(⟦ \[ Gamma mapsto sans(L)'^(upright(bold(Q))') \] ⟧) \, \[ ⟦ Gamma^(upright(bold(q))_i) \, x_i : A_i tack.r_epsilon.alt t_i : sans(L)^(upright(bold(Q))^arrow.t) ⟧ ; ⟦ Gamma \, x_i : A_i tack.r sans(L)^(upright(bold(Q))^arrow.t) arrow.r.squiggly sans(L)'^(upright(bold(Q))'^arrow.t) ⟧ ; alpha^arrow.b \, \]_(ell_i \( A_i \)^(upright(bold(q))_i) in sans(R)^(upright(bold(Q))'')) \]\
   & = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt kappa gt.tri sans(L)'^(upright(bold(Q))') \, sans(R)^(upright(bold(Q))'') ⟧ ; alpha^(+) ; ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧ + ⟦ \[ Gamma mapsto sans(R)^(upright(bold(Q))'') \] ⟧ ;\
   & #h(2em) \[ sans(i d)_(⟦ \[ Gamma mapsto sans(L)'^(upright(bold(Q))') \] ⟧) \, \[ ⟦ Gamma^(upright(bold(q))_i) \, x_i : A_i tack.r_epsilon.alt t_i : sans(L)^(upright(bold(Q))^arrow.t) ⟧ ; alpha^arrow.b ; ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧ \, \]_(ell_i \( A_i \)^(upright(bold(q))_i) in sans(R)^(upright(bold(Q))'')) \]\
   & = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt kappa gt.tri sans(L)'^(upright(bold(Q))') \, sans(R)^(upright(bold(Q))'') ⟧ ; alpha^(+) ;\
   & #h(2em) \[ ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧ \, \[ ⟦ Gamma^(upright(bold(q))_i) \, x_i : A_i tack.r_epsilon.alt t_i : sans(L)^(upright(bold(Q))^arrow.t) ⟧ ; alpha^arrow.b \, \]_(ell_i \( A_i \)^(upright(bold(q))_i) in sans(R)^(upright(bold(Q))'')) ; ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧ \]\
   & = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt kappa gt.tri sans(L)'^(upright(bold(Q))') \, sans(R)^(upright(bold(Q))'') ⟧ ; alpha^(+) ; \[ ⟦ sans(i d) \, \[ ⟦ Gamma^(upright(bold(q))_i) \, x_i : A_i tack.r_epsilon.alt t_i : sans(L)^(upright(bold(Q))^arrow.t) ⟧ ; alpha^arrow.b \, \]_(ell_i \( A_i \)^(upright(bold(q))_i) in sans(R)^(upright(bold(Q))'')) \] ; Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧\
   & = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt kappa #h(0em) sans(w h e r e)_(sans(n o n r e c)) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i gt.tri sans(L)^(upright(bold(Q))) ⟧ ; ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧ $
  as desired.

- ($Gamma^(upright(bold(q))) tack.r_epsilon.alt kappa #h(0em) sans(w h e r e)_(sans(r e c)) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i gt.tri sans(L)^(upright(bold(Q)))$):
  we have
  $  & ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt kappa #h(0em) sans(w h e r e)_(sans(r e c)) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i gt.tri sans(L)'^(upright(bold(Q))') ⟧\
   & = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt kappa gt.tri sans(L)'^(upright(bold(Q))') \, sans(R)^(upright(bold(Q))'') ⟧ ; alpha^(+) ; \[ sans(i d)_(⟦ \[ Gamma mapsto sans(L)'^(upright(bold(Q))') \] ⟧) \, \[ ⟦ Gamma^(upright(bold(q))_i) \, x_i : A_i tack.r_epsilon.alt t_i : sans(L)'^(upright(bold(Q))'^arrow.t) \, sans(R)^(upright(bold(Q))''^arrow.t) ⟧ ; alpha^arrow.b ; alpha^(+) \, \]_(ell_i \( A_i \)^(upright(bold(q))_i) in sans(R)^(upright(bold(Q))'))^dagger \]\
   & = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt kappa gt.tri sans(L)'^(upright(bold(Q))') \, sans(R)^(upright(bold(Q))'') ⟧ ; ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) \, sans(R)^(upright(bold(Q))'') arrow.r.squiggly sans(L)'^(upright(bold(Q))') \, sans(R)^(upright(bold(Q))'') ⟧ ; alpha^(+) ;\
   & #h(2em) \[ sans(i d)_(⟦ \[ Gamma mapsto sans(L)'^(upright(bold(Q))') \] ⟧) \, \[ ⟦ Gamma^(upright(bold(q))_i) \, x_i : A_i tack.r_epsilon.alt t_i : sans(L)^(upright(bold(Q))^arrow.t) \, sans(R)^(upright(bold(Q))''^arrow.t) ⟧ ; ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) \, sans(R)^(upright(bold(Q))'') arrow.r.squiggly sans(L)'^(upright(bold(Q))') \, sans(R)^(upright(bold(Q))'') ⟧ ; alpha^arrow.b ; alpha^(+) \, \]_(ell_i \( A_i \)^(upright(bold(q))_i) in sans(R)^(upright(bold(Q))'))^dagger \]\
   & = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt kappa gt.tri sans(L)'^(upright(bold(Q))') \, sans(R)^(upright(bold(Q))'') ⟧ ; ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) \, sans(R)^(upright(bold(Q))'') arrow.r.squiggly sans(L)'^(upright(bold(Q))') \, sans(R)^(upright(bold(Q))'') ⟧ ; alpha^(+) ;\
   & #h(2em) \[ sans(i d)_(⟦ \[ Gamma mapsto sans(L)'^(upright(bold(Q))') \] ⟧) \, \[ ⟦ Gamma^(upright(bold(q))_i) \, x_i : A_i tack.r_epsilon.alt t_i : sans(L)^(upright(bold(Q))^arrow.t) \, sans(R)^(upright(bold(Q))''^arrow.t) ⟧ ; ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) \, sans(R)^(upright(bold(Q))'') arrow.r.squiggly sans(L)'^(upright(bold(Q))') \, sans(R)^(upright(bold(Q))'') ⟧ ; alpha^arrow.b ; alpha^(+) \, \]_(ell_i \( A_i \)^(upright(bold(q))_i) in sans(R)^(upright(bold(Q))'))^dagger \]\
   & = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt kappa gt.tri sans(L)'^(upright(bold(Q))') \, sans(R)^(upright(bold(Q))'') ⟧ ; alpha^(+) ; ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧ + ⟦ \[ Gamma mapsto sans(R)^(upright(bold(Q))'') \] ⟧ ; \[ sans(i d)_(⟦ \[ Gamma mapsto sans(L)'^(upright(bold(Q))') \] ⟧) \,\
   & #h(2em) \[ ⟦ Gamma^(upright(bold(q))_i) \, x_i : A_i tack.r_epsilon.alt t_i : sans(L)^(upright(bold(Q))^arrow.t) \, sans(R)^(upright(bold(Q))''^arrow.t) ⟧ ; alpha^arrow.b ; alpha^(+) \, ; ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧ + ⟦ \[ Gamma mapsto sans(R)^(upright(bold(Q))'') \] ⟧ \]_(ell_i \( A_i \)^(upright(bold(q))_i) in sans(R)^(upright(bold(Q))'))^dagger \]\
   & = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt kappa gt.tri sans(L)'^(upright(bold(Q))') \, sans(R)^(upright(bold(Q))'') ⟧ ; alpha^(+) ; \[ ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧ \,\
   & #h(2em) \( \[ ⟦ Gamma^(upright(bold(q))_i) \, x_i : A_i tack.r_epsilon.alt t_i : sans(L)^(upright(bold(Q))^arrow.t) \, sans(R)^(upright(bold(Q))''^arrow.t) ⟧ ; alpha^arrow.b ; alpha^(+) \, \]_(ell_i \( A_i \)^(upright(bold(q))_i) in sans(R)^(upright(bold(Q))')) ; ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧ + ⟦ \[ Gamma mapsto sans(R)^(upright(bold(Q))'') \] ⟧ \)^dagger \]\
   & = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt kappa gt.tri sans(L)'^(upright(bold(Q))') \, sans(R)^(upright(bold(Q))'') ⟧ ; alpha^(+) ; \[ ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧ \,\
   & #h(2em) \[ ⟦ Gamma^(upright(bold(q))_i) \, x_i : A_i tack.r_epsilon.alt t_i : sans(L)^(upright(bold(Q))^arrow.t) \, sans(R)^(upright(bold(Q))''^arrow.t) ⟧ ; alpha^arrow.b ; alpha^(+) \, \]_(ell_i \( A_i \)^(upright(bold(q))_i) in sans(R)^(upright(bold(Q))'))^dagger ; ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧ \]\
   & = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt kappa gt.tri sans(L)'^(upright(bold(Q))') \, sans(R)^(upright(bold(Q))'') ⟧ ; alpha^(+) ; \[ sans(i d) \, \[ ⟦ Gamma^(upright(bold(q))_i) \, x_i : A_i tack.r_epsilon.alt t_i : sans(L)^(upright(bold(Q))^arrow.t) \, sans(R)^(upright(bold(Q))''^arrow.t) ⟧ ; alpha^arrow.b ; alpha^(+) \, \]_(ell_i \( A_i \)^(upright(bold(q))_i) in sans(R)^(upright(bold(Q))'))^dagger \] ;\
   & #h(2em) ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧\
   & = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt kappa #h(0em) sans(w h e r e)_(sans(r e c)) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i gt.tri sans(L)^(upright(bold(Q))) ⟧ ; ⟦ Gamma tack.r sans(L)^(upright(bold(Q))) arrow.r.squiggly sans(L)'^(upright(bold(Q))') ⟧ $
  as desired.

~◻

]
We may now define $sans(S S A)_ell \( P \)$ by induction on ANF programs
$P$ as follows:

- (Valid operations $o$): we define
  $\( sans(S S A)_ell \( o \) \) := sans(b r) #h(0em) ell #h(0em) o$.
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
  This has the desired semantics, since \$\$\\begin{aligned}
      \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} \\ensuremath{\\mathsf{br}}\\;\\ell\\;o \\rhd \\ell(A)^{\\ensuremath{\\mathbf{0}}}}\\rrbracket
      & = \\llbracket{\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}\\rrbracket 
        ; \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_r}}\\rrbracket \\otimes \\llbracket{\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} o: {A}}\\rrbracket 
        ; \\iota\_r
        ; \\cancel{\\llbracket{\\Gamma \\vdash \\ell(A)^{\\ensuremath{\\mathbf{q}}\_l} \\rightsquigarrow \\ell(A)^{\\ensuremath{\\mathbf{q}}\_l}}\\rrbracket}
    
  \\end{aligned}\$\$

- ($sans(l e t) #h(0em) x = o ; #h(0em) P$): we define
  $\( sans(S S A)_ell \( sans(l e t) #h(0em) x = o ; #h(0em) P \) \) := sans(l e t) #h(0em) x = o ; sans(S S A)_ell \( P \)$;
  we verify this has the correct semantics by induction as follows:
  $  & ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(S S A)_ell \( sans(l e t) #h(0em) x = o ; #h(0em) P \) gt.tri ell \( B \)^(upright(bold(q))_1) ⟧\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_12 + upright(bold(q))_3 ⟧ ; ⟦ Gamma^(upright(bold(q))_12) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_3) tack.r_epsilon.alt o : A ⟧ ; ⟦ Gamma^(upright(bold(q))_12) \, x : A tack.r_epsilon.alt sans(S S A)_ell \( P \) gt.tri ell \( B \)^(upright(bold(q))_1 \, 0) ⟧ ; alpha^arrow.b\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_12 + upright(bold(q))_3 ⟧ ; ⟦ Gamma^(upright(bold(q))_12) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_3) tack.r_epsilon.alt o : A ⟧ med ; ⟦ Gamma tack.r upright(bold(q))_12 \, x : A = upright(bold(q))_1 \, 0 + upright(bold(q))_2 \, omega ⟧\
   & quad ; \( ⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗ I \) ⊗ ⟦ Gamma^(upright(bold(q))_2) \, x : A tack.r_epsilon.alt P : B ⟧ ; iota_r ; alpha^arrow.b\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_12 + upright(bold(q))_3 ⟧ ; ⟦ Gamma tack.r upright(bold(q))_12 = upright(bold(q))_1 + upright(bold(q))_2 ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_3) tack.r_epsilon.alt o : A ⟧ ; alpha ; ⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_2) \, x : A tack.r_epsilon.alt P : B ⟧ ; iota_r\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_1 + upright(bold(q))_23 ⟧ ; ⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗ \( ⟦ Gamma tack.r upright(bold(q))_23 = upright(bold(q))_2 + upright(bold(q))_3 ⟧ ; ⟦ Gamma^(upright(bold(q))_3) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_3) tack.r_epsilon.alt o : A ⟧ ; ⟦ Gamma^(upright(bold(q))_2) \, x : A tack.r_epsilon.alt P : B ⟧ \) ; iota_r\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_1 + upright(bold(q))_23 ⟧ ; ⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗ \( ⟦ Gamma^(upright(bold(q))_23) tack.r_epsilon.alt sans(l e t) #h(0em) x = o ; #h(0em) P : B ⟧ \) ; iota_r $
  as desired.

- ($sans(l e t) #h(0em) \( x \, y \) = o ; #h(0em) P$): we define
  $\( sans(S S A)_ell \( sans(l e t) #h(0em) \( x \, y \) = o ; #h(0em) P \) \) := sans(l e t) #h(0em) \( x \, y \) = o ; sans(S S A)_ell \( P \)$;
  we verify this has the correct semantics by induction as follows:
  $  & ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(S S A)_ell \( sans(l e t) #h(0em) \( x \, y \) = o ; #h(0em) P \) gt.tri ell \( B \)^(upright(bold(q))_1) ⟧\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_12 + upright(bold(q))_3 ⟧ ; ⟦ Gamma^(upright(bold(q))_12) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_3) tack.r_epsilon.alt o : A ⊗ B ⟧ ; ⟦ Gamma^(upright(bold(q))_12) \, x : A \, y : B tack.r_epsilon.alt sans(S S A)_ell \( P \) gt.tri ell \( C \)^(upright(bold(q))_1 \, 0 \, 0) ⟧ ; alpha^arrow.b ; alpha^arrow.b\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_12 + upright(bold(q))_3 ⟧ ; ⟦ Gamma^(upright(bold(q))_12) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_3) tack.r_epsilon.alt o : A ⊗ B ⟧ med ; ⟦ Gamma tack.r upright(bold(q))_12 \, x : A \, y : B = upright(bold(q))_1 \, 0 \, 0 + upright(bold(q))_2 \, omega \, omega ⟧\
   & quad ; \( ⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗ I ⊗ I \) ⊗ ⟦ Gamma^(upright(bold(q))_2) \, x : A \, y : B tack.r_epsilon.alt P : C ⟧ ; iota_r ; alpha^arrow.b ; alpha^arrow.b\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_12 + upright(bold(q))_3 ⟧ ; ⟦ Gamma tack.r upright(bold(q))_12 = upright(bold(q))_1 + upright(bold(q))_2 ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_3) tack.r_epsilon.alt o : A ⊗ B ⟧ ; alpha\
   & quad ; ⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_2) \, x : A \, y : B tack.r_epsilon.alt P : C ⟧ ; iota_r\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_1 + upright(bold(q))_23 ⟧ ; ⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗\
   & #h(2em) \( ⟦ Gamma tack.r upright(bold(q))_23 = upright(bold(q))_2 + upright(bold(q))_3 ⟧ ; ⟦ Gamma^(upright(bold(q))_3) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_3) tack.r_epsilon.alt o : A ⊗ B ⟧ ; alpha ; ⟦ Gamma^(upright(bold(q))_2) \, x : A \, y : B tack.r_epsilon.alt P : C ⟧ \) ; iota_r\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_1 + upright(bold(q))_23 ⟧ ; ⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗ \( ⟦ Gamma^(upright(bold(q))_23) tack.r_epsilon.alt sans(l e t) #h(0em) x = o ; #h(0em) P : C ⟧ \) ; iota_r $

- ($Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(l e t) #h(0em) x = sans(c a s e) #h(0em) o #h(0em) { iota_l #h(0em) y : P \, iota_r #h(0em) z : Q } ; #h(0em) R : D$):
  we define
  $ \( sans(S S A)_ell \( sans(l e t) #h(0em) x = sans(c a s e) #h(0em) o #h(0em) { iota_l #h(0em) y : P \, iota_r #h(0em) z : Q } ; #h(0em) R \) \) & := \( sans(c a s e) #h(0em) o #h(0em) { iota_l #h(0em) y : sans(b r) #h(0em) ell_l #h(0em) y \, iota_r #h(0em) z : sans(b r) #h(0em) ell_r #h(0em) z }\
   & #h(2em) #h(0em) sans(w h e r e)_(sans(n o n r e c)) #h(0em)\
   & quad #h(2em) ell_l \( y \) : { sans(S S A)_(ell_o) \( P \) } \,\
   & quad #h(2em) ell_r \( z \) : { sans(S S A)_(ell_o) \( Q \) } \)\
   & quad #h(0em) sans(w h e r e)_(sans(n o n r e c)) #h(0em)\
   & #h(2em) ell_o \( x \) : { sans(S S A)_ell \( R \) } $ We verify the
  semantics by induction as follows:
  $  & ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(S S A)_ell \( sans(l e t) #h(0em) x = sans(c a s e) #h(0em) o #h(0em) { iota_l #h(0em) y : P \, iota_r #h(0em) z : Q } ; #h(0em) R \) gt.tri ell \( D \)^(upright(bold(q))_1) ⟧\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_123 + upright(bold(q))_4 ⟧ ; ⟦ Gamma^(upright(bold(q))_123) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_4) tack.r_epsilon.alt o : A + B ⟧ ; delta^(- 1) ; \[\
   & quad #h(2em) ⟦ Gamma^(upright(bold(q))_123) \, y : A tack.r_epsilon.alt sans(b r) #h(0em) ell_l #h(0em) y gt.tri ell \( D \)^(upright(bold(q))_1 \, 0) \, ell_o \( C \)^(upright(bold(q))_12 \, 0) \, ell_l \( A \)^(upright(bold(q))_123 \, 0) \, ell_r \( B \)^(upright(bold(q))_123 \, 0) ⟧ ; alpha^arrow.b \,\
   & quad #h(2em) ⟦ Gamma^(upright(bold(q))_123) \, z : B tack.r_epsilon.alt sans(b r) #h(0em) ell_r #h(0em) z gt.tri ell \( D \)^(upright(bold(q))_1 \, 0) \, ell_o \( C \)^(upright(bold(q))_12 \, 0) \, ell_l \( A \)^(upright(bold(q))_123 \, 0) \, ell_r \( B \)^(upright(bold(q))_123 \, 0) ⟧ ; alpha^arrow.b\
   & quad \] ; \[ sans(i d) \,\
   & #h(2em) ⟦ Gamma^(upright(bold(q))_123) \, y : A tack.r_epsilon.alt sans(S S A)_(ell_o) \( P \) gt.tri ell \( D \)^(upright(bold(q))_1 \, 0) \, ell_o \( C \)^(upright(bold(q))_12 \, 0) ⟧ ; alpha^arrow.b \,\
   & #h(2em) ⟦ Gamma^(upright(bold(q))_123) \, z : B tack.r_epsilon.alt sans(S S A)_(ell_o) \( Q \) gt.tri ell \( D \)^(upright(bold(q))_1 \, 0) \, ell_o \( C \)^(upright(bold(q))_12 \, 0) ⟧ ; alpha^arrow.b\
   & quad \] ; \[ sans(i d) \, ⟦ Gamma^(upright(bold(q))_12) \, x : C tack.r_epsilon.alt sans(S S A)_ell \( R \) gt.tri ell \( D \)^(upright(bold(q))_1 \, 0) ⟧ ; alpha^arrow.b \]\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_123 + upright(bold(q))_4 ⟧ ; ⟦ Gamma^(upright(bold(q))_123) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_4) tack.r_epsilon.alt o : A + B ⟧ ; delta^(- 1) ; \[ iota_l ; iota_r \, iota_r \] ; \[ sans(i d) \,\
   & #h(2em) ⟦ Gamma^(upright(bold(q))_123) \, y : A tack.r_epsilon.alt sans(S S A)_(ell_o) \( P \) gt.tri ell_o \( C \)^(upright(bold(q))_12 \, 0) ⟧ ; ⟦ Gamma tack.r ell_o \( C \)^(upright(bold(q))_12 \, 0) arrow.r.squiggly ell \( D \)^(upright(bold(q))_1 \, 0) \, ell_o \( C \)^(upright(bold(q))_12 \, 0) ⟧ ; alpha^arrow.b \,\
   & #h(2em) ⟦ Gamma^(upright(bold(q))_123) \, z : B tack.r_epsilon.alt sans(S S A)_(ell_o) \( Q \) gt.tri ell_o \( C \)^(upright(bold(q))_12 \, 0) ⟧ ; ⟦ Gamma tack.r ell_o \( C \)^(upright(bold(q))_12 \, 0) arrow.r.squiggly ell \( D \)^(upright(bold(q))_1 \, 0) \, ell_o \( C \)^(upright(bold(q))_12 \, 0) ⟧ ; alpha^arrow.b\
   & quad \] ; \[ sans(i d) \, ⟦ Gamma^(upright(bold(q))_12) \, x : C tack.r upright(bold(q))_1 \, omega = upright(bold(q))_1 \, 0 + upright(bold(q))_2 \, omega ⟧ ; \( ⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗ I \) ⊗ ⟦ Gamma^(upright(bold(q))_2) \, x : C tack.r_epsilon.alt R : D ⟧ ; iota_r ; alpha^arrow.b \]\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_123 + upright(bold(q))_4 ⟧ ; ⟦ Gamma^(upright(bold(q))_123) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_4) tack.r_epsilon.alt o : A + B ⟧ ; delta^(- 1) ; \[\
   & #h(2em) ⟦ Gamma \, y : A tack.r upright(bold(q))_123 \, omega = upright(bold(q))_12 \, 0 + upright(bold(q))_3 \, omega ⟧ ; \( ⟦ Gamma^(upright(bold(q))_12) ⟧ ⊗ I \) ⊗ ⟦ Gamma^(upright(bold(q))_3) \, y : A tack.r_epsilon.alt P : C ⟧ ; iota_r ; alpha^arrow.b \,\
   & #h(2em) ⟦ Gamma \, z : B tack.r upright(bold(q))_123 \, omega = upright(bold(q))_12 \, 0 + upright(bold(q))_3 \, omega ⟧ ; \( ⟦ Gamma^(upright(bold(q))_12) ⟧ ⊗ I \) ⊗ ⟦ Gamma^(upright(bold(q))_3) \, z : B tack.r_epsilon.alt Q : C ⟧ ; iota_r ; alpha^arrow.b\
   & quad \] ; \[ sans(i d) \, ⟦ Gamma tack.r upright(bold(q))_12 = upright(bold(q))_1 + upright(bold(q))_2 ⟧ ⊗ ⟦ C ⟧ ; alpha ; ⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_2) \, x : C tack.r_epsilon.alt R : D ⟧ ; iota_r \]\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_123 + upright(bold(q))_4 ⟧ ; ⟦ Gamma^(upright(bold(q))_123) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_4) tack.r_epsilon.alt o : A + B ⟧ ; delta^(- 1) ; \[\
   & #h(2em) ⟦ Gamma tack.r upright(bold(q))_123 = upright(bold(q))_12 + upright(bold(q))_3 ⟧ ⊗ ⟦ A ⟧ ; alpha ; ⟦ Gamma^(upright(bold(q))_12) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_3) \, y : A tack.r_epsilon.alt P : C ⟧ \,\
   & #h(2em) ⟦ Gamma tack.r upright(bold(q))_123 = upright(bold(q))_12 + upright(bold(q))_3 ⟧ ⊗ ⟦ B ⟧ ; alpha ; ⟦ Gamma^(upright(bold(q))_12) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_3) \, z : B tack.r_epsilon.alt Q : C ⟧\
   & quad \] ; ⟦ Gamma tack.r upright(bold(q))_12 = upright(bold(q))_1 + upright(bold(q))_2 ⟧ ⊗ ⟦ C ⟧ ; alpha ; ⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_2) \, x : C tack.r_epsilon.alt R : D ⟧ ; iota_r\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_123 + upright(bold(q))_4 ⟧ ; ⟦ Gamma tack.r upright(bold(q))_123 = upright(bold(q))_12 + upright(bold(q))_3 ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_4) ⟧ ; alpha ; ⟦ Gamma^(upright(bold(q))_12) ⟧ ⊗ \(\
   & #h(2em) ⟦ Gamma^(upright(bold(q))_3) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_4) tack.r_epsilon.alt o : A + B ⟧ ; delta^(- 1) ; \[ ⟦ Gamma^(upright(bold(q))_3) \, y : A tack.r_epsilon.alt P : C ⟧ \, ⟦ Gamma^(upright(bold(q))_3) \, z : B tack.r_epsilon.alt Q : C ⟧\
   & quad \] \) ; ⟦ Gamma^(upright(bold(q))_12) tack.r upright(bold(q))_1 = upright(bold(q))_1 + upright(bold(q))_2 ⟧ ⊗ ⟦ C ⟧ ; alpha ; ⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_2) \, x : C tack.r_epsilon.alt R : D ⟧ ; iota_r\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_12 + upright(bold(q))_34 ⟧ ; ⟦ Gamma tack.r upright(bold(q))_12 = upright(bold(q))_1 + upright(bold(q))_2 ⟧ ⊗ \( ⟦ Gamma tack.r upright(bold(q))_34 = upright(bold(q))_3 + upright(bold(q))_4 ⟧ ; ⟦ Gamma^(upright(bold(q))_3) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_4) tack.r_epsilon.alt o : A + B ⟧ ;\
   & #h(2em) delta^(- 1) ; \[ ⟦ Gamma^(upright(bold(q))_3) \, y : A tack.r_epsilon.alt P : C ⟧ \, ⟦ Gamma^(upright(bold(q))_3) \, z : B tack.r_epsilon.alt Q : C ⟧ \] \) ; alpha ; ⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_2) \, x : C tack.r_epsilon.alt R : D ⟧ ; iota_r\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_1 + upright(bold(q))_234 ⟧ ; \( ⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗ \( ⟦ Gamma tack.r upright(bold(q))_234 = upright(bold(q))_2 + upright(bold(q))_34 ⟧ ;\
   & #h(2em) ⟦ Gamma^(upright(bold(q))_2) ⟧ ⊗ \( ⟦ Gamma^(upright(bold(q))_34) tack.r_epsilon.alt sans(c a s e) #h(0em) o #h(0em) { iota_l #h(0em) y : P \, iota_r #h(0em) z : Q } : C ⟧ ; ⟦ Gamma^(upright(bold(q))_2) \, x : C tack.r_epsilon.alt R : D ⟧ \) \) \) ; iota_r\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_1 + upright(bold(q))_234 ⟧ ; ⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_234) tack.r_epsilon.alt sans(l e t) #h(0em) x = sans(c a s e) #h(0em) o #h(0em) { iota_l #h(0em) y : P \, iota_r #h(0em) z : Q } ; #h(0em) R : D ⟧ ; iota_r $
  as desired.

- ($sans(l e t) #h(0em) x = sans(i t e r) #h(0em) o #h(0em) { iota_r #h(0em) x : P } ; #h(0em) Q$):
  $ \( sans(S S A)_ell \( sans(l e t) #h(0em) x = sans(i t e r) #h(0em) o #h(0em) { iota_r #h(0em) y : P } ; #h(0em) Q \) \) & := sans(b r) #h(0em) ell_b #h(0em) o #h(0em) sans(w h e r e)_(sans(r e c)) #h(0em)\
   & #h(2em) ell_b \( y \) : { sans(S S A)_(ell_h) \( P \) } \,\
   & #h(2em) ell_h \( w \) : { sans(c a s e) #h(0em) w #h(0em) { iota_l #h(0em) x : sans(b r) #h(0em) ell_o #h(0em) x \, iota_r #h(0em) y : sans(b r) #h(0em) ell_b #h(0em) y } } \,\
   & #h(2em) ell_o \( x \) : { sans(S S A)_ell \( Q \) } $ We verify the
  semantics by induction as follows, where
  $sans(R)^(upright(bold(Q))) := ell_r \( A \)^(upright(bold(q))_12) \, ell_h \( B + A \)^(upright(bold(q))_12) \, ell_o \( B \)^(upright(bold(q))_12)$:
  $  & ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(S S A)_ell \( sans(l e t) #h(0em) x = sans(i t e r) #h(0em) o #h(0em) { iota_r #h(0em) y : P } ; #h(0em) Q \) gt.tri ell \( C \)^(upright(bold(q))_1) ⟧\
   & = ⟦ Gamma^(upright(bold(q))) tack.r_epsilon.alt sans(b r) #h(0em) ell_r #h(0em) o gt.tri ell \( C \)^(upright(bold(q))_1) \, sans(R)^(upright(bold(Q))^arrow.t) ⟧ ; \[ sans(i d)_(⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗ ⟦ C ⟧) \, \[\
   & #h(2em) ⟦ Gamma^(upright(bold(q))_12) \, y : A tack.r_epsilon.alt sans(S S A)_(ell_h) \( P \) gt.tri ell \( C \)^(upright(bold(q))_1 \, 0) \, sans(R)^(upright(bold(Q))^arrow.t) ⟧ ; alpha^arrow.b ; alpha^(+) \,\
   & #h(2em) ⟦ Gamma^(upright(bold(q))_12) \, w : A + B tack.r_epsilon.alt sans(c a s e) #h(0em) w #h(0em) { iota_l #h(0em) x : sans(b r) #h(0em) ell_o #h(0em) x \, iota_r #h(0em) y : sans(b r) #h(0em) ell_b #h(0em) y } gt.tri ell \( C \)^(upright(bold(q))_1 \, 0) \, sans(R)^(upright(bold(Q))^arrow.t) ⟧ ; alpha^arrow.b ; alpha^(+) \,\
   & #h(2em) ⟦ Gamma^(upright(bold(q))_12) \, x : B tack.r_epsilon.alt sans(S S A)_ell \( Q \) gt.tri ell \( C \)^(upright(bold(q))_1 \, 0) \, sans(R)^(upright(bold(Q))^arrow.t) ⟧ ; alpha^arrow.b ; alpha^(+) \]^dagger \]\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_12 + upright(bold(q))_3 ⟧ ; ⟦ Gamma^(upright(bold(q))_12) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_3) tack.r_epsilon.alt o : A ⟧ ; iota_l ; iota_l ; iota_r ; \[ sans(i d)_(⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗ ⟦ C ⟧) \, \[\
   & #h(2em) ⟦ Gamma^(upright(bold(q))_12) \, y : A tack.r_epsilon.alt sans(S S A)_(ell_h) \( P \) gt.tri ell \( C \)^(upright(bold(q))_1 \, 0) \, sans(R)^(upright(bold(Q))) ⟧ ; alpha^arrow.b ; alpha^(+) \,\
   & #h(2em) delta^(- 1) ; \[ iota_r \, iota_r ; iota_l \] ; iota_r \,\
   & #h(2em) ⟦ Gamma^(upright(bold(q))_12) \, x : B tack.r_epsilon.alt sans(S S A)_ell \( Q \) gt.tri ell \( C \)^(upright(bold(q))_1 \, 0) \, sans(R)^(upright(bold(Q))^arrow.t) ⟧ ; alpha^arrow.b ; alpha^(+) \]^dagger \]\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_12 + upright(bold(q))_3 ⟧ ; ⟦ Gamma^(upright(bold(q))_12) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_3) tack.r_epsilon.alt o : A ⟧ ; iota_l ; iota_l ; \[\
   & #h(2em) ⟦ Gamma^(upright(bold(q))_12) \, y : A tack.r_epsilon.alt sans(S S A)_(ell_h) \( P \) gt.tri ell_h \( B + A \)^(upright(bold(q))_12 \, 0) ⟧ ; ⟦ Gamma tack.r ell_h \( B + A \)^(upright(bold(q))_12 \, 0) arrow.r.squiggly ell \( C \)^(upright(bold(q))_1 \, 0) \, sans(R)^(upright(bold(Q))^arrow.t) ⟧ ; alpha^arrow.b ; alpha^(+) \,\
   & #h(2em) delta^(- 1) ; \[ iota_r \, iota_r ; iota_l \] ; iota_r \,\
   & #h(2em) ⟦ Gamma^(upright(bold(q))_12) \, z : B tack.r_epsilon.alt sans(S S A)_(ell_h) \( Q \) gt.tri ell \( C \)^(upright(bold(q))_1 \, 0) ⟧ ; ⟦ Gamma tack.r ell \( C \)^(upright(bold(q))_1 \, 0) arrow.r.squiggly ell \( C \)^(upright(bold(q))_1 \, 0) \, sans(R)^(upright(bold(Q))^arrow.t) ⟧ ; alpha^arrow.b ; alpha^(+) \]^dagger\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_12 + upright(bold(q))_3 ⟧ ; ⟦ Gamma^(upright(bold(q))_12) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_3) tack.r_epsilon.alt o : A ⟧ ; iota_l ; iota_l ; \[\
   & #h(2em) ⟦ Gamma tack.r upright(bold(q))_12 = upright(bold(q))_12 + upright(bold(q))_r ⟧ ⊗ ⟦ A ⟧ ; alpha ; ⟦ Gamma^(upright(bold(q))_12) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_r) \, y : A tack.r_epsilon.alt P : B + A ⟧ ; iota_r ; iota_r \,\
   & #h(2em) delta^(- 1) ; \[ iota_r \, iota_r ; iota_l \] ; iota_r \,\
   & #h(2em) ⟦ Gamma tack.r upright(bold(q))_12 = upright(bold(q))_1 + upright(bold(q))_2 ⟧ ⊗ ⟦ B ⟧ ; alpha ; ⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_2) \, x : B tack.r_epsilon.alt Q : C ⟧ ; iota_r ; iota_l \]^dagger\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_12 + upright(bold(q))_3 ⟧ ; ⟦ Gamma^(upright(bold(q))_12) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_3) tack.r_epsilon.alt o : A ⟧ ; \(\
   & #h(2em) ⟦ Gamma tack.r upright(bold(q))_12 = upright(bold(q))_12 + upright(bold(q))_r ⟧ ⊗ ⟦ A ⟧ ; alpha ; ⟦ Gamma^(upright(bold(q))_12) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_r) \, y : A tack.r_epsilon.alt P : B + A ⟧ ; delta^(- 1) ;\
   & #h(2em) \( ⟦ Gamma tack.r upright(bold(q))_12 = upright(bold(q))_1 + upright(bold(q))_2 ⟧ ⊗ ⟦ B ⟧ ; alpha ; ⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_2) \, x : B tack.r_epsilon.alt Q : C ; iota_r ⟧ \) + \( ⟦ Gamma^(upright(bold(q))_12) ⟧ ⊗ ⟦ A ⟧ \) \)^dagger\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_12 + upright(bold(q))_3 ⟧ ; ⟦ Gamma^(upright(bold(q))_12) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_3) tack.r_epsilon.alt o : A ⟧ ; \(\
   & #h(2em) ⟦ Gamma tack.r upright(bold(q))_12 = upright(bold(q))_12 + upright(bold(q))_r ⟧ ⊗ ⟦ A ⟧ ; alpha ; ⟦ Gamma^(upright(bold(q))_12) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_r) \, y : A tack.r_epsilon.alt P : B + A ⟧ ; delta^(- 1)\
   & quad \)^dagger ; ⟦ Gamma tack.r upright(bold(q))_12 = upright(bold(q))_1 + upright(bold(q))_2 ⟧ ⊗ ⟦ B ⟧ ; alpha ; ⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_2) \, x : B tack.r_epsilon.alt Q : C ⟧ ; iota_r\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_12 + upright(bold(q))_3 ⟧ ; ⟦ Gamma tack.r upright(bold(q))_12 = upright(bold(q))_12 + upright(bold(q))_r ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_3) tack.r_epsilon.alt o : A ⟧ ; alpha ; \( ⟦ Gamma^(upright(bold(q))_12) ⟧ ⊗ \(\
   & #h(2em) ⟦ Gamma tack.r upright(bold(q))_r = upright(bold(q))_r + upright(bold(q))_r ⟧ ⊗ ⟦ A ⟧ ; alpha ; ⟦ Gamma^(upright(bold(q))_r) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_r) \, y : A tack.r_epsilon.alt P : B + A ⟧ ;\
   & #h(2em) delta^(- 1) ; \( ⟦ Gamma^(upright(bold(q))_r) mapsto dot.op ⟧ ⊗ ⟦ B ⟧ ; lambda \) + ⟦ Gamma^(upright(bold(q))_r) ⟧ ⊗ ⟦ A ⟧\
   & quad \)^dagger \) ; alpha ; ⟦ Gamma tack.r upright(bold(q))_12 = upright(bold(q))_1 + upright(bold(q))_2 ⟧ ⊗ ⟦ B ⟧ ; alpha ; ⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_2) \, x : B tack.r_epsilon.alt Q : C ⟧ ; iota_r\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_12 + upright(bold(q))_(3 r) ⟧ ; ⟦ Gamma tack.r upright(bold(q))_12 = upright(bold(q))_1 + upright(bold(q))_2 ⟧ ⊗ \( ⟦ Gamma tack.r upright(bold(q))_(3 r) = upright(bold(q))_r + upright(bold(q))_3 ⟧ ; ⟦ Gamma^(upright(bold(q))_r) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_3) tack.r_epsilon.alt o : A ⟧ ; \(\
   & #h(2em) ⟦ Gamma tack.r upright(bold(q))_r = upright(bold(q))_r + upright(bold(q))_r ⟧ ⊗ ⟦ A ⟧ ; alpha ; ⟦ Gamma^(upright(bold(q))_r) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_r) \, y : A tack.r_epsilon.alt P : B + A ⟧ \)^dagger ; ⟦ Gamma^(upright(bold(q))_r) mapsto dot.op ⟧ ⊗ ⟦ B ⟧ ; lambda\
   & quad \) ; alpha ; ⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_2) \, x : B tack.r_epsilon.alt Q : C ⟧ ; iota_r\
   $
  $  & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_12 + upright(bold(q))_(3 r) ⟧ ; ⟦ Gamma tack.r upright(bold(q))_12 = upright(bold(q))_1 + upright(bold(q))_2 ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_(3 r)) tack.r_epsilon.alt sans(i t e r) #h(0em) o #h(0em) { iota_r #h(0em) y : P } : B ⟧ ;\
   & quad alpha ; ⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_2) \, x : B tack.r_epsilon.alt Q : C ⟧ ; iota_r\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_12 + upright(bold(q))_(3 r) ⟧ ; ⟦ Gamma tack.r upright(bold(q))_12 = upright(bold(q))_1 + upright(bold(q))_2 ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_(3 r)) tack.r_epsilon.alt sans(i t e r) #h(0em) o #h(0em) { iota_r #h(0em) y : P } : B ⟧ ;\
   & quad alpha ; ⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_2) \, x : B tack.r_epsilon.alt Q : C ⟧ ; iota_r\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_1 + upright(bold(q))_(23 r) ⟧ ; ⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗ \(\
   & #h(2em) ⟦ Gamma tack.r upright(bold(q))_(23 r) = upright(bold(q))_2 + upright(bold(q))_(3 r) ⟧ ; ⟦ Gamma^(upright(bold(q))_2) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_(3 r)) tack.r_epsilon.alt sans(i t e r) #h(0em) o #h(0em) { iota_r #h(0em) y : P } : B ⟧ ; ⟦ Gamma^(upright(bold(q))_2) \, x : B tack.r_epsilon.alt Q : C ⟧ \) ; iota_r\
   & = ⟦ Gamma tack.r upright(bold(q)) = upright(bold(q))_1 + upright(bold(q))_(23 r) ⟧ ; ⟦ Gamma^(upright(bold(q))_1) ⟧ ⊗ ⟦ Gamma^(upright(bold(q))_(23 r)) tack.r_epsilon.alt sans(l e t) #h(0em) x = sans(i t e r) #h(0em) o #h(0em) { iota_r #h(0em) y : P } ; #h(0em) Q : C ⟧ ; iota_r $
  as desired.

= Models
<refall:apx:models>
In this section, we give a few simple families of
$lambda_(sans(i t e r))$-models highlighting some of the features of our
formalization.

== Poset-Enriched Elgot Monads
<refall:poset-enriched-elgot-monads>
A wide variety of $lambda_(sans(i t e r))$-models can be derived from
#emph[poset-enriched Elgot monads] over $upright(bold(S e t))$, which
are just standard monads equipped with a notion of refinement and
iteration. We begin by defining a #emph[poset-enriched monad] as
follows:

#block[
We say a monad $T$ over $upright(bold(S e t))$ is #emph[poset-enriched]
if each $T \( A \)$ is equipped with a partial order $arrow.r.twohead$
compatible with
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
\$\\cdot \\mathbin{\>\\!\\!\>\\mkern-6.7mu=}\_{T} \\cdot\$, i.e., such
that, for $a arrow.r.twohead b$ and $f arrow.r.twohead g$, we have
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
\$a \\mathbin{\>\\!\\!\>\\mkern-6.7mu=}\_{T} f \\twoheadrightarrow b \\mathbin{\>\\!\\!\>\\mkern-6.7mu=}\_{T} g\$,
where morphisms in the Kleisli category $f \, g : A arrow.r T \( B \)$
are given the pointwise partial order.

]
Note that, just like for poset-enriched categories, #emph[every] monad
is poset-enriched with the identity order on $T #h(0em) A$. Probably the
simplest nontrivial example of a poset-enriched monad is given by
adjoining a top element to every set as follows
$top \( A \) := A union { top }$, with pure and bind defined as for the
option monad; we can symmetrically instead adjoin a bottom element
$tack.t \( A \) := A union { tack.t }$. A more complex example is given
by the power-set monad $cal(P)$ equipped with the inclusion order, with
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
\$\$\\eta\_{\\ensuremath{\\mathcal{P}}}(a) := \\{a\\} \\qquad
  X \\mathbin{\>\\!\\!\>\\mkern-6.7mu=}\_{\\ensuremath{\\mathcal{P}}} f := \\bigcup\_{a \\in X}f(a)\$\$
This has numerous natural submonads which are also poset-enriched,
including:

- Nonempty sets $cal(P)^(+)$

- Finite sets $cal(P)_(sans(f i n))$

- Countable sets $cal(P)_(bb(N))$

- Sets of cardinality at most one, which is isomorphic to $tack.t$.

- Sets of cardinality exactly one, corresponding to pure morphisms.

It is easy to see that the Kleisli category of a poset-enriched monad is
always a poset-enriched distributive category; in particular, tensor
products and coproducts are simply given by the product and coproduct in
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
$upright(bold(S e t))$, with \$\$\\begin{gathered}
  f \\otimes A := (\\lambda (x, y) . f\\;x \\mathbin{\>\\!\\!\>\\mkern-6.7mu=}\_{} \\lambda z . (z, y)) \\qquad
  A \\otimes f := (\\lambda (x, y) . f\\;y \\mathbin{\>\\!\\!\>\\mkern-6.7mu=}\_{} \\lambda z . (x, z)) 
\\end{gathered}\$\$ and (inverse) associators, unitors, symmetries,
distributors, and injections given by the lifts of the underlying
morphisms in $upright(bold(S e t))$. We can always equip the Kleisli
category with the structure of a distributive effectful category with
pure morphisms
$ sans(S e t)_(T tack.t) \( A \, B \) := { eta_B compose f divides f : A arrow.r B } $
We can define $sans(S e t)_(T epsilon.alt)$ for other effects
$epsilon.alt in cal(E)$ in a given effect system as appropriate to the
effect system and monad; submonads are often a good place to look for
these.

We would now like to equip the Kleisli category of $T$ with an iteration
structure. The notion of an Elgot monad @goncharov-16-complete-elgot
generalizes directly to the poset-enriched setting:

#block[
We say a poset-enriched monad $T$ is a (strong) Elgot monad if its
Kleisli category is equipped with a monotone iteration operator
$\( dot.op \)^dagger$ satisfying the following properties:

- #emph[Naturality]: for $f : A arrow.r T \( B + A \)$ and
  $g : B arrow.r T \( C \)$, we have
  $\( f ; g + A \)^dagger = f^dagger ; g$

- #emph[Codiagonal]: for $f : A arrow.r T \( \( B + A \) + A \)$, we
  have $f^(dagger dagger) = \( f ; \[ sans(i d) \, iota_r \] \)^dagger$

- #emph[Directed uniformity]: given $f : A arrow.r T \( B + A \)$,
  $g : X arrow.r T \( B + X \)$, and #emph[pure] $h : X arrow.r A$, we
  have

  - $h^arrow.t #h(0em) f arrow.r.twohead g ; B + h^arrow.t arrow.r.double.long h^arrow.t ; f^dagger arrow.r.twohead g^dagger$

  - $h^arrow.t #h(0em) f arrow.l.twohead g ; B + h^arrow.t arrow.r.double.long h^arrow.t ; f^dagger arrow.l.twohead g^dagger$

  where $h^arrow.t = eta_A compose h : X arrow.r T \( A \)$.

#emph[Strengh]: given $f : A arrow.r T \( B + A \)$, we have
$X ⊗ f^dagger = \( X ⊗ f ; delta^(- 1) \)^dagger$

]
We can easily verify that the Kleisli category of a strong Elgot monad
is an Elgot category, which in particular is
$sans(S e t)_(T tack.t)$-uniform by uniformity. Probably the simplest
example of an Elgot monad is the power-set $cal(P)$, with
$ f^dagger := union.big_i f_i #h(2em) upright("where") #h(2em) f_0 = diameter #h(2em) f_(i + 1) = f ; \[ sans(i d) \, f_i \] $
Analysis of semantics in this monad corresponds to #emph[partial
correctness], with any infinite executions discarded. This isn't always
what we want, especially since every program can be safely refined to
(and hence "optimized to") the infinite loop
$0 := diameter : A arrow.r B$. Note for example that

- The pure effect is not closed under refinement, since any pure
  morphism can be refined to $0$

- The pure effect, as well as the effect of being finite and the effect
  of being nonempty, are #emph[not] iterative, but the effect of being
  countable and the effect of being deterministic but potentially
  nonterminating #emph[are].

== Undefined Behavior
<refall:apx:ub>
In this section, we demonstrate how to build a more complex
poset-enriched Elgot monad, by constructing a monad $sans(U B)$ which
supports

- #emph[Undefined behavior] (UB), represented as a top element
  $arrow.zigzag arrow.r.twohead a$ for all $a$.

- #emph[Nondeterministic behavior]

- #emph[Total correctness], with nontermination represented as a
  separate possible outcome $oo$ (allowing us to distinguish between a
  program which always terminates, never terminates, and is
  nondeterministically nonterminating)

As described in Section~@refall:ssec:ub, we define
$sans(U B) \( A \) := cal(P)^(+) \( A union { oo } \) union { arrow.zigzag }$,
with
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
\$\$\\lightning \\mathbin{\>\\!\\!\>\\mkern-6.7mu=}\_{\\ensuremath{\\mathsf{UB}}} f = \\lightning\\qquad
X \\mathbin{\>\\!\\!\>\\mkern-6.7mu=}\_{\\ensuremath{\\mathsf{UB}}} f = \\{f\\;a \\mid a \\in X\\} \\;\\; \\text{if } \\forall a \\in X, f\\;a \\neq \\lightning
\\qquad
X \\mathbin{\>\\!\\!\>\\mkern-6.7mu=}\_{\\ensuremath{\\mathsf{UB}}} f = \\lightning\\;\\; \\text{otherwise}\$\$
We can equip this with iteration structure $\( dot.op \)^dagger$ given
by, given $f : A arrow.r sans(U B) \( B + A \)$,
$ f^dagger \( a \) := cases(delim: "{", f_oo \( a \) union union.big_(i in bb(N)) f_i \( a \) & upright("if ") forall i \, f_i \( a \) eq.not arrow.zigzag, arrow.zigzag & upright("otherwise")) $
where
$ f_0 := diameter #h(2em) f_(i + 1) := f ; \[ sans(i d) \, f_i \] #h(2em) f_oo \( a_0 \) := cases(delim: "{", { oo } & upright("if ") exists a_i \, forall i \, a_(i + 1) in f \( a_i \), diameter & upright("otherwise")) $
Note that the $f_i$ are in the slightly larger monad
$A mapsto cal(P) \( A union { oo } \) union { arrow.zigzag }$; but it is
straightforward to show that $f^dagger$ must be nonempty and therefore
lie in the submonad $sans(U B)$ (since if all $f_i$ are empty,
$f_oo = { oo }$). It is straightforward to verify that this indeed gives
us an Elgot structure.

== Monad Transformers
<refall:apx:ub-st>
In functional programming, we often use a stack of #emph[monad
transformers] to build up complex effects from simple building blocks.
It turns out that many common monad transformers are compatible with
both poset-enrichment and Elgot structure; we give some important
examples below:

- The #emph[reader transformer]
  $sans(R d)_R #h(0em) T #h(0em) A := R arrow.r T #h(0em) A$ allows us
  to read from an environment $R$, with
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
  \$\$\\eta\_{\\ensuremath{\\mathsf{Rd}}\_R\\;T}\\;a := \\lambda r . \\eta\_T\\;a \\qquad
    a \\mathbin{\>\\!\\!\>\\mkern-6.7mu=}\_{\\ensuremath{\\mathsf{Rd}}\_R\\;T} f := \\lambda r. a\\;r \\mathbin{\>\\!\\!\>\\mkern-6.7mu=}\_{T} \\lambda a\' . f\\;a\'\\;r\$\$
  Given
  $f : A arrow.r sans(R d)_R #h(0em) T #h(0em) \( B + A \) = A arrow.r R arrow.r T \( B + A \)$,
  we define
  \$\$f^{\\dagger\_{\\ensuremath{\\mathsf{Rd}}\_R\\;T}} := \\lambda a, r . 
        ((\\lambda (r, a) . (r, f\\;a\\;r)) ; \\delta^{-1})^\\dagger(r, a) \\mathbin{\>\\!\\!\>\\mkern-6.7mu=}\_{T} \\pi\_2\$\$

- The #emph[writer transformer]
  $sans(W r)_W #h(0em) T #h(0em) A := T #h(0em) \( W times A \)$ for a
  monoid $\( W \, dot.op \, 1 \)$ allows us to write to a $W$-typed log,
  with
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
  \$\$\\eta\_{\\ensuremath{\\mathsf{Wr}}\_W\\;T}\\;a := \\eta\_T\\;(1, a) \\qquad
    a \\mathbin{\>\\!\\!\>\\mkern-6.7mu=}\_{\\ensuremath{\\mathsf{Wr}}\_W\\;T} f := a \\mathbin{\>\\!\\!\>\\mkern-6.7mu=}\_{T} \\lambda (w, a\') . 
      f\\;a \\mathbin{\>\\!\\!\>\\mkern-6.7mu=}\_{T} \\lambda (w\', b) . (w \\cdot w\', b)\$\$
  Given
  $f : A arrow.r sans(W r)_W #h(0em) T #h(0em) \( B + A \) = A arrow.r T \( W times \( B + A \) \)$,
  we define
  $ f^(dagger_(sans(W r)_W #h(0em) T)) := lambda a . \( W ⊗ f ; \( lambda \( w \, \( w' \, c \) \) . eta_T \( w dot.op w' \, c \) \) ; delta^(- 1) \)^dagger \( 1 \, a \) $

- The #emph[state transformer]
  $sans(S t)_S #h(0em) T #h(0em) A := S arrow.r T #h(0em) \( S times A \)$
  allows us to access mutable state of type $S$, with
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
  \$\$\\eta\_{\\ensuremath{\\mathsf{St}}\_S\\;T}\\;a := \\lambda s . \\eta\_T\\;(s, a) \\qquad
    a \\mathbin{\>\\!\\!\>\\mkern-6.7mu=}\_{\\ensuremath{\\mathsf{St}}\_S\\;T} f := \\lambda s . 
      a\\;s \\mathbin{\>\\!\\!\>\\mkern-6.7mu=}\_{T} \\lambda (s\', a\') . f\\;a\'\\;s\'\$\$
  Given
  $f : A arrow.r sans(S t)_S #h(0em) T #h(0em) \( B + A \) = A arrow.r S arrow.r T \( S times \( B + A \) \)$,
  we define
  $ f^(dagger_(sans(S t)_S #h(0em) T)) := lambda a \, s . \( \( lambda \( s \, a \) . f #h(0em) a #h(0em) s \) ; delta^(- 1) \)^dagger \( s \, a \) $

As a concrete example, we can build the heap monad from
Section~@refall:ssec:heaps by simply applying the state transformer to the UB
monad from Appendix~@refall:apx:ub, with state
$S := bb(N) harpoon.rt_(sans(f i n)) bb(N)$.

== Brookes-Style Concurrency
<refall:apx:rel-acq>
In this section, we show how to construct a concurrency monad from a
#cite(<brookes-full-abstraction-96>, form: "prose")-style model of
concurrency, which we axiomatize. We will then explicitly show how to
instantiate the model for sequentially consistent execution from
#cite(<brookes-full-abstraction-96>, form: "prose").

We begin by defining a #emph[countable closure operator], given below:

#block[
We define a #emph[(countable) closure operator]
$sans(c) : cal(P) \( T \) arrow.r cal(P) \( T \)$ on $T$ to be a
function on sets of $T$ which:

- #emph[is extensive]: $X subset.eq sans(c) \( X \)$

- #emph[is idempotent]:
  $sans(c) \( sans(c) \( X \) \) = sans(c) \( X \)$

- #emph[distributes over countable unions]:
  $sans(c) \( union.big_i X_i \) = union.big_i sans(c) \( X_i \)$

We say a set $X$ such that $sans(c) \( X \) = X$ is #emph[closed] under
$sans(c)$.

]
Note that this differs from the standard definition of a Kuratowski
topological closure operator, which only requires us to distributive
over #emph[finite] unions. We define the #emph[lift] of a closure
operator
$sans(c)_A : cal(P) \( T times A \) arrow.r cal(P) \( T times A \)$ to
be given by
$ sans(c)_A \( X \) := union.big_(a in A) { \( t' \, a \) divides t' in sans(c) \( { t divides \( t \, a \) in X } \) } $
Identifying $cal(P) \( T times A \)$ with $A arrow.r cal(P) \( T \)$,
this is equivalent to stating that
$sans(c)_A \( X \) := sans(c) compose X$. It is hence easy to check that
this gives a closure operator on $T times A$.

#block[
Given a monoid of #emph[traces] $T$ and a closure operator
$sans(c) : cal(P) \( T \) arrow.r cal(P) \( T \)$, we define the
#emph[Brookes monad] $sans(B)_(sans(c))$ over $sans(c)$ to be given by
closed sets of pairs $t therefore a$ of #emph[traces] $t in T$ and
#emph[results] $a in A$. In particular, we define
$ sans(B)_(sans(c)) \( A \) := sans(c)_A \( cal(P) \( T times A \) \) tilde.eq A arrow.r sans(c) \( cal(P) \( T \) \) $
with
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
\$\$\\eta\_{\\ensuremath{\\mathsf{B}}\_{\\ensuremath{\\mathsf{c}}}}\\;a := \\ensuremath{\\mathsf{c}}\_A(\\{1 \\therefore a\\}) \\qquad
  X \\mathbin{\>\\!\\!\>\\mkern-6.7mu=}\_{\\ensuremath{\\mathsf{B}}\_{\\ensuremath{\\mathsf{c}}}} f 
  := \\ensuremath{\\mathsf{c}}\_A(\\{t \\cdot t\' \\therefore b \\mid \\exists a . t \\therefore a \\in X, t\' \\therefore b \\in X\'\\})\$\$
It is easy to see that the Brookes monad is in fact poset-enriched under
the inclusion order. We say a Brookes monad is #emph[standard] if
$T = ⟨ S \, S ⟩^(\*)$ is the monoid of finite sequences of
#emph[rely-guarantee pairs] of #emph[states] $S$.

]
We note that this definition gives us a Kleisli category which is not
only poset-enriched, but in fact compatible with countable unions: with
the usual definition $union_i f_i := lambda a . union_i f_i \( a \)$, we
have
$ \( \( union.big_i f_i \) ; g \) \( a \) & := sans(c)_C \( { t dot.op t' therefore c divides exists b . t therefore b in union.big_i f_i \( a \) \, t' therefore c in g \( b \) } \)\
 & = sans(c) \( union.big_i { t dot.op t' therefore c divides exists b . t therefore b in f_i \( a \) \, t' therefore c in g \( b \) } \)\
 & = union.big_i sans(c) \( { t dot.op t' therefore c divides exists b . t therefore b in f_i \( a \) \, t' therefore c in g \( b \) } \)\
 & = union.big_i \( f_i ; g \) \( a \)\
f ; \( union.big_i g_i \) \( a \) & := sans(c) \( { t dot.op t' therefore c divides exists b . t therefore b in f \( a \) \, t' therefore c in union.big_i g_i \( b \) } \)\
 & = sans(c) \( union.big_i { t dot.op t' therefore c divides exists b . t therefore b in f \( a \) \, t' therefore c in g_i \( b \) } \)\
 & = union.big_i sans(c) \( { t dot.op t' therefore c divides exists b . t therefore b in f \( a \) \, t' therefore c in g_i \( b \) } \)\
 & = union.big_i \( f ; g_i \) \( a \) $ and likewise for coproducts.

We can always equip $sans(B)_(sans(c))$ with a (poset-enriched) Elgot
structure $\( dot.op \)^dagger$ by, for
$f : A arrow.r sans(B)_(sans(c)) \( B + A \)$, defining
$ f^dagger := union.big_(i in bb(N)) f_i $ where
$f_i : A arrow.r sans(B)_(cal(C)) \( B \)$ are the #emph[iterates] of
$f$, defined inductively as follows
$ f_0 := 0_(A \, B) = \( lambda x . diameter \) #h(2em) f_(i + 1) := f ; \[ sans(i d)_B \, f_i \] $
We note in particular that $forall i . f_i subset.eq f_(i + 1)$;
similarly, if $g subset.eq f$, we have that $g_i subset.eq f_i$. We can
think of analysis using this structure as corresponding to #emph[partial
correctness], since any infinite traces are simply discarded (a program
which always diverges will have denotation $diameter$). It is
straightforward to check that this is indeed an Elgot structure, since
it satisfies:

- #emph[Fixpoint]: we have, since $f_0 union g = g$,
  $ f^dagger = union.big_(i in bb(N)) f_i = union.big_(i in bb(N)) f_(i + 1) = union.big_(i in bb(N)) \( f ; \[ sans(i d)_B \, f_i \] \) = f ; \[ sans(i d)_B \, union.big_(i in bb(N)) f_i \] = f ; \[ sans(i d)_B \, f^dagger \] $
  as desired.

- #emph[Naturality]: by induction, we show that
  $\( f ; g + A \)_i = f_i ; g$, since
  $\( f ; g + A \)_0 = 0_(A \, C) = 0_(A \, B) ; g$ and
  $ \( f ; g + A \)_(i + 1) = f ; g + A ; \[ sans(i d)_C \, \( f ; g + A \)_i \] = f ; \[ g \, f_i ; g \] = f ; \[ sans(i d)_B \, f_i \] ; g = f_(i + 1) ; g $
  and therefore
  $ \( f ; g + A \)^dagger = union.big_(i in bb(N)) \( f ; g + A \)_i = union.big_(i in bb(N)) \( f_i ; g \) = \( union.big_(i in bb(N)) f_i \) ; g = f^dagger ; g $

- #emph[Codiagonal]: given $f : A arrow.r \( B + A \) + A$, define
  $g = f ; \[ sans(i d)_(B + A) \, iota_r \]$ and $h = f^dagger$. We
  have
  $ h_(i + 1) & = f^dagger ; \[ sans(i d) \, h_i \] = f ; \[ sans(i d) \, f^dagger \] ; \[ sans(i d) \, h_i \]\
   & = f ; \[ \[ sans(i d) \, h_i \] \, f^dagger ; \[ sans(i d) \, h_i \] \] = f ; \[ \[ sans(i d) \, h_i \] \, h_(i + 1) \]\
  g_(i + 1) & = f ; \[ sans(i d)_B \, iota_r \] ; \[ sans(i d) \, g_i \] = f ; \[ \[ sans(i d) \, g_i \] \, g_i \] $
  It follows by induction that $g_i subset.eq h_i$, since $g_0 = h_0$,
  and
  $ g_(i + 1) = f ; \[ \[ sans(i d) \, g_i \] \, g_i \] subset.eq f ; \[ \[ sans(i d) \, h_i \] \, h_i \] subset.eq f ; \[ \[ sans(i d) \, h_i \] \, h_(i + 1) \] = h_(i + 1) $
  We therefore have that $g^dagger subset.eq h^dagger$. On the other
  hand, we may show by induction on $j$ that
  $f_j ; \[ sans(i d) \, g^dagger \] subset.eq g^dagger$, since
  $0 subset.eq g^dagger$ and
  $ f_(j + 1) ; \[ sans(i d) \, g^dagger \] & = f ; \[ sans(i d) \, f_j \] ; \[ sans(i d) \, g^dagger \] = f ; \[ \[ sans(i d) \, g^dagger \] \, f_j ; \[ sans(i d) \, g^dagger \] \] subset.eq f ; \[ \[ sans(i d) \, g^dagger \] \, g^dagger \] = g^dagger $
  We now show by induction that $h_i subset.eq g^dagger$: noting that
  $h_0 = 0 subset.eq g^dagger$, it suffices to show that
  $ h_(i + 1) & = f ; \[ \[ sans(i d) \, h_i \] \, f^dagger ; \[ sans(i d) \, h_i \] \] subset.eq f ; \[ \[ sans(i d) \, g^dagger \] \, f_j ; \[ sans(i d) \, g^dagger \] \]\
   & = union.big_(j in bb(N)) \( f ; \[ \[ sans(i d) \, g^dagger \] \, f_j ; \[ sans(i d) \, g^dagger \] \] \) subset.eq union.big_(j in bb(N)) \( f ; \[ \[ sans(i d) \, g^dagger \] \, g^dagger \] \] \) = g^dagger $
  It follows that $h^dagger subset.eq g^dagger$ and hence that
  $h^dagger = g^dagger$, as desired.

- #emph[Directed Uniformity]: given arbitrary $f : A arrow.r B + A$,
  $g : X arrow.r B + X$ and $h : X arrow.r A$, we have that

  - Given $h ; f subset.eq g ; B + h$, for all $f_i$, we show by
    induction that $h ; f_i subset.eq g_i$ since
    $h ; f_0 = 0 subset.eq g_0$ and
    $ h ; f_(i + 1) = h ; f ; \[ sans(i d) \, f_i \] subset.eq g ; B + h ; \[ sans(i d) \, f_i \] = g ; \[ sans(i d) \, h ; f_i \] subset.eq g ; \[ sans(i d) \, g_i \] = g_(i + 1) $
    and therefore we have that
    $h ; f^dagger = union.big_i h ; f_i subset.eq union.big_i g_i = g^dagger$

  - Given $h ; f supset.eq g ; B + h$, for all $f_i$, we show by
    induction that $h ; f_i supset.eq g_i$ since $h ; f_0 = 0 = g_0$ and
    $ h ; f_(i + 1) = h ; f ; \[ sans(i d) \, f_i \] supset.eq g ; B + h ; \[ sans(i d) \, f_i \] = g ; \[ sans(i d) \, h ; f_i \] supset.eq g ; \[ sans(i d) \, g_i \] = g^dagger $
    and therefore we have that
    $h ; f^dagger = union.big_i h ; f_i supset.eq union.big_i g_i = g^dagger$

Following #cite(<brookes-full-abstraction-96>, form: "prose"), we can
build up a model of #emph[sequentially consistent] concurrent
computation by taking a standard Brookes monad with

- States maps from locations to values
  $S := sans(L o c) arrow.r sans(V a l)$

- Closure operator generated by:

  - #emph[Stuttering]
    $forall mu in S . dot.op arrow.r.twohead ⟨ mu \, mu ⟩$

  - #emph[Mumbling]
    $forall mu \, rho \, theta in S . ⟨ mu \, rho ⟩ ⟨ rho \, theta ⟩ arrow.r.twohead ⟨ mu \, theta ⟩$

The semantics of a write, for example, is then given by
$ sans(w r i t e) : sans(L o c) times sans(V a l) arrow.r sans(B)_(sans(c)) \( upright(bold(1)) \) := lambda \( ell \, v \) . sans(c)_(upright(bold(1))) \( { ⟨ mu \, \[ ell mapsto v \] mu ⟩ therefore \( \) divides mu in S } \) $
More complex states (e.g. involving per-thread buffers) and closure
operators can allow us to model weak memory models. In particular,
#cite(<jagadeesan-brookes-relaxed-12>, form: "prose") gives a Brookes
model of TSO, while #cite(<release-acquire>, form: "prose") gives a
Brookes model of release-acquire.
