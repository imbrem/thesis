// VERBATIM TRANSCRIPTION — markup translated from LaTeX to Typst.
// Source: papers/isotope/denotational-semantics-of-ssa.tex @ afa82558acf643f53a3e038e635ed9520ace88c6
// Coverage: lines 6597–9481, “Definitions and Proofs” through “Completeness”.
#import "/lib/prelude.typ": *
#show: appendix

#set math.equation(numbering: "(1)")
= Definitions and Proofs
<definitions-and-proofs>
== Syntactic Metatheory
<syntactic-metatheory>
#figure([$ \( gamma \, x mapsto e \) \( x \) = e #h(2em) \( gamma \, y mapsto e \) \( x \) = gamma \( x \) #h(2em) \( dot.op \) \( x \) = x\
  \
  \[ gamma \] x = gamma \( x \) #h(2em) \[ gamma \] \( sans(l e t) #h(0em) x = a ; #h(0em) e \) = sans(l e t) #h(0em) x = \[ gamma \] a ; #h(0em) \[ gamma \] e #h(2em) \[ gamma \] \( a \, b \) = \( \[ gamma \] a \, \[ gamma \] b \) #h(2em) \[ gamma \] \( \) = \( \)\
  \[ gamma \] \( sans(l e t) #h(0em) \( x \, y \) = a ; #h(0em) e \) = sans(l e t) #h(0em) \( x \, y \) = \[ gamma \] a ; #h(0em) \[ gamma \] e #h(2em) \[ gamma \] \( iota_l #h(0em) a \) = iota_l #h(0em) \[ gamma \] a #h(2em) \[ gamma \] \( iota_r #h(0em) b \) = iota_r #h(0em) \[ gamma \] b\
  \[ gamma \] \( sans(c a s e) #h(0em) e #h(0em) { iota_l #h(0em) x : a \, iota_r #h(0em) y : b } \) = sans(c a s e) #h(0em) \[ gamma \] e #h(0em) { iota_l #h(0em) x : \[ gamma \] a \, iota_r #h(0em) y : \[ gamma \] b }\
  \[ gamma \] \( sans(a b o r t) #h(0em) a \) = sans(a b o r t) #h(0em) \[ gamma \] a\
  \
  \[ gamma \] \( sans(b r) #h(0em) ell #h(0em) a \) = sans(b r) #h(0em) ell #h(0em) \[ gamma \] a #h(2em) \[ gamma \] \( sans(l e t) #h(0em) x = a ; r \) = sans(l e t) #h(0em) x = \[ gamma \] a ; \[ gamma \] r\
  \[ gamma \] \( sans(l e t) #h(0em) \( x \, y \) = e ; r \) = sans(l e t) #h(0em) \( x \, y \) = \[ gamma \] e ; \[ gamma \] r\
  \[ gamma \] \( sans(c a s e) #h(0em) e #h(0em) { iota_l #h(0em) x : r \, iota_r #h(0em) y : s } \) = sans(c a s e) #h(0em) \[ gamma \] e #h(0em) { iota_l #h(0em) x : \[ gamma \] r \, iota_r #h(0em) y : \[ gamma \] s }\
  \[ gamma \] \( r #h(0em) sans(w h e r e) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i \) = \[ gamma \] r #h(0em) sans(w h e r e) #h(0em) \( ell_i \( x_i \) : { \[ gamma \] t_i } \, \)_i\
  \
  \[ gamma \] \( dot.op \) = dot.op #h(2em) \[ gamma \] \( gamma' \, x mapsto e \) = \( \[ gamma \] gamma' \, x mapsto \[ gamma \] e \)\
  \
  \[ gamma \] \( dot.op \) = dot.op #h(2em) \[ gamma \] \( sigma \, ell \( x \) mapsto r \) = \( \[ gamma \] sigma \, ell \( x \) mapsto \[ gamma \] r \) $

  ],
  caption: [
    Capture-avoiding substititon for #lssa terms,
    regions, and (label) substitutions; in particular, we assume bound
    variables and labels are $alpha$-converted so as not to appear in
    $gamma$/$sigma$.
  ]
)
<fig:ssa-subst-def>

== Lexical SSA and ANF
<lexical-ssa-and-anf>
<proof:anf-conversion>

#block[
#emph[Proof.] We may show that $sans(A N F) \( r \)$ is always in ANF
and that $sans(A N F)_(sans(l e t)) \( x \, a \, r \)$ is in ANF if $r$
is by a straightforward induction. To prove the rest of the lemma, we
begin by proving the correctness of
$sans(A N F)_(sans(l e t)) \( x \, a \, r \)$ by induction on
expressions $a$:

- If $Gamma tack.r_epsilon.alt^(sans(a n f)) a : A$ is atomic, we are
  done; otherwise

- If $a = f #h(0em) e$, then, since $e$ is a subterm of $a$, by
  induction, we have
  $ sans(l e t) #h(0em) x = a ; r approx sans(l e t) #h(0em) y = e ; sans(l e t) #h(0em) x = f #h(0em) y ; r approx sans(A N F)_(sans(l e t)) \( y \, e \, sans(l e t) #h(0em) x = f #h(0em) y ; r \) = sans(A N F)_(sans(l e t)) \( x \, a \, r \) $
  as desired.

- The cases for pairs, injections, and aborts containing expressions are
  analogous

- If
  $a = sans(c a s e) #h(0em) e #h(0em) { iota_l #h(0em) y : b \, iota_r #h(0em) z : c }$,
  then we may rewrite
  $ sans(l e t) #h(0em) x = a ; r approx sans(l e t) #h(0em) w = e ; sans(c a s e) #h(0em) w #h(0em) { iota_l #h(0em) y : sans(l e t) #h(0em) b = x ; #h(0em) r \, iota_r #h(0em) z : sans(l e t) #h(0em) c = x ; #h(0em) r } $
  Since $r$ is in ANF, by induction (since $b \, c$ are subterms of
  $a$), this is equivalent to
  $ sans(l e t) #h(0em) w = e ; sans(c a s e) #h(0em) w #h(0em) { iota_l #h(0em) y : sans(A N F)_(sans(l e t)) \( b \, x \, r \) \, iota_r #h(0em) z : sans(A N F)_(sans(l e t)) \( c \, x \, r \) } $
  which is equal to $sans(A N F)_(sans(l e t)) \( x \, a \, r \)$, as
  desired.

- The cases for unary and binary $sans(l e t)$ are analogous to the
  above

We may now prove the correctness of $sans(A N F) \( r \)$ by a
straightforward induction on $r$:

- If $r = sans(b r) #h(0em) ell #h(0em) a$, by $beta$-reduction, we have
  that
  $ r approx sans(l e t) #h(0em) x = a ; #h(0em) sans(b r) #h(0em) ell #h(0em) x approx sans(A N F)_(sans(l e t)) \( x \, a \, sans(b r) #h(0em) ell #h(0em) x \) = sans(A N F) \( r \) $

- If $r = sans(l e t) #h(0em) x = a ; r'$, then by induction we have
  that
  $ r approx sans(l e t) #h(0em) x = a ; sans(A N F) \( r' \) approx sans(A N F)_(sans(l e t)) \( x \, a \, sans(A N F) \( r' \) \) = sans(A N F) \( r \) $
  as desired.

- If $r = sans(l e t) #h(0em) \( x \, y \) = a ; r'$, then by induction
  we have that
  $ r & approx sans(l e t) #h(0em) z = a ; sans(l e t) #h(0em) \( x \, y \) = z ; r'\
   & approx sans(l e t) #h(0em) z = a ; sans(l e t) #h(0em) \( x \, y \) = z ; sans(A N F) \( r' \)\
   & approx sans(A N F)_(sans(l e t)) \( z \, a \, sans(l e t) #h(0em) \( x \, y \) = z ; sans(A N F) \( r' \) \) approx sans(A N F) \( r \) $
  The proof for $sans(c a s e)$-statements is analogous

- The case for control-flow graphs follows trivially by induction

~◻

]
<proof:ssa-conversion>

#block[
#emph[Proof.] Given that
$sans(S S A)_(sans(a)) \( r \, G \) approx r #h(0em) sans(w h e r e) #h(0em) G$
for $r$ in ANF, it is trivial to see that
$ sans(S S A) \( r \) := sans(S S A)_(sans(a)) \( sans(A N F) \( r \) \, dot.op \) approx \( sans(A N F) \( r \) #h(0em) sans(w h e r e) #h(0em) dot.op \) approx sans(A N F) \( r \) approx r $
We hence only need to prove the second part of the lemma. We proceed by
induction on ANF regions $r$ as follows:

- If $r$ is a terminator, this holds trivially by reflexivity

- If $r = sans(l e t) #h(0em) x = a ; r'$, then by induction, we have
  that
  $ sans(S S A)_(sans(a)) \( r \, G \) := sans(l e t) #h(0em) x = a ; sans(S S A)_(sans(a)) \( r' \, G \) approx sans(l e t) #h(0em) x = a ; r' #h(0em) sans(w h e r e) #h(0em) G approx sans(l e t) #h(0em) x = a ; r' #h(0em) sans(w h e r e) #h(0em) G approx r #h(0em) sans(w h e r e) #h(0em) G $
  as desired. The case for binary $sans(l e t)$-statements is analogous.

- If
  $r = sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) x : s \, iota_r #h(0em) y : t }$,
  then by induction, we have that
  $ sans(S S A)_(sans(a)) \( r \, G \) & := \( sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) x : sans(b r) #h(0em) ell_l #h(0em) x \, iota_r #h(0em) y : sans(b r) #h(0em) ell_r #h(0em) y } \) #h(0em) sans(w h e r e) #h(0em) G \, ell_l \( x \) : { sans(S S A) \( s \) } \, ell_r \( y \) : { sans(S S A) \( t \) }\
   & := \( sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) x : sans(b r) #h(0em) ell_l #h(0em) x \, iota_r #h(0em) y : sans(b r) #h(0em) ell_r #h(0em) y } \) #h(0em) sans(w h e r e) #h(0em) G \, ell_l \( x \) : { s } \, ell_r \( y \) : { t }\
   & approx \( \( sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) x : sans(b r) #h(0em) ell_l #h(0em) x \, iota_r #h(0em) y : sans(b r) #h(0em) ell_r #h(0em) y } \) #h(0em) sans(w h e r e) #h(0em) ell_l \( x \) : { s } \, ell_r \( y \) : { t } \) #h(0em) sans(w h e r e) #h(0em) G\
   & approx sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) x : s \, iota_r #h(0em) y : t } #h(0em) sans(w h e r e) #h(0em) G approx r #h(0em) sans(w h e r e) #h(0em) G $

- If
  $r = r' #h(0em) sans(w h e r e) #h(0em) ell_i \( x_i \) : { t_i } \, \)_i$,
  then by induction, we have that
  $ sans(S S A)_(sans(a)) \( r \, G \) & := sans(S S A)_(sans(a)) \( r' \, G \, \( ell_i \( x_i \) : { sans(S S A) \( t_i \) } \, \)_i \)\
   & approx r' #h(0em) sans(w h e r e) #h(0em) G \, \( ell_i \( x_i \) : { t_i } \, \)_i\
   & approx \( r' #h(0em) sans(w h e r e) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i #h(0em) sans(w h e r e) #h(0em) G approx r #h(0em) sans(w h e r e) #h(0em) G\
   $

~◻

]
<proof:cfg-perm-invar>

#block[
#emph[Proof.] We proceed by induction on the size of $G$. If $G$
consists only of an entry block, there is only one permutation, so we
are done. Otherwise, assume
$G = beta \, \( ell_i \( x_i \) : { t_i } \, \)_(i in I)$. Furthermore,
let:

- $ell_i \( x_i \) : { beta_i }$ be the children of $beta$ in $G$ in
  order

- $G_i = \( kappa_(i \, j) \( y_(i \, j) \) : { t_(i \, j) } \, \)_(j in I)$
  be the CFG composed of the descendants of $beta_i$ in $G$, with
  $beta_i$ as entry block, in order

- $ell_(i') \( x_(i') \) : { beta_(i') }$ be the children of $beta$ in
  $G'$ in order

- $G_(i')$ be the CFG composed of the descendants of $beta_(i')$ in
  $G'$, with $beta_(i')$ as entry block, in order

By assumption, there exists some permutation $sigma : I arrow.r I$ such
that
$G' = beta \, \( ell_(sigma_i) \( x_(sigma_i) \) : { t_(sigma_i) } \, \)_(i in I)$.
It follows that, since the dominance relation on labels is
permutation-invariant, there exists some permutation $rho$ such that
$forall i in I \, ell_(i') \( x_(i') \) : { beta_(i') } = ell_(rho_i) \( x_(rho_i) \) : { beta_(rho_i) }$,
as well as permutations $tau_i$ such that
$G_(i') = \( ell_(rho_i \, tau_(i j)) \( x_(rho_i \, tau_(i j)) \) : { t_(rho_i \, tau_(i j)) } \, \)_(j in I)$,
implying in particular that $G_(i') tilde.eq G_(rho_i)$. By induction,
we hence have that, for all $i$,
$sans(r e g) \( G_(i') \) approx sans(r e g) \( G_(rho_i) \)$, and hence
that
$ sans(r e g) \( G' \) & := sans(b b) \( beta \, \( ell_(rho_i) \( x_(rho_i) \) : { sans(r e g) \( G_(i') \) } \, \)_(i in I) \)\
 & approx sans(b b) \( beta \, \( ell_(rho_i) \( x_(rho_i) \) : { sans(r e g) \( G_(rho_i) \) } \, \)_(i in I) \)\
 & approx sans(b b) \( beta \, \( ell_i \( x_i \) : { sans(r e g) \( G_i \) } \, \)_(i in I) \) approx sans(r e g) \( G \) $~◻

]
<proof:cfg-conversion>

#block[
#emph[Proof.] We will proceed by induction on the length of
$G = sans(c f g) \( r \)$. If $G$ consists of only an entry block
$beta$, then we trivially have that
$r = sans(r e g) \( sans(c f g) \( r \) \)$, and so we are done.
Otherwise, assume
$r = sans(b b) \( beta \, \( ell_i \( x_i \) : { t_i } \, \)_(i in I) \)$.
Clearly, $sans(c f g) \( r \)$ will have entry block $beta$; moreover,
since every block in $sans(c f g) \( r \)$ other than those of the form
$sans(e n t r y) \( t_i \)$ can only be reached from within the region
$t_i$ (due to lexical scoping of labels), we have
$beta_i = sans(e n t r y) \( t_(rho_i) \)$ for some injection $rho$,
where $beta_i$ are the children of $beta$ in the dominance tree of $G$.
In particular, we can write
${ ell_i \( x_i \) : { sans(e n t r y) \( t_i \) } \, }_i$ as the
disjoint union of:

- The immediate children of $beta$, $kappa_i \( y_i \) : { beta_i }$,
  where $kappa_i = ell_(rho_i)$, $y_i = x_(rho_i)$, and
  $beta_i = sans(e n t r y) \( t_(rho_i) \)$

- The nodes dominated by each $beta_i$ but not immediately dominated by
  $beta$; we will write the collection of such nodes for each $i$ as
  $kappa_(i \, j) \( y_(i \, j) \) : { beta_(i \, j) }$, where
  $kappa_(i \, j) = ell_(rho_(i \, j))$,
  $y_(i \, j) = x_(rho_(i \, j))$, and
  $beta_(i \, j) = sans(e n t r y) \( t_(rho_(i \, j)) \)$.

As in the algorithm to compute $sans(r e g) \( dot.op \)$, let $G_i$
denote the control-flow graph with entry block $beta_i$ consisting of
all blocks dominated by $beta_i$. We may write
$ G tilde.eq beta \, \( kappa_i \( y_i \) : { G_i } \, \)_(i in I) #h(2em) forall i in I \, G_i = beta_i \, \( kappa_(i \, j) \( y_(i \, j) \) : { beta_(i \, j) } \, \)_(j in I) \, R_i $
where $R_i$ is the "remainder" of the control-flow graph $G_i$. Note the
equations for $G_i$ are actually equalities, rather than being
equivalence up to permutation $tilde.eq$, since the $beta_(i \, j)$,
appear in $G$ before any other elements, being immediate children of
$beta$. It follows that
$ sans(r e g) \( sans(c f g) \( r \) \) = sans(r e g) \( sans(c f g) \( sans(b b) \( beta \, \( ell_i \( x_i \) : { t_i } \, \)_i \) \) \) = sans(b b) \( beta \, \( kappa_i \( y_i \) : { sans(r e g) \( G_i \) } \, \)_i \) $
Now, define the lexical SSA regions
$ r_i = sans(b b) \( beta_i \, \( \( kappa_(i \, j) \( y_(i \, j) \) : { t_(rho_(i \, j)) } \, \)_j \, sans(c h i l d r e n) \( t_i \) \) \) $
It is easy to show that $sans(c f g) \( r_i \) tilde.eq G_i$, since
every basic block dominated by $beta_i$ must be dominated via either
some $t_(rho_(i \, j))$ or some child of $t_i$. Since by induction
$sans(r e g) \( sans(c f g) \( r_i \) \) approx r_i$, and by the
previous lemma
#todo[Port the following preserved source equation to native Typst.]
\$\\ensuremath{\\mathsf{reg}}(\\tocfg\_r\_i) \\approx\\ensuremath{\\mathsf{reg}}(G\_i)\$,
it follows that
$ sans(r e g) \( sans(c f g) \( r \) \) approx sans(b b) \( beta \, \( kappa_i \( y_i \) : { r_i } \, \)_i \) $
Define
$ T_i = \( kappa_j \( y_j \) : { r_j } \, \)_(j < i) \, \( kappa_j \( y_j \) : { t_j } \, \( kappa_(j \, k) \( y_(j \, k) \) : { t_(rho_(j \, k)) } \, \)_k \, \)_(j gt.eq i) $
Using Equation~#todo[Resolve source reference `eqn:pull-where` during integration.], we may show that, for all $i$,
$sans(b b) \( beta \, T_(i + 1) \) approx sans(b b) \( beta \, T_i \)$,
since

- For all $j$, $t_(rho_(i \, j))$ cannot use variables defined in
  $beta_i$, or $r$ would not typecheck

- For all $j$, if $r_k$ or $t_(rho_(k \, j'))$ calls $kappa_(i \, j)$,
  then $k = i$, or $beta_(i \, j)$ would not be dominated by $beta_i$

- Similarly, $beta$ cannot call $kappa_(i \, j)$ or $beta_(i \, j)$
  would be a direct descendant of $beta$

We hence have by induction that
$ sans(r e g) \( sans(c f g) \( r \) \) approx sans(b b) \( beta \, T_N \) approx sans(b b) \( beta \, T_0 \) approx r $
as desired, since $T_0$ is a permutation of
$\( ell_i \( x_i \) : { t_i } \, \)_i$.~◻

]
== Böhm-Jacopini
<böhm-jacopini>
#block[
The following facts hold:

- Given $Gamma tack.r r gt.tri square.filled.medium \( A \)$ and
  $Gamma \, square.stroked.tiny : A tack.r s gt.tri sans(L)$, we have
  that
  $  & bracket.l Gamma tack.r sans(s e q) \( r \, s \) := \( \[ square.filled.medium \( x \) mapsto sans(b r) #h(0em) ell #h(0em) x \] r #h(0em) sans(w h e r e) #h(0em) ell \( square.stroked.tiny \) : { s } \) gt.tri sans(L) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r \[ square.filled.medium \( x \) mapsto sans(b r) #h(0em) ell #h(0em) x \] r gt.tri ell \( A \) bracket.r \) ; bracket.l Gamma bracket.r times alpha_A^(+) ; bracket.l Gamma \, square.stroked.tiny : A tack.r s gt.tri sans(L) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r r gt.tri ell \( A \) bracket.r \) ; bracket.l Gamma bracket.r times alpha_A^(+) ; bracket.l Gamma \, square.stroked.tiny : A tack.r s gt.tri sans(L) bracket.r $

- Given $Gamma tack.r_epsilon.alt e : A$,
  $Gamma \, square.stroked.tiny : A tack.r r gt.tri square.filled.medium \( B + A \)$,
  we have that
  $  & bracket.l Gamma tack.r sans(l o o p) \( e \, r \) := \( sans(b r) #h(0em) ell #h(0em) e #h(0em) sans(w h e r e) #h(0em) ell \( square.stroked.tiny \) : { sans(s e q) \( r \, sans(c a s e) #h(0em) square.stroked.tiny #h(0em) { iota_l #h(0em) x : sans(b r) #h(0em) square.filled.medium #h(0em) x \, iota_r #h(0em) y : sans(b r) #h(0em) ell #h(0em) y } \) } \) gt.tri square.filled.medium \( B \) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt e : A bracket.r \) ; sans(r f i x) \( bracket.l Gamma \, square.stroked.tiny : A tack.r r gt.tri square.filled.medium \( B + A \) bracket.r ; alpha_(B + A)^(+) \) $

- Given $sans(R) = \( ell_i \( A_i \) \, \)_i$ and
  $Gamma \, x_i : A_i tack.r t_i gt.tri sans(L)$, we have
  $  & bracket.l Gamma \, c : 〈 sans(R) 〉 tack.r sans(c a s e)_(sans(R)) #h(0em) c #h(0em) { ell_i \( x_i \) : t_i } gt.tri sans(L) bracket.r\
   & = bracket.l Gamma bracket.r times alpha_(Sigma_i bracket.l A_i bracket.r)^(+) ; delta_Sigma^(- 1) ; \[ bracket.l Gamma \, x_i : A_i tack.r t_i gt.tri sans(L) bracket.r \, \]_i $

We have that
$ bracket.l Gamma \, square.stroked.tiny : tack.t tack.r_(\[ sans(L) \]) sans(u a) #h(0em) square.stroked.tiny : 〈 sans(L) 〉 + 〈 sans(R) 〉 bracket.r = pi_r ; alpha_(bracket.l sans(L) bracket.r + bracket.l sans(R) bracket.r)^(+) $

We have that
$ bracket.l Gamma tack.r sans(p a c k)_kappa^(+) \( sans(L) \) : sans(L) arrow.r.squiggly kappa \( 〈 sans(L) 〉 \) bracket.r = pi_r ; alpha_(upright(bold(0)) + bracket.l sans(L) bracket.r)^(+) $
and
$ bracket.l Gamma tack.r sans(u n p a c k)_kappa^(+) \( sans(L) \) : kappa \( 〈 sans(L) 〉 \) arrow.r.squiggly sans(L) bracket.r = pi_r ; alpha_(bracket.l sans(L) bracket.r)^(+) $
In particular, given $Gamma tack.r r gt.tri sans(L)$, we have that
$ bracket.l Gamma tack.r 〈 r 〉^(+) gt.tri square.filled.medium \( 〈 sans(L) 〉 \) bracket.r = bracket.l Gamma tack.r r gt.tri sans(L) bracket.r ; alpha_(upright(bold(0)) + bracket.l sans(L) bracket.r)^(+) $

]
<proof:bohm-jacopini>

#block[
#emph[Proof.] We begin by showing the correctness of
$sans(P W)_(sans(L)) \( r \)$ by induction on $r$:

- If $r = sans(b r) #h(0em) ell #h(0em) a$, we have that
  $sans(P W)_(sans(L)) \( a \) = sans(p a c k)^(+) \( sans(L) \)_ell \( a \) = \[ sans(b r) #h(0em) ell #h(0em) a \]^(+)$
  by definition

- If $r = sans(l e t) #h(0em) x = a ; s$, we have by induction that
  $ sans(P W)_(sans(L)) \( sans(l e t) #h(0em) x = a ; s \) = sans(l e t) #h(0em) x = a ; sans(P W)_(sans(L)) \( s \) approx sans(l e t) #h(0em) x = a ; \[ s \]^(+) = \[ sans(l e t) #h(0em) x = a ; s \]^(+) $

- If $r = sans(l e t) #h(0em) \( x \, y \) = a ; s$, we have by
  induction that
  $ sans(P W)_(sans(L)) \( sans(l e t) #h(0em) \( x \, y \) = a ; s \) = sans(l e t) #h(0em) \( x \, y \) = a ; sans(P W)_(sans(L)) \( s \) approx sans(l e t) #h(0em) \( x \, y \) = a ; 〈 s 〉^(+) = 〈 sans(l e t) #h(0em) \( x \, y \) = a ; s 〉^(+) $

- If
  $r = sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) x : s \, iota_r #h(0em) y : t }$,
  we have by induction that
  $ sans(P W)_(sans(L)) \( sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) x : s \, iota_r #h(0em) y : t } \) & = sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) x : sans(P W)_(sans(L)) \( s \) \, iota_r #h(0em) y : sans(P W)_(sans(L)) \( t \) }\
   & approx sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) x : 〈 s 〉^(+) \, iota_r #h(0em) y : 〈 t 〉^(+) }\
   & = 〈 sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) x : s \, iota_r #h(0em) y : t } 〉^(+)\
   $

- Assume
  $r = s #h(0em) sans(w h e r e) #h(0em) \( ell_i \( t_i \) : { x_i } \, \)_i$.
  Define $sans(R) = \( ell_i \( A_i \) \, \)_i$. By induction, we have
  that
  $forall i \, sans(P W)_(sans(L) \, sans(R)) \( t_i \) approx 〈 t_i 〉^(+)$,
  and hence by soundness
  $ bracket.l Gamma \, x_i : A_i tack.r sans(P W)_(sans(L)) \( t_i \) gt.tri square.filled.medium \( 〈 sans(L) \, sans(R) 〉 \) bracket.r = bracket.l Gamma \, x_i : A_i tack.r 〈 t_i 〉^(+) gt.tri square.filled.medium \( 〈 sans(L) \, sans(R) 〉 \) bracket.r $
  Now, define
  $ D = sans(c a s e)_(sans(L)) #h(0em) square.stroked.tiny #h(0em) { ell_i \( x_i \) : sans(s e q) \( sans(P W)_(sans(L)) \( t_i \) \, sans(b r) #h(0em) square.filled.medium #h(0em) \( sans(u a) #h(0em) square.stroked.tiny \) } \) $
  and $L = sans(l o o p) \( y \, D \)$. It follows that
  $  & bracket.l Gamma \, square.stroked.tiny : \[ R \] tack.r D gt.tri square.filled.medium \( 〈 L 〉 + 〈 R 〉 \) bracket.r\
   & = bracket.l Gamma bracket.r times alpha_(Sigma_i bracket.l A_i bracket.r)^(+) ; delta_Sigma^(- 1) ; \[ bracket.l Gamma \, x_i : A_i tack.r sans(s e q) \( sans(P W)_(sans(L)) \( t_i \) \, sans(b r) #h(0em) square.filled.medium #h(0em) \( sans(u a) #h(0em) square.stroked.tiny \) \) gt.tri square.filled.medium \( 〈 sans(L) 〉 + 〈 sans(R) 〉 \) bracket.r \, \]_i\
   & = bracket.l Gamma bracket.r times alpha_(Sigma_i bracket.l A_i bracket.r)^(+) ; delta_Sigma^(- 1) ; \[ bracket.l Gamma \, x_i : A_i tack.r sans(P W)_(sans(L)) \( t_i \) gt.tri square.filled.medium \( 〈 sans(L) \, sans(R) 〉 \) bracket.r ; alpha_(upright(bold(0)) + \( bracket.l sans(L) bracket.r + bracket.l sans(R) bracket.r \))^(+) \, \]_i\
   & = bracket.l Gamma bracket.r times alpha_(Sigma_i bracket.l A_i bracket.r)^(+) ; delta_Sigma^(- 1) ; \[ bracket.l Gamma \, x_i : A_i tack.r 〈 t_i 〉^(+) gt.tri square.filled.medium \( 〈 sans(L) \, sans(R) 〉 \) bracket.r ; alpha_(upright(bold(0)) + \( bracket.l sans(L) bracket.r + bracket.l sans(R) bracket.r \))^(+) \, \]_i\
   & = bracket.l Gamma bracket.r times alpha_(Sigma_i bracket.l A_i bracket.r)^(+) ; delta_Sigma^(- 1) ; \[ bracket.l Gamma \, x_i : A_i tack.r t_i gt.tri sans(L) \, sans(R) bracket.r ; alpha_(upright(bold(0)) + \( bracket.l sans(L) bracket.r + bracket.l sans(R) bracket.r \))^(+) \, \]_i $
  and therefore that
  $  & bracket.l Gamma \, y : 〈 R 〉 tack.r L gt.tri square.filled.medium \( 〈 sans(L) 〉 \) bracket.r\
   & = sans(l e t) \( bracket.l Gamma \, y : 〈 R 〉 tack.r_tack.t y : A bracket.r \) ; sans(r f i x) \( bracket.l Gamma \, square.stroked.tiny : 〈 R 〉 tack.r D gt.tri square.filled.medium \( 〈 L 〉 + 〈 R 〉 \) bracket.r ; alpha_(\( upright(bold(0)) + bracket.l sans(L) bracket.r \) + bracket.l sans(R) bracket.r)^(+) \)\
   & = sans(r f i x) \( bracket.l Gamma bracket.r times alpha_(Sigma_i bracket.l A_i bracket.r)^(+) ; delta_Sigma^(- 1) ; \[ bracket.l Gamma \, x_i : A_i tack.r t_i gt.tri 〈 sans(L) \, sans(R) 〉 bracket.r ; alpha_(\( upright(bold(0)) + bracket.l sans(L) bracket.r \) + bracket.l sans(R) bracket.r)^(+) \, \]_i \)\
   & = bracket.l Gamma bracket.r times alpha_(Sigma_i bracket.l A_i bracket.r)^(+) ; sans(r f i x) \( sans(l s e m)_(Gamma \, sans(L)) \( \( ell_i \( x_i \) : { t_i } \, \)_i \) \) ; alpha_(upright(bold(0)) + bracket.l sans(L) bracket.r)^(+) $
  Hence, we have that
  $  & bracket.l Gamma \, square.stroked.tiny : 〈 sans(L) \, sans(R) 〉 tack.r sans(c a s e) #h(0em) sans(u a) #h(0em) square.stroked.tiny #h(0em) { iota_l #h(0em) x : sans(b r) #h(0em) square.filled.medium #h(0em) x \, iota_r #h(0em) y : L } gt.tri square.filled.medium \( \[ sans(L) \] \) bracket.r\
   & = bracket.l Gamma bracket.r times alpha_(bracket.l sans(L) bracket.r + bracket.l sans(R) bracket.r)^(+) ; delta^(- 1) ; \[ bracket.l Gamma \, x : 〈 sans(L) 〉 tack.r sans(b r) #h(0em) square.filled.medium #h(0em) x gt.tri square.filled.medium \( 〈 sans(L) 〉 \) bracket.r \, bracket.l Gamma \, y : 〈 sans(R) 〉 tack.r L gt.tri square.filled.medium \( 〈 sans(L) 〉 \) bracket.r \]\
   & = bracket.l Gamma bracket.r times alpha_(bracket.l sans(L) bracket.r + bracket.l sans(R) bracket.r)^(+) ; delta^(- 1) ; \[ pi_r ; alpha_(upright(bold(0)) + bracket.l sans(L) bracket.r)^(+) \, bracket.l Gamma bracket.r times alpha_(Sigma_i bracket.l A_i bracket.r)^(+) ; sans(r f i x) \( sans(l s e m)_(Gamma \, sans(L)) \( \( ell_i \( x_i \) : { t_i } \, \)_i \) \) ; alpha_(upright(bold(0)) + bracket.l sans(L) bracket.r)^(+) \]\
   & = bracket.l Gamma bracket.r times alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+) ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( sans(l s e m)_(Gamma \, sans(L)) \( \( ell_i \( x_i \) : { t_i } \, \)_i \) \) \] ; alpha_(upright(bold(0)) + bracket.l sans(L) bracket.r)^(+) $
  It hence suffices by completeness (Theorem~#todo[Resolve source reference `thm:complete-reg` during integration.]) to show
  that
  $  & bracket.l Gamma tack.r sans(s e q) \( sans(P W)_(sans(L)) \( r \) \, sans(c a s e) #h(0em) sans(u a) #h(0em) square.stroked.tiny #h(0em) { iota_l #h(0em) x : sans(b r) #h(0em) square.filled.medium #h(0em) x \, iota_r #h(0em) y : L } \) gt.tri square.filled.medium \( 〈 sans(L) 〉 \) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r sans(P W)_(sans(L)) \( r \) gt.tri square.filled.medium \( 〈 sans(L) \, sans(R) 〉 \) bracket.r \) ; bracket.l Gamma bracket.r times alpha_(bracket.l sans(L \, R) bracket.r)^(+) ;\
   & #h(2em) bracket.l Gamma \, square.stroked.tiny : 〈 sans(L) \, sans(R) 〉 tack.r sans(c a s e) #h(0em) sans(u a) #h(0em) square.stroked.tiny #h(0em) { iota_l #h(0em) x : sans(b r) #h(0em) square.filled.medium #h(0em) x \, iota_r #h(0em) y : L } gt.tri square.filled.medium \( 〈 sans(L) 〉 \) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r sans(P W)_(sans(L)) \( r \) gt.tri square.filled.medium \( 〈 sans(L) \, sans(R) 〉 \) bracket.r \) ; bracket.l Gamma bracket.r times alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+) ; delta^(- 1) ;\
   & #h(2em) \[ pi_r \, sans(r f i x) \( sans(l s e m)_(Gamma \, sans(L)) \( \( ell_i \( x_i \) : { t_i } \, \)_i \) \) \] ; alpha_(upright(bold(0)) + bracket.l sans(L) bracket.r)^(+)\
   & = bracket.l Gamma tack.r r #h(0em) sans(w h e r e) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i gt.tri sans(L) bracket.r ; alpha_(upright(bold(0)) + bracket.l sans(L) bracket.r)^(+)\
   & = bracket.l Gamma tack.r \[ r #h(0em) sans(w h e r e) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i \]^(+) gt.tri sans(L) bracket.r $

~◻

]
== Substitution
<substitution>
#block[
The following facts hold:

+ For all $f : A arrow.r B times C$,
  $g : \( A times B \) times C arrow.r D$, we have
  $ sans(l e t) \( f \) ; alpha ; sans(l e t) \( g \) ; \( pi_l ; pi_l \) times D = sans(l e t) \( sans(l e t) \( f \) ; alpha ; g \) $

+ For all $f : A arrow.r B + C$, $g : A times B arrow.r D$,
  $h : A times C arrow.r D$, we have
  $ sans(l e t) \( f \) ; delta^(- 1) ; \[ sans(l e t) \( g \) ; pi_l times D \, sans(l e t) \( h \) ; pi_l times D \] = sans(l e t) \( sans(l e t) \( f \) ; delta^(- 1) ; \[ g \, h \] \) $

+ For all $f_i : R times A_i arrow.r B$, we have
  $ delta_Sigma^(- 1) ; \[ sans(l e t) \( f_i \) ; pi_l times B \, \]_i = sans(l e t) \( delta_Sigma^(- 1) ; \[ f_i \]_i \) ; pi_l times B $
  i.e.,
  $ delta_Sigma^(- 1) ; \[ sans(r l e t) \( f_i \) \, \]_i = sans(r l e t) \( delta_Sigma^(- 1) ; \[ f_i \]_i \) $

+ For all $f : A arrow.r B + C$, $g : A times B arrow.r B'$,
  $h : A times C arrow.r C'$, we have
  $ sans(l e t) \( sans(l e t) \( f \) ; delta^(- 1) ; g + h \) & = sans(l e t) \( f \) ; delta^(- 1) ; \[ sans(l e t) \( g \) ; pi_l times iota_l \, sans(l e t) \( h \) ; pi_l times iota_r \]\
   & = sans(l e t) \( f \) ; delta^(- 1) ; \( sans(l e t) \( g \) ; pi_l times B' \) + \( sans(l e t) \( h \) ; pi_l times C' \) ; delta\
   & = sans(l e t) \( f \) ; delta^(- 1) ; sans(r l e t) \( g \) + sans(r l e t) \( h \) ; delta $
  In particular, we have
  $ sans(l e t) \( sans(l e t) \( f \) ; delta^(- 1) ; pi_r + h \) & = sans(l e t) \( f \) ; delta^(- 1) ; \[ A times iota_l \, sans(l e t) \( h \) ; pi_l times iota_r \]\
   & = sans(l e t) \( f \) ; delta^(- 1) ; \( A times B \) + \( sans(l e t) \( h \) ; pi_l times C' \) ; delta\
   & = sans(l e t) \( f \) ; delta^(- 1) ; \( A times B \) + sans(r l e t) \( h \) ; delta $
  and
  $ sans(l e t) \( sans(l e t) \( f \) ; delta^(- 1) ; g + pi_r \) & = sans(l e t) \( f \) ; delta^(- 1) ; \[ sans(l e t) \( g \) ; pi_l times iota_l \, A times iota_r \]\
   & = sans(l e t) \( f \) ; delta^(- 1) ; \( sans(l e t) \( g \) ; pi_l times B' \) + \( A times C \) ; delta\
   & = sans(l e t) \( f \) ; delta^(- 1) ; sans(r l e t) \( g \) + \( A times C \) ; delta $

]
<proof:weakening>

#block[
#emph[Proof.] To show that variable weakenings compose #todo[Resolve source reference `itm:varwk` during integration.], we
proceed by induction on the derivation of $Gamma lt.eq Gamma'$ as
follows:

- wk-nil: if $Gamma \, Gamma' = dot.op$, then $Delta = dot.op$, and so
  we trivially have
  $bracket.l dot.op lt.eq dot.op bracket.r ; bracket.l dot.op lt.eq dot.op bracket.r = bracket.l dot.op lt.eq dot.op bracket.r = sans(i d)$

- wk-skip: we have $Gamma = Xi \, x : A$, and so by induction
  $ bracket.l Xi \, x : A lt.eq Gamma' bracket.r ; bracket.l Gamma' lt.eq Delta bracket.r = pi_l ; bracket.l Xi lt.eq Gamma' bracket.r ; bracket.l Gamma' lt.eq Delta bracket.r = pi_l ; bracket.l Xi lt.eq Delta bracket.r = bracket.l Xi \, x : A lt.eq Delta bracket.r $
  as desired

- wk-cons: we have $Gamma = Xi \, x : A$ and $Gamma' = Xi' \, x : A$. We
  proceed by case analysis on $Gamma' lt.eq Delta$:

  - wk-skip: we have
    $ bracket.l Xi \, x : A lt.eq Xi' \, x : A bracket.r ; bracket.l Xi' lt.eq Delta bracket.r & = bracket.l Xi lt.eq Xi' bracket.r times bracket.l A bracket.r ; bracket.l Xi' \, x : A lt.eq Delta bracket.r\
     & = bracket.l Xi lt.eq Xi' bracket.r times bracket.l A bracket.r ; pi_l ; bracket.l Xi' lt.eq Delta bracket.r\
     & = pi_l ; bracket.l Xi lt.eq Xi' bracket.r ; bracket.l Xi' lt.eq Delta bracket.r\
     & = pi_l ; bracket.l Xi lt.eq Delta bracket.r\
     & = bracket.l Xi \, x : A lt.eq Delta bracket.r $ as
    desired

  - wk-cons: we have $Delta = Delta' \, x : A$, and so by induction
    $ bracket.l Xi \, x : A lt.eq Xi' \, x : A bracket.r ; bracket.l Xi' \, x : A lt.eq Delta' \, x : A bracket.r & = bracket.l Xi lt.eq Xi' bracket.r times bracket.l A bracket.r ; bracket.l Xi' lt.eq Delta' bracket.r times bracket.l A bracket.r\
     & = \( bracket.l Xi lt.eq Xi' bracket.r ; bracket.l Xi' lt.eq Delta' bracket.r \) times bracket.l A bracket.r\
     & = bracket.l Xi lt.eq Delta' bracket.r times bracket.l A bracket.r\
     & = bracket.l Xi \, x : A lt.eq Delta bracket.r $ as
    desired

We can analogously show #todo[Resolve source reference `itm:lbwk` during integration.] (i.e., that label weakenings compose)
by induction on the derivation of $sans(L) lt.eq sans(K)$ as follows:

- lwk-nil: if $sans(L) = sans(K) = dot.op$, then $sans(L)' = dot.op$, so
  the result follows trivially from the fact that
  $bracket.l dot.op bracket.r = upright(bold(sans(L)'))$
  is the initial object

- lwk-skip: we have $sans(K) = sans(K)' \, ell \( A \)$, and therefore
  $ bracket.l sans(L)' lt.eq sans(L) bracket.r ; bracket.l sans(L) lt.eq sans(K)' \, ell \( A \) bracket.r = bracket.l sans(L)' lt.eq sans(L) bracket.r ; bracket.l sans(L) lt.eq sans(K)' bracket.r ; iota_r = bracket.l sans(L)' lt.eq sans(K)' bracket.r ; iota_r = bracket.l sans(L)' lt.eq sans(K) bracket.r $

- lwk-cons: we have $sans(L) = sans(R) \, ell \( A \)$ and
  $sans(K) = sans(K)' \, ell \( A \)$. We proceed by case splitting on
  $sans(L) lt.eq sans(K)'$:

  - lwk-skip: we have
    $ bracket.l sans(L)' lt.eq sans(R) \, ell \( A \) bracket.r ; bracket.l sans(R) \, ell \( A \) lt.eq sans(K)' \, ell \( A \) bracket.r & = bracket.l sans(L)' lt.eq sans(R) bracket.r ; iota_r ; bracket.l sans(R) lt.eq sans(K)' bracket.r + bracket.l A bracket.r\
     & = bracket.l sans(L)' lt.eq sans(R) bracket.r ; bracket.l sans(R) lt.eq sans(K)' bracket.r ; iota_r\
     & = bracket.l sans(L)' lt.eq sans(K)' bracket.r ; iota_r\
     & = bracket.l sans(L)' lt.eq sans(K)' \, ell \( A \) bracket.r $

  - lwk-cons: we have that $sans(L)' = sans(R)' \, ell \( A \)$, and
    therefore
    $ bracket.l sans(R)' \, ell \( A \) lt.eq sans(R) \, ell \( A \) bracket.r ; bracket.l sans(R) \, ell \( A \) lt.eq sans(K)' \, ell \( A \) bracket.r & = bracket.l sans(R)' lt.eq sans(R) bracket.r + bracket.l A bracket.r ; bracket.l sans(R) lt.eq sans(K)' bracket.r + bracket.l A bracket.r\
     & = \( bracket.l sans(R)' lt.eq sans(R) bracket.r ; bracket.l sans(R) lt.eq sans(K)' bracket.r \) + bracket.l A bracket.r\
     & = bracket.l sans(R)' lt.eq sans(K)' bracket.r + bracket.l A bracket.r\
     & = bracket.l sans(R)' \, ell \( A \) lt.eq sans(K)' \, ell \( A \) bracket.r $

We can now show weakening for expressions
$Delta tack.r_epsilon.alt a : A$ #todo[Resolve source reference `itm:expwk` during integration.] by induction on the typing
derivation as follows:

- var: we need to show that
  $ bracket.l Gamma lt.eq Delta bracket.r ; bracket.l Delta tack.r_epsilon.alt x : A bracket.r = bracket.l Gamma lt.eq Delta bracket.r ; pi_(Delta \, x) = bracket.l Gamma tack.r_epsilon.alt x : A bracket.r = pi_(Gamma \, x) $
  we proceed by induction on $Gamma lt.eq Delta$:

  - wk-nil: this case yields a contradiction, since if $Delta = dot.op$
    it cannot define $x$.

  - wk-cons: given $Gamma = Gamma' \, y : B$, $Delta = Delta' \, y : B$,

    - If $x = y$, then $B = A$, and
      $ bracket.l Gamma' \, x : A lt.eq Delta' \, x : A bracket.r ; pi_(\( Delta \, x : A \) \, x) = bracket.l Gamma' lt.eq Delta' bracket.r times bracket.l A bracket.r ; pi_r = pi_r = pi_(\( Gamma \, x : A \) \, x) $
      as desired.

    - Otherwise, we have by induction that
      $ bracket.l Gamma' \, y : B lt.eq Delta' \, y : B bracket.r ; pi_(\( Delta' \, y : B \) \, x) & = bracket.l Gamma' lt.eq Delta' bracket.r times bracket.l B bracket.r ; pi_l ; pi_(Delta' \, x)\
       & = pi_l ; bracket.l Gamma' lt.eq Delta' bracket.r ; pi_(Delta' \, x) = pi_l ; pi_(Gamma' \, x) = pi_(Gamma \, x) $

  - wk-skip: we have $Gamma = Gamma' \, y : B$, and hence
    $ bracket.l Gamma' \, y : B lt.eq Delta bracket.r ; pi_(Delta \, x) = pi_l ; bracket.l Gamma' lt.eq Delta bracket.r ; pi_(Delta \, x) = pi_l ; pi_(Gamma' \, x) = pi_(Gamma \, x) $

- let$""_1$: we have
  $  & bracket.l Gamma lt.eq Delta bracket.r ; bracket.l Delta tack.r_epsilon.alt sans(l e t) #h(0em) x = a ; #h(0em) b : B bracket.r\
   & = bracket.l Gamma lt.eq Delta bracket.r ; sans(l e t) \( bracket.l Delta tack.r_epsilon.alt a : A bracket.r \) ; bracket.l Delta \, x : A tack.r_epsilon.alt b : B bracket.r\
   & = sans(l e t) \( bracket.l Gamma lt.eq Delta bracket.r ; bracket.l Delta tack.r_epsilon.alt a : A bracket.r \) ; bracket.l Gamma lt.eq Delta bracket.r times bracket.l A bracket.r ; bracket.l Delta \, x : A tack.r_epsilon.alt b : B bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A bracket.r \) ; bracket.l Gamma \, x : A lt.eq Delta \, x : A bracket.r ; bracket.l Delta \, x : A tack.r_epsilon.alt b : B bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A bracket.r \) ; bracket.l Gamma \, x : A tack.r_epsilon.alt b : B bracket.r\
   & = bracket.l Gamma tack.r_epsilon.alt sans(l e t) #h(0em) x = a ; #h(0em) b : B bracket.r $

- unit: follows immediately since weakenings are pure and
  $upright(bold(1))$ is the terminal object.

- pair: we have
  $  & bracket.l Gamma lt.eq Delta bracket.r ; bracket.l Delta tack.r_epsilon.alt \( a \, b \) : A times B bracket.r\
   & = bracket.l Gamma lt.eq Delta bracket.r ; Delta_Delta ; bracket.l Delta tack.r_epsilon.alt a : A bracket.r times bracket.l Delta tack.r_epsilon.alt b : B bracket.r\
   & = Delta_Gamma ; \( bracket.l Gamma lt.eq Delta bracket.r ; bracket.l Delta tack.r_epsilon.alt a : A bracket.r \) times \( bracket.l Gamma lt.eq Delta bracket.r ; bracket.l Delta tack.r_epsilon.alt b : B bracket.r \)\
   & = Delta_Gamma ; bracket.l Gamma tack.r_epsilon.alt a : A bracket.r times bracket.l Gamma tack.r_epsilon.alt b : B bracket.r\
   & = bracket.l Gamma tack.r_epsilon.alt \( a \, b \) : A times B bracket.r $

- let$""_2$: we have
  $  & bracket.l Gamma lt.eq Delta bracket.r ; bracket.l Delta tack.r_epsilon.alt sans(l e t) #h(0em) \( x \, y \) = a ; #h(0em) b : B bracket.r\
   & = bracket.l Gamma lt.eq Delta bracket.r ; sans(l e t) \( bracket.l Delta tack.r_epsilon.alt a : A times B bracket.r \) ; alpha ; bracket.l Delta \, x : A \, y : B tack.r_epsilon.alt b : B bracket.r\
   & = sans(l e t) \( bracket.l Gamma lt.eq Delta bracket.r ; bracket.l Delta tack.r_epsilon.alt a : A times B bracket.r \) ; alpha ; bracket.l Gamma lt.eq Delta bracket.r times bracket.l A bracket.r times bracket.l B bracket.r ; bracket.l Delta \, x : A \, y : B tack.r_epsilon.alt b : B bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A times B bracket.r \) ; alpha ; bracket.l Gamma \, x : A \, y : B lt.eq Delta \, x : A \, y : B bracket.r ; bracket.l Delta \, x : A \, y : B tack.r_epsilon.alt b : B bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A times B bracket.r \) ; alpha ; bracket.l Gamma \, x : A \, y : B tack.r_epsilon.alt b : B bracket.r\
   & = bracket.l Gamma tack.r_epsilon.alt sans(l e t) #h(0em) \( x \, y \) = a ; #h(0em) b : B bracket.r $

- case: we have
  $  & bracket.l Gamma lt.eq Delta bracket.r ; bracket.l Delta tack.r_epsilon.alt sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) x : s \, iota_r #h(0em) y : t } : B bracket.r\
   & = bracket.l Gamma lt.eq Delta bracket.r ; sans(l e t) \( bracket.l Delta tack.r_epsilon.alt a : A bracket.r \) ; delta^(- 1) ; \[ bracket.l Delta \, x : A tack.r_epsilon.alt s : B bracket.r \, bracket.l Delta \, y : A tack.r_epsilon.alt t : B bracket.r \]\
   & = sans(l e t) \( bracket.l Gamma lt.eq Delta bracket.r ; bracket.l Gamma tack.r_epsilon.alt a : A bracket.r \) ; delta^(- 1) ;\
   & #h(2em) \[ bracket.l Gamma lt.eq Delta bracket.r times bracket.l A bracket.r ; bracket.l Delta \, x : A tack.r_epsilon.alt s : C bracket.r \, bracket.l Gamma lt.eq Delta bracket.r times bracket.l B bracket.r ; bracket.l Delta \, y : B tack.r_epsilon.alt t : C bracket.r \]\
   & = sans(l e t) \( bracket.l Delta tack.r_epsilon.alt a : A bracket.r \) ;\
   & #h(2em) \[ bracket.l Gamma \, x : A lt.eq Delta \, x : A bracket.r ; bracket.l Delta \, x : A tack.r_epsilon.alt s : C bracket.r \, bracket.l Gamma \, y : B lt.eq Delta \, y : B bracket.r ; bracket.l Delta \, y : B tack.r_epsilon.alt t : C bracket.r \]\
   & = sans(l e t) \( bracket.l Delta tack.r_epsilon.alt a : A bracket.r \) ; \[ bracket.l Gamma \, x : A tack.r_epsilon.alt s : C bracket.r \, bracket.l Gamma \, y : B tack.r_epsilon.alt t : C bracket.r \] $

- op: we have
  $ bracket.l Gamma lt.eq Delta bracket.r ; bracket.l Gamma tack.r_epsilon.alt f #h(0em) a : B bracket.r & = bracket.l Gamma lt.eq Delta bracket.r ; bracket.l Delta tack.r_epsilon.alt a : A bracket.r ; bracket.l f in cal(I)_epsilon.alt \( A \, B \) bracket.r\
   & = bracket.l Gamma tack.r_epsilon.alt a : A bracket.r ; bracket.l f in cal(I)_epsilon.alt \( A \, B \) bracket.r\
   & = bracket.l Gamma tack.r_epsilon.alt f #h(0em) a : B bracket.r $

- inl, inr: analogous to the op case

Similarly, we can show weakening for regions
$Delta tack.r r gt.tri sans(L)$ #todo[Resolve source reference `itm:regwk` during integration.] by induction on the typing
derivation as follows:

- br: we have that
  $ bracket.l Gamma lt.eq Delta bracket.r ; bracket.l Delta tack.r sans(b r) #h(0em) ell #h(0em) a gt.tri sans(L) bracket.r ; bracket.l sans(L) lt.eq sans(K) bracket.r & = bracket.l Gamma lt.eq Delta bracket.r ; bracket.l Delta tack.r_tack.t a : A bracket.r ; iota_(sans(L) \, ell) ; bracket.l sans(L) lt.eq sans(K) bracket.r\
   & = bracket.l Gamma tack.r_tack.t a : A bracket.r ; iota_(sans(L) \, ell) ; bracket.l sans(L) lt.eq sans(K) bracket.r $
  It hence suffices to show that
  $iota_(sans(L) \, ell) ; bracket.l sans(L) lt.eq sans(K) bracket.r = iota_(sans(K) \, ell)$,
  which we can do by induction on $sans(L) lt.eq sans(K)$:

  - lwk-nil: this case yields a contradiction, since if
    $sans(K) = dot.op$ it cannot define the label $ell$.

  - lwk-skip: we have $sans(K) = sans(K)' \, kappa \( B \)$, and hence
    $ iota_(sans(L)' \, ell) ; bracket.l sans(L) lt.eq sans(K)' \, kappa \( B \) bracket.r = iota_(sans(L)' \, ell) ; bracket.l sans(L) lt.eq sans(K)' \, kappa \( B \) bracket.r ; iota_l = iota_(sans(K)' \, ell) ; iota_l = iota_(sans(K) \, ell) $

  - lwk-cons: we have $sans(L) = sans(L)' \, kappa \( B \)$ and
    $sans(K) = sans(K)' \, kappa \( B \)$ .

    - If $kappa = ell$, then $B = A$ and
      $ iota_(\( sans(L)' \, ell \( A \) \) \, ell) ; bracket.l sans(L) \, ell \( A \) lt.eq sans(K)' \, ell \( A \) bracket.r = iota_r ; bracket.l sans(L)' lt.eq sans(K)' bracket.r + bracket.l A bracket.r = iota_r = iota_(sans(K) \, ell) $

    - Otherwise, we have by induction that
      $ iota_(\( sans(L)' \, kappa \( B \) \) \, ell) ; bracket.l sans(L) \, kappa \( B \) lt.eq sans(K)' \, kappa \( B \) bracket.r & = iota_(sans(L)' \, ell) ; iota_l ; bracket.l sans(L)' lt.eq sans(K)' bracket.r + bracket.l B bracket.r\
       & = iota_(sans(L)' \, ell) ; bracket.l sans(L)' lt.eq sans(K)' bracket.r ; iota_l\
       & = iota_(sans(K)' \, ell) ; iota_l & = iota_(sans(K) \, ell) $

- let$""_1$-r: we have by induction that
  $  & bracket.l Gamma lt.eq Delta bracket.r ; bracket.l Delta tack.r sans(l e t) #h(0em) x = a ; r gt.tri sans(L) bracket.r ; bracket.l sans(L) lt.eq sans(K) bracket.r\
   & = bracket.l Gamma lt.eq Delta bracket.r ; sans(l e t) \( bracket.l Delta tack.r_epsilon.alt a : A bracket.r \) ; bracket.l Delta \, x : A tack.r r gt.tri sans(L) bracket.r ; bracket.l sans(L) lt.eq sans(K) bracket.r\
   & = sans(l e t) \( bracket.l Gamma lt.eq Delta bracket.r ; bracket.l Delta tack.r_epsilon.alt a : A bracket.r \) ; bracket.l Gamma lt.eq Delta bracket.r times bracket.l A bracket.r ; bracket.l Delta \, x : A tack.r r gt.tri sans(L) bracket.r ; bracket.l sans(L) lt.eq sans(K) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A bracket.r \) ; bracket.l Gamma \, x : A lt.eq Delta \, x : A bracket.r ; bracket.l Delta \, x : A tack.r r gt.tri sans(L) bracket.r ; bracket.l sans(L) lt.eq sans(K) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A bracket.r \) ; bracket.l Gamma \, x : A tack.r r gt.tri sans(K) bracket.r\
   & = bracket.l Gamma tack.r sans(l e t) #h(0em) x = a ; r gt.tri sans(K) bracket.r $

- let$""_2$-r: we have by induction that
  $  & bracket.l Gamma lt.eq Delta bracket.r ; bracket.l Delta tack.r sans(l e t) #h(0em) \( x \, y \) = a ; r gt.tri sans(L) bracket.r ; bracket.l sans(L) lt.eq sans(K) bracket.r\
   & = bracket.l Gamma lt.eq Delta bracket.r ; sans(l e t) \( bracket.l Delta tack.r_epsilon.alt a : A times B bracket.r \) ; alpha ; bracket.l Delta \, x : A \, y : B tack.r r gt.tri sans(L) bracket.r ; bracket.l sans(L) lt.eq sans(K) bracket.r\
   & = sans(l e t) \( bracket.l Gamma lt.eq Delta bracket.r ; bracket.l Delta tack.r_epsilon.alt a : A times B bracket.r \) ; alpha ; bracket.l Gamma lt.eq Delta bracket.r times bracket.l A bracket.r times bracket.l B bracket.r ; bracket.l Delta \, x : A \, y : B tack.r r gt.tri sans(L) bracket.r ; bracket.l sans(L) lt.eq sans(K) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A times B bracket.r \) ; alpha ; bracket.l Gamma \, x : A \, y : B lt.eq Delta \, x : A \, y : B bracket.r ; bracket.l Delta \, x : A \, y : B tack.r r gt.tri sans(L) bracket.r ; bracket.l sans(L) lt.eq sans(K) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A times B bracket.r \) ; alpha ; bracket.l Gamma \, x : A \, y : B tack.r r gt.tri sans(K) bracket.r $

- case-r: we have by induction that
  $  & bracket.l Gamma lt.eq Delta bracket.r ; bracket.l Delta tack.r sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) x : r \, iota_r #h(0em) y : s } gt.tri sans(L) bracket.r ; bracket.l sans(L) lt.eq sans(K) bracket.r\
   & = bracket.l Gamma lt.eq Delta bracket.r ; sans(l e t) \( bracket.l Delta tack.r_epsilon.alt a : A bracket.r \) ; delta^(- 1) ;\
   & #h(2em) \[ bracket.l Delta \, x : A tack.r s gt.tri sans(L) bracket.r \, bracket.l Delta \, y : B tack.r t gt.tri sans(L) bracket.r \] ; bracket.l sans(L) lt.eq sans(K) bracket.r\
   & = sans(l e t) \( bracket.l Gamma lt.eq Delta bracket.r ; bracket.l Delta tack.r_epsilon.alt a : A bracket.r \) ; delta^(- 1) ; \[\
   & #h(2em) bracket.l Gamma lt.eq Delta bracket.r times bracket.l A bracket.r ; bracket.l Delta \, x : A tack.r s gt.tri sans(L) bracket.r ; bracket.l sans(L) lt.eq sans(K) bracket.r \,\
   & #h(2em) bracket.l Gamma lt.eq Delta bracket.r times bracket.l B bracket.r ; bracket.l Delta \, y : B tack.r t gt.tri sans(L) bracket.r ; bracket.l sans(L) lt.eq sans(K) bracket.r \]\
   & = sans(l e t) \( bracket.l Gamma lt.eq Delta bracket.r ; bracket.l Delta tack.r_epsilon.alt a : A bracket.r \) ; delta^(- 1) ; \[\
   & #h(2em) bracket.l Gamma \, x : A lt.eq Delta \, x : A bracket.r ; bracket.l Delta \, x : A tack.r s gt.tri sans(L) bracket.r ; bracket.l sans(L) lt.eq sans(K) bracket.r \,\
   & #h(2em) bracket.l Gamma \, y : B lt.eq Delta \, y : B bracket.r ; bracket.l Delta \, y : B tack.r t gt.tri sans(L) bracket.r ; bracket.l sans(L) lt.eq sans(K) bracket.r \]\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A bracket.r \) ; delta^(- 1) ; \[ bracket.l Gamma \, x : A tack.r s gt.tri sans(K) bracket.r \, bracket.l Gamma \, y : B tack.r t gt.tri sans(K) bracket.r \]\
   & = bracket.l Gamma tack.r sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) x : s \, iota_r #h(0em) y : t } gt.tri sans(K) bracket.r $

- cfg: Let
  $L = sans(l s e m)_(Delta \, sans(L)) \( \( ell_i \( x_i \) : { t_i } \, \)_i \)$
  and $sans(R) = \( ell_i \( A_i \) \, \)_i$. We have by induction that
  $  & bracket.l Gamma lt.eq Delta bracket.r ; L ; bracket.l sans(L) lt.eq sans(K) bracket.r + Sigma_i bracket.l A_i bracket.r\
   & = bracket.l Gamma lt.eq Delta bracket.r ; delta_Sigma^(- 1) ; \[ \( bracket.l Delta \, x_i : A_i tack.r t_i gt.tri sans(L) \, sans(R) bracket.r \, \)_i \] ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+) ; bracket.l sans(L) lt.eq sans(K) bracket.r + Sigma_i bracket.l A_i bracket.r\
   & = delta_Sigma^(- 1) ; \[ bracket.l Gamma lt.eq Delta bracket.r times bracket.l A_i bracket.r ; \( bracket.l Delta \, x_i : A_i tack.r t_i gt.tri sans(L) \, sans(R) bracket.r ; alpha_(bracket.l sans(L) bracket.r + bracket.l sans(R) bracket.r) ; bracket.l sans(L) lt.eq sans(K) bracket.r + bracket.l sans(R) bracket.r \, \)_i \] ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+)\
   & = delta_Sigma^(- 1) ; \[ \( bracket.l Gamma \, x_i : A_i lt.eq Delta \, x_i : A_i bracket.r ; bracket.l Delta \, x_i : A_i tack.r t_i gt.tri sans(L) \, sans(R) bracket.r ; bracket.l sans(L) \, sans(R) lt.eq sans(K) \, sans(R) bracket.r \, \)_i \] ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+)\
   & = delta_Sigma^(- 1) ; \[ \( bracket.l Gamma \, x_i : A_i tack.r t_i gt.tri sans(K) \, sans(R) bracket.r \, \)_i \] ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+)\
   & = sans(l s e m)_(Gamma \, sans(K)) \( \( ell_i \( x_i \) : { t_i } \, \)_i \) $
  It follows that
  $  & bracket.l Gamma lt.eq Delta bracket.r ; bracket.l Delta tack.r r #h(0em) sans(w h e r e) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i gt.tri sans(L) bracket.r ; bracket.l sans(L) lt.eq sans(K) bracket.r\
   & = bracket.l Gamma lt.eq Delta bracket.r ; sans(l e t) \( bracket.l Delta tack.r r gt.tri sans(L) \, sans(R) bracket.r \) ; bracket.l Delta bracket.r times alpha_(bracket.l L bracket.r + Sigma_i bracket.l A_i bracket.r)^(+) \) ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( L \) \] ; bracket.l sans(L) lt.eq sans(K) bracket.r\
   & = sans(l e t) \( bracket.l Gamma lt.eq Delta bracket.r ; bracket.l Delta tack.r r gt.tri sans(L) \, sans(R) bracket.r ; alpha_(bracket.l L bracket.r + Sigma_i bracket.l A_i bracket.r)^(+) \) ; delta^(- 1) ; \[ pi_r \, bracket.l Gamma lt.eq Delta bracket.r ; sans(r f i x) \( L \) \] ; bracket.l sans(L) lt.eq sans(K) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r r gt.tri sans(L) \, sans(R) bracket.r ; alpha_(bracket.l L bracket.r + Sigma_i bracket.l A_i bracket.r)^(+) \) ; \[ pi_r ; bracket.l sans(L) lt.eq sans(K) bracket.r \, sans(r f i x) \( sans(l s e m)_(Gamma \, sans(K)) \( \( ell_i \( x_i \) : { t_i } \, \)_i \) \) \]\
   & = sans(l e t) \( bracket.l Gamma tack.r r gt.tri sans(L) \, sans(R) bracket.r ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r) ; bracket.l sans(L) lt.eq sans(K) bracket.r + Sigma_i bracket.l A_i bracket.r \) ; \[ pi_r \, sans(r f i x) \( sans(l s e m)_(Gamma \, sans(K)) \( \( ell_i \( x_i \) : { t_i } \, \)_i \) \) \]\
   & = sans(l e t) \( bracket.l Gamma tack.r r gt.tri sans(L) \, sans(R) bracket.r ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r) ; bracket.l sans(L) lt.eq sans(K) bracket.r + Sigma_i bracket.l A_i bracket.r \) ; \[ pi_r \, sans(r f i x) \( sans(l s e m)_(Gamma \, sans(K)) \( \( ell_i \( x_i \) : { t_i } \, \)_i \) \) \]\
   & = sans(l e t) \( bracket.l Gamma tack.r r gt.tri sans(L) \, sans(R) bracket.r ; bracket.l sans(L) \, sans(R) lt.eq sans(K) \, sans(R) bracket.r ; alpha_(bracket.l sans(K) bracket.r + Sigma_i bracket.l A_i bracket.r) \) ; \[ pi_r \, sans(r f i x) \( sans(l s e m)_(Gamma \, sans(K)) \( \( ell_i \( x_i \) : { t_i } \, \)_i \) \) \]\
   & = sans(l e t) \( bracket.l Gamma tack.r r gt.tri sans(K) \, sans(R) bracket.r ; alpha_(bracket.l sans(K) bracket.r + Sigma_i bracket.l A_i bracket.r) \) ; \[ pi_r \, sans(r f i x) \( sans(l s e m)_(Gamma \, sans(K)) \( \( ell_i \( x_i \) : { t_i } \, \)_i \) \) \]\
   & = bracket.l Gamma tack.r r #h(0em) sans(w h e r e) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i gt.tri sans(K) bracket.r $

Weakening for substitutions #todo[Resolve source reference `itm:substwk` during integration.] and label substitututions
#todo[Resolve source reference `itm:lbsubstwk` during integration.] then follow by a trivial induction.~◻

]
#block[
For $gamma : Gamma mapsto Delta$, $sans(e f f) \( Delta \) = tack.t$ and
$Delta \( x \) = A$, we have
$ bracket.l gamma : Gamma mapsto Delta bracket.r ; pi_(Delta \, x) = bracket.l Gamma tack.r_epsilon.alt \[ gamma \] x : A bracket.r $
<lem:subst-proj>

]
#block[
#emph[Proof.] We proceed by induction on $Delta$:

- If $Delta = dot.op$, then $Delta \( x \) = A$ is a contradiction.

- If $Delta = Delta' \, x : A$, then
  $gamma = gamma' \, x mapsto \[ gamma \] x$, so we have
  $ bracket.l gamma : Gamma mapsto Delta bracket.r ; pi_(Delta \, x) = Delta_(bracket.l Gamma bracket.r) ; bracket.l gamma' : Gamma mapsto Delta' bracket.r times bracket.l Gamma tack.r_tack.t \[ gamma \] x : A bracket.r ; pi_r = bracket.l Gamma tack.r_epsilon.alt \[ gamma \] x : A bracket.r $
  as desired.

- If $Delta = Delta' \, y : B$ (with $y eq.not x$), then
  $gamma = gamma' \, y mapsto \[ gamma \] y$, so by induction we have
  $ bracket.l gamma : Gamma mapsto Delta bracket.r ; pi_(Delta \, x) & = Delta_(bracket.l Gamma bracket.r) ; bracket.l gamma' : Gamma mapsto Delta' bracket.r times bracket.l Gamma tack.r_tack.t \[ gamma \] y : B bracket.r ; pi_l ; pi_(Delta' \, x)\
   & = bracket.l gamma' : Gamma mapsto Delta' bracket.r ; pi_(Delta' \, x) = bracket.l Gamma tack.r_epsilon.alt \[ gamma' \] x : A bracket.r = bracket.l Gamma tack.r_epsilon.alt \[ gamma \] x : A bracket.r $

~◻

]
<proof:soundness-subst>

#block[
#emph[Proof.] Fix $gamma : Gamma mapsto Delta$ with
$sans(e f f) \( Delta \) = tack.t$. We will begin by showing the
soundness of substitution for expressions #todo[Resolve source reference `itm:tm-subst-sound:` during integration.] we
proceed by induction on the derivation $Delta tack.r_epsilon.alt e : E$:

- If $e = x$ is a variable, then by Lemma~#todo[Resolve source reference `lem:subst-proj` during integration.], we have
  $ bracket.l gamma : Gamma mapsto Delta bracket.r ; bracket.l Delta tack.r_epsilon.alt x : A bracket.r = bracket.l gamma : Gamma mapsto Delta bracket.r ; pi_(Delta \, x) = bracket.l Gamma tack.r_epsilon.alt \[ gamma \] x : A bracket.r $
  as desired.

- If $e = f #h(0em) a$ is an operation, then by induction we have that
  $ bracket.l gamma : Gamma mapsto Delta bracket.r ; bracket.l Gamma tack.r_epsilon.alt f #h(0em) a : B bracket.r & = bracket.l gamma : Gamma mapsto Delta bracket.r ; bracket.l Delta tack.r_epsilon.alt a : A bracket.r ; bracket.l f in cal(I)_B \( epsilon.alt \, A \) bracket.r\
   & = bracket.l Gamma tack.r_epsilon.alt \[ gamma \] a : A bracket.r ; bracket.l f in cal(I)_B \( epsilon.alt \, A \) bracket.r = bracket.l Gamma tack.r_epsilon.alt \[ gamma \] \( f #h(0em) a \) : B bracket.r $
  as desired. The cases for left injections, right injections, and
  $sans(a b o r t)$ are analogous

- If $e = \( sans(l e t) #h(0em) x = a ; #h(0em) b \)$ is a unary
  $sans(l e t)$-binding, then by induction we have that
  $  & bracket.l gamma : Gamma mapsto Delta bracket.r times bracket.l A bracket.r ; bracket.l Delta \, x : A tack.r_epsilon.alt b : B bracket.r\
   & = bracket.l \( gamma \, x mapsto x \) : \( Gamma \, x : A \) mapsto \( Delta \, x : A \) bracket.r ; bracket.l Delta \, x : A tack.r_epsilon.alt b : B bracket.r\
   & = bracket.l Gamma \, x : A tack.r_epsilon.alt \[ gamma \, x mapsto x \] b : B bracket.r = bracket.l Gamma \, x : A tack.r_epsilon.alt \[ gamma \] b : B bracket.r $
  as we can assume that $x$ is a fresh variable. Hence, it follows that
  $  & bracket.l gamma : Gamma mapsto Delta bracket.r ; bracket.l Delta tack.r_epsilon.alt sans(l e t) #h(0em) x = a ; #h(0em) b : B bracket.r\
   & = bracket.l gamma : Gamma mapsto Delta bracket.r ; Delta_(bracket.l Delta bracket.r) ; bracket.l Delta bracket.r times bracket.l Delta tack.r_epsilon.alt a : A bracket.r ; bracket.l Delta \, x : A tack.r_epsilon.alt b : B bracket.r\
   & = Delta_(bracket.l Gamma bracket.r) ; bracket.l Gamma bracket.r times bracket.l Gamma tack.r_epsilon.alt \[ gamma \] a : A bracket.r ; bracket.l gamma : Gamma mapsto Delta bracket.r times bracket.l A bracket.r ; bracket.l Delta \, x : A tack.r_epsilon.alt b : B bracket.r\
   & = Delta_(bracket.l Gamma bracket.r) ; bracket.l Gamma bracket.r times bracket.l Gamma tack.r_epsilon.alt \[ gamma \] a : A bracket.r ; bracket.l Gamma \, x : A tack.r_epsilon.alt \[ gamma \] b : B bracket.r\
   & = bracket.l Gamma tack.r_epsilon.alt \[ gamma \] \( sans(l e t) #h(0em) x = a ; #h(0em) b \) : B bracket.r $
  as desired.

- If $e = \( a \, b \)$ is a pair, then by induction we have that
  $  & bracket.l gamma : Gamma mapsto Delta bracket.r ; bracket.l Delta tack.r_epsilon.alt \( a \, b \) : A times B bracket.r\
   & = bracket.l gamma : Gamma mapsto Delta bracket.r ; Delta_(bracket.l Delta bracket.r) ; bracket.l Delta tack.r_epsilon.alt a : A bracket.r times.l bracket.l Delta tack.r_epsilon.alt b : B bracket.r\
   & = Delta_(bracket.l Gamma bracket.r) ; \( bracket.l gamma : Gamma mapsto Delta bracket.r times bracket.l Delta tack.r_epsilon.alt a : A bracket.r \) times.l \( bracket.l gamma : Gamma mapsto Delta bracket.r times bracket.l Delta tack.r_epsilon.alt b : B bracket.r \)\
   & = Delta_(bracket.l Gamma bracket.r) ; bracket.l Gamma tack.r_epsilon.alt \[ gamma \] a : A bracket.r times.l bracket.l Gamma tack.r_epsilon.alt \[ gamma \] b : B bracket.r = bracket.l Gamma tack.r_epsilon.alt \[ gamma \] \( a \, b \) : A times B bracket.r $

- If $e = \( sans(l e t) #h(0em) \( x \, y \) = a ; #h(0em) b \)$ is a
  binary $sans(l e t)$-binding, then by induction we have that
  $  & bracket.l gamma : Gamma mapsto Delta bracket.r times \( bracket.l A bracket.r times bracket.l B bracket.r \) ; alpha ; bracket.l Delta \, x : A \, y : B tack.r_epsilon.alt b : C bracket.r\
   & = alpha ; bracket.l \( gamma \, x mapsto x \, y mapsto y \) : \( Gamma \, x : A \, y : B \) mapsto \( Delta \, x : A \, y : B \) bracket.r ; bracket.l Delta \, x : A \, y : B tack.r_epsilon.alt b : C bracket.r\
   & = bracket.l Gamma \, x : A \, y : B tack.r_epsilon.alt \[ gamma \, x mapsto x \, y mapsto y \] b : C bracket.r = bracket.l Gamma \, x : A \, y : B tack.r_epsilon.alt \[ gamma \] b : C bracket.r $
  as we can assume that $x \, y$ are fresh variables. Hence, it follows
  that
  $  & bracket.l gamma : Gamma mapsto Delta bracket.r ; bracket.l Delta tack.r_epsilon.alt sans(l e t) #h(0em) \( x \, y \) = a ; #h(0em) b : C bracket.r\
   & = bracket.l gamma : Gamma mapsto Delta bracket.r ; Delta_(bracket.l Delta bracket.r) ; bracket.l Delta bracket.r times bracket.l Delta tack.r_epsilon.alt a : A times B bracket.r ; alpha ; bracket.l Delta \, x : A \, y : B tack.r_epsilon.alt b : C bracket.r\
   & = Delta_(bracket.l Gamma bracket.r) ; bracket.l Gamma bracket.r times bracket.l Gamma tack.r_epsilon.alt \[ gamma \] a : A times B bracket.r ; bracket.l gamma : Gamma mapsto Delta bracket.r times \( bracket.l A bracket.r times bracket.l B bracket.r \) ; alpha ; bracket.l Delta \, x : A \, y : B tack.r_epsilon.alt b : C bracket.r\
   & = Delta_(bracket.l Gamma bracket.r) ; bracket.l Gamma bracket.r times bracket.l Gamma tack.r_epsilon.alt \[ gamma \] a : A times B bracket.r ; bracket.l Gamma \, x : A \, y : B tack.r_epsilon.alt \[ gamma \] b : C bracket.r\
   & = bracket.l Gamma tack.r_epsilon.alt \[ gamma \] \( sans(l e t) #h(0em) \( x \, y \) = a ; #h(0em) b \) : C bracket.r $
  as desired.

- If
  $e = sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) x : b \, iota_r #h(0em) y : c }$
  is a $sans(c a s e)$-expression, then by induction we have that
  $  & bracket.l gamma : Gamma mapsto Delta bracket.r times bracket.l A bracket.r ; bracket.l Delta \, x : A tack.r_epsilon.alt b : C bracket.r\
   & = bracket.l \( gamma \, x mapsto x \) : \( Gamma \, x : A \) mapsto \( Delta \, x : A \) bracket.r ; bracket.l Delta \, x : A tack.r_epsilon.alt b : C bracket.r\
   & = bracket.l Gamma \, x : A tack.r_epsilon.alt \[ gamma \, x mapsto x \] b : C bracket.r = bracket.l Gamma \, x : A tack.r_epsilon.alt \[ gamma \] b : C bracket.r $
  and
  $  & bracket.l gamma : Gamma mapsto Delta bracket.r times bracket.l B bracket.r ; bracket.l Delta \, y : B tack.r_epsilon.alt c : C bracket.r\
   & = bracket.l \( gamma \, y mapsto y \) : \( Gamma \, y : B \) mapsto \( Delta \, y : B \) bracket.r ; bracket.l Delta \, y : B tack.r_epsilon.alt c : C bracket.r\
   & = bracket.l Gamma \, y : B tack.r_epsilon.alt \[ gamma \, x mapsto x \] c : C bracket.r = bracket.l Gamma \, y : B tack.r_epsilon.alt \[ gamma \] c : C bracket.r $
  as we can assume that $x \, y$ are fresh variables. Hence, it follows
  that
  $  & bracket.l gamma : Gamma mapsto Delta bracket.r ; Delta_(bracket.l Delta bracket.r) ; bracket.l Delta bracket.r times bracket.l Delta tack.r_epsilon.alt a : A + B bracket.r ; delta_(bracket.l Delta bracket.r)^(- 1) ; \[ bracket.l Delta \, x : A tack.r_epsilon.alt b : C bracket.r \, bracket.l Delta \, y : B tack.r_epsilon.alt c : C bracket.r \]\
   & = Delta_(bracket.l Gamma bracket.r) ; bracket.l Gamma bracket.r times bracket.l Gamma tack.r_epsilon.alt \[ gamma \] a : A + B bracket.r ; delta_(bracket.l Gamma bracket.r)^(- 1) ;\
   & #h(2em) \[ bracket.l gamma : Gamma mapsto Delta bracket.r times bracket.l A bracket.r ; bracket.l Delta \, x : A tack.r_epsilon.alt b : C bracket.r \, bracket.l gamma : Gamma mapsto Delta bracket.r times bracket.l B bracket.r ; bracket.l Delta \, y : B tack.r_epsilon.alt c : C bracket.r \]\
   & = Delta_(bracket.l Gamma bracket.r) ; bracket.l Gamma bracket.r times bracket.l Gamma tack.r_epsilon.alt \[ gamma \] a : A + B bracket.r ; delta_(bracket.l Gamma bracket.r)^(- 1) ; \[ bracket.l Gamma \, x : A tack.r_epsilon.alt \[ gamma \] b : C bracket.r \, bracket.l Gamma \, y : B tack.r_epsilon.alt \[ gamma \] c : C bracket.r \]\
   & = bracket.l Gamma tack.r_epsilon.alt \[ gamma \] \( sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) x : b \, iota_r #h(0em) y : c } \) : C bracket.r $
  as desired.

- If $e = \( \)$ is the null expression, since
  $bracket.l gamma : Gamma mapsto Delta bracket.r$ is
  pure, the desired result holds trivially since $upright(bold(1))$ is
  the terminal object in the category of pure morphisms.

We may now prove the soundness of substitution for regions as follows:
assuming $Gamma tack.r r gt.tri sans(L)$, we proceed by induction on $r$
as follows:

- If $r = sans(b r) #h(0em) ell #h(0em) a$, then we have that
  $ bracket.l gamma : Gamma mapsto Delta bracket.r ; bracket.l Delta tack.r sans(b r) #h(0em) ell #h(0em) A gt.tri sans(L) bracket.r & = bracket.l gamma : Gamma mapsto Delta bracket.r ; bracket.l Delta tack.r_tack.t a : A bracket.r ; iota_(sans(L) \, ell)\
   & = bracket.l Gamma tack.r_tack.t \[ gamma \] a : A bracket.r ; iota_(sans(L) \, ell) = bracket.l Gamma tack.r \[ gamma \] \( sans(b r) #h(0em) ell #h(0em) a \) gt.tri sans(L) bracket.r $

- If $r = \( sans(l e t) #h(0em) x = a ; t \)$, then we have that, by
  induction,
  $  & bracket.l gamma : Gamma mapsto Delta bracket.r times bracket.l A bracket.r ; bracket.l Delta \, x : A tack.r t gt.tri sans(L) bracket.r\
   & = bracket.l \( gamma \, x mapsto x \) : \( Gamma \, x : A \) mapsto \( Delta \, x : A \) bracket.r ; bracket.l Delta \, x : A tack.r t gt.tri sans(L) bracket.r\
   & = bracket.l Gamma \, x : A tack.r \[ gamma \, x mapsto x \] t gt.tri sans(L) bracket.r = bracket.l Gamma \, x : A tack.r \[ gamma \] t gt.tri sans(L) bracket.r $
  since $x$ can be taken to be a free variable. Hence,
  $  & bracket.l gamma : Gamma mapsto Delta bracket.r ; bracket.l Delta tack.r sans(l e t) #h(0em) x = a ; #h(0em) t gt.tri sans(L) bracket.r\
   & = bracket.l gamma : Gamma mapsto Delta bracket.r ; Delta_(bracket.l Delta bracket.r) ; bracket.l Delta bracket.r times bracket.l Delta tack.r_epsilon.alt a : A bracket.r ; bracket.l Delta \, x : A tack.r t gt.tri sans(L) bracket.r\
   & = Delta_(bracket.l Gamma bracket.r) ; bracket.l Gamma bracket.r times bracket.l Gamma tack.r_epsilon.alt \[ gamma \] a : A bracket.r ; bracket.l gamma : Gamma mapsto Delta bracket.r times bracket.l A bracket.r ; bracket.l Delta \, x : A tack.r t gt.tri sans(L) bracket.r\
   & = Delta_(bracket.l Gamma bracket.r) ; bracket.l Gamma bracket.r times bracket.l Gamma tack.r_epsilon.alt \[ gamma \] a : A bracket.r ; bracket.l Gamma \, x : A tack.r \[ gamma \] t gt.tri sans(L) bracket.r\
   & = bracket.l Gamma tack.r \[ gamma \] \( sans(l e t) #h(0em) x = a ; #h(0em) t \) gt.tri sans(L) bracket.r $

- If $r = \( sans(l e t) #h(0em) \( x \, y \) = a ; t \)$, then we have
  that, by induction,
  $  & bracket.l gamma : Gamma mapsto Delta bracket.r times \( bracket.l A bracket.r times bracket.l B bracket.r \) ; alpha ; bracket.l Delta \, x : A \, y : B tack.r t gt.tri sans(L) bracket.r\
   & = alpha ; bracket.l \( gamma \, x mapsto x \, y mapsto y \) : \( Gamma \, x : A \, y : B \) mapsto \( Delta \, x : A \, y : B \) bracket.r ; bracket.l Delta \, x : A \, y : B tack.r t gt.tri sans(L) bracket.r\
   & = bracket.l Gamma \, x : A \, y : B tack.r \[ gamma \, x mapsto x \, y mapsto y \] t gt.tri sans(L) bracket.r = bracket.l Gamma \, x : A \, y : B tack.r \[ gamma \] t gt.tri sans(L) bracket.r $
  since $x \, y$ can be taken to be free variables. Hence,
  $  & bracket.l gamma : Gamma mapsto Delta bracket.r ; bracket.l Delta tack.r sans(l e t) #h(0em) \( x \, y \) = a ; #h(0em) t gt.tri sans(L) bracket.r\
   & = bracket.l gamma : Gamma mapsto Delta bracket.r ; Delta_(bracket.l Delta bracket.r) ; bracket.l Delta bracket.r times bracket.l Delta tack.r_epsilon.alt a : A times B bracket.r ; alpha ; bracket.l Delta \, x : A \, y : B tack.r t gt.tri sans(L) bracket.r\
   & = Delta_(bracket.l Gamma bracket.r) ; bracket.l Gamma bracket.r times bracket.l Gamma tack.r_epsilon.alt \[ gamma \] a : A times B bracket.r ; bracket.l gamma : Gamma mapsto Delta bracket.r times \( bracket.l A bracket.r times bracket.l B bracket.r \) ; alpha ; bracket.l Delta \, x : A \, y : B tack.r t gt.tri sans(L) bracket.r\
   & = Delta_(bracket.l Gamma bracket.r) ; bracket.l Gamma bracket.r times bracket.l Gamma tack.r_epsilon.alt \[ gamma \] a : A times B bracket.r ; bracket.l Gamma \, x : A \, y : B tack.r \[ gamma \] t gt.tri sans(L) bracket.r\
   & = bracket.l Gamma tack.r \[ gamma \] \( sans(l e t) #h(0em) \( x \, y \) = a ; #h(0em) t \) gt.tri sans(L) bracket.r $

- If
  $r = sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) x : s \, iota_r #h(0em) y : t }$,
  then we have that, by induction
  $  & bracket.l gamma : Gamma mapsto Delta bracket.r times bracket.l A bracket.r ; bracket.l Delta \, x : A tack.r s gt.tri sans(L) bracket.r\
   & = bracket.l \( gamma \, x mapsto x \) : \( Gamma \, x : A \) mapsto \( Delta \, x : A \) bracket.r ; bracket.l Delta \, x : A tack.r s gt.tri sans(L) bracket.r\
   & = bracket.l Gamma \, x : A tack.r \[ gamma \, x mapsto x \] s gt.tri sans(L) bracket.r = bracket.l Gamma \, x : A tack.r \[ gamma \] s gt.tri sans(L) bracket.r $
  and
  $  & bracket.l gamma : Gamma mapsto Delta bracket.r times bracket.l B bracket.r ; bracket.l Delta \, y : B tack.r t gt.tri sans(L) bracket.r\
   & = bracket.l \( gamma \, y mapsto y \) : \( Gamma \, y : B \) mapsto \( Delta \, y : B \) bracket.r ; bracket.l Delta \, y : B tack.r t gt.tri sans(L) bracket.r\
   & = bracket.l Gamma \, y : B tack.r \[ gamma \, y mapsto y \] t gt.tri sans(L) bracket.r = bracket.l Gamma \, y : B tack.r \[ gamma \] t gt.tri sans(L) bracket.r $
  since $x \, y$ can be taken to be free variables. Hence,
  $  & bracket.l gamma : Gamma mapsto Delta bracket.r ; Delta_(bracket.l Delta bracket.r) ; bracket.l Delta bracket.r times bracket.l Delta tack.r_epsilon.alt a : A + B bracket.r ; delta_(bracket.l Delta bracket.r)^(- 1) ; \[ bracket.l Delta \, x : A tack.r s gt.tri sans(L) bracket.r \, bracket.l Delta \, y : B tack.r t gt.tri sans(L) bracket.r \]\
   & = Delta_(bracket.l Gamma bracket.r) ; bracket.l Gamma bracket.r times bracket.l Gamma tack.r_epsilon.alt \[ gamma \] a : A + B bracket.r ; delta_(bracket.l Gamma bracket.r)^(- 1) ;\
   & #h(2em) \[ bracket.l gamma : Gamma mapsto Delta bracket.r times bracket.l A bracket.r ; bracket.l Delta \, x : A tack.r s gt.tri sans(L) bracket.r \, bracket.l gamma : Gamma mapsto Delta bracket.r times bracket.l B bracket.r ; bracket.l Delta \, y : B tack.r t gt.tri sans(L) bracket.r \]\
   & = Delta_(bracket.l Gamma bracket.r) ; bracket.l Gamma bracket.r times bracket.l Gamma tack.r_epsilon.alt \[ gamma \] a : A + B bracket.r ; delta_(bracket.l Gamma bracket.r)^(- 1) ; \[ bracket.l Gamma \, x : A tack.r \[ gamma \] s gt.tri sans(L) bracket.r \, bracket.l Gamma \, y : B tack.r \[ gamma \] t gt.tri sans(L) bracket.r \]\
   & = bracket.l Gamma tack.r \[ gamma \] \( sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) x : s \, iota_r #h(0em) y : t } \) gt.tri sans(L) bracket.r $
  as desired.

- Assume
  $r = s #h(0em) sans(w h e r e) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i$.
  Define $sans(R) = \( ell_i \( A_i \) \, \)_i$ and
  $S = bracket.l gamma : Gamma mapsto Delta bracket.r$. We
  have by induction that, for all $i$,
  $  & bracket.l gamma : Gamma mapsto Delta bracket.r times bracket.l A_i bracket.r ; bracket.l Delta \, x_i : A_i tack.r t_i gt.tri sans(L) \, sans(R) bracket.r\
   & = bracket.l \( gamma \, x_i mapsto x_i \) : \( Gamma \, x_i : A_i \) mapsto \( Delta \, x_i : A_i \) bracket.r ; bracket.l Delta \, x_i : A_i tack.r t_i gt.tri sans(L) \, sans(R) bracket.r\
   & = bracket.l Gamma \, x_i : A_i tack.r \[ gamma \, x_i mapsto x_i \] t_i gt.tri sans(L) \, sans(R) bracket.r = bracket.l Gamma \, x_i : A_i tack.r \[ gamma \] t_i gt.tri sans(L) \, sans(R) bracket.r $
  and therefore that
  $  & S times Sigma_i bracket.l A_i bracket.r ; sans(l s e m)_(Delta \, sans(L)) \( \( ell_i \( x_i \) : { t_i } \, \)_i \)\
   & = S times Sigma_i bracket.l A_i bracket.r ; delta_Sigma^(- 1) ; \[ bracket.l Delta \, x_i : A_i tack.r t_i gt.tri sans(L) \, sans(R) bracket.r \, \]_i ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+)\
   & = delta_Sigma^(- 1) ; \[ S times bracket.l A_i bracket.r ; bracket.l Delta \, x_i : A_i tack.r t_i gt.tri sans(L) \, sans(R) bracket.r \, \]_i ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+)\
   & = delta_Sigma^(- 1) ; \[ bracket.l Gamma \, x_i : A_i tack.r \[ gamma \] t_i gt.tri sans(L) \, sans(R) bracket.r \, \]_i ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+)\
   & = sans(l s e m)_(Gamma \, sans(L)) \( \( ell_i \( x_i \) : { \[ gamma \] t_i } \, \)_i \) $
  It follows that
  $  & S ; bracket.l Delta tack.r s #h(0em) sans(w h e r e) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i gt.tri sans(L) bracket.r\
   & = S ; sans(l e t) \( bracket.l Delta tack.r s gt.tri sans(L) \, sans(R) bracket.r ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+) \) ; delta^(- 1) ; \[ pi_r \, sans(l s e m)_(Delta \, sans(L)) \( \( ell_i \( x_i \) : { t_i } \, \)_i \) \]\
   & = sans(l e t) \( S ; bracket.l Delta tack.r s gt.tri sans(L) \, sans(R) bracket.r ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+) \) ; S times \( bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r \) ; delta^(- 1) ; \[ pi_r \, sans(l s e m)_(Delta \, sans(L)) \( \( ell_i \( x_i \) : { t_i } \, \)_i \) \]\
   & = sans(l e t) \( bracket.l Gamma tack.r \[ gamma \] s gt.tri sans(L) \, sans(R) bracket.r ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+) \) ; delta^(- 1) ; \[ pi_r \, S times \( bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r \) ; sans(l s e m)_(Delta \, sans(L)) \( \( ell_i \( x_i \) : { t_i } \, \)_i \) \]\
   & = sans(l e t) \( bracket.l Gamma tack.r \[ gamma \] s gt.tri sans(L) \, sans(R) bracket.r ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+) \) ; delta^(- 1) ; \[ pi_r \, sans(l s e m)_(Gamma \, sans(L)) \( \( ell_i \( x_i \) : { \[ gamma \] t_i } \, \)_i \) \]\
   & = bracket.l Gamma tack.r \[ gamma \] s #h(0em) sans(w h e r e) #h(0em) \( ell_i \( x_i \) : { \[ gamma \] t_i } \, \)_i gt.tri sans(L) bracket.r\
   $ as desired.

Composition of substitutions then follows by a trivial induction, as
does substitution for label substitutions.~◻

]
== Label Substitution
<label-substitution>
#block[
For $Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K)$ and
$sans(L) \( ell \) = A$, we have
$ bracket.l Gamma bracket.r times iota_(sans(L) \, ell) ; bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r = bracket.l Gamma \, x : A tack.r \[ gamma \] \( sans(b r) #h(0em) ell #h(0em) x \) gt.tri sans(K) bracket.r $
<lem:lsubst-inj>

]
#block[
#emph[Proof.] We proceed by induction on $sans(L)$:

- If $sans(L) = dot.op$, then $sans(L) \( ell \) = A$ is a contradiction

- If $sans(L) = sans(L)' \, ell \( A \)$, then
  $sigma = sigma' \, ell \( x \) mapsto \[ sigma \] \( sans(b r) #h(0em) ell #h(0em) x \)$,
  so we have
  $  & bracket.l Gamma bracket.r times iota_(sans(L) \, ell) ; bracket.l Gamma tack.r sigma : sans(L) \, ell \( A \) arrow.r.squiggly sans(K) bracket.r\
   & = bracket.l Gamma bracket.r times iota_r ; delta^(- 1) ; \[ bracket.l Gamma tack.r sigma' : sans(L) arrow.r.squiggly sans(K) bracket.r \, bracket.l Gamma \, x : A tack.r \[ sigma \] \( sans(b r) #h(0em) ell #h(0em) x \) gt.tri sans(K) bracket.r \]\
   & = bracket.l Gamma \, x : A tack.r \[ sigma \] \( sans(b r) #h(0em) ell #h(0em) x \) gt.tri sans(K) bracket.r $

- If $sans(L) = sans(L)' \, kappa \( A \)$, then
  $sigma = sigma' \, kappa \( x \) mapsto \[ sigma \] \( sans(b r) #h(0em) kappa #h(0em) x \)$,
  so by induction we have
  $  & bracket.l Gamma bracket.r times iota_(sans(L) \, ell) ; bracket.l Gamma tack.r sigma : sans(L) \, ell \( A \) arrow.r.squiggly sans(K) bracket.r\
   & = bracket.l Gamma bracket.r times \( iota_(sans(L)' \, ell) ; iota_l \) ; delta^(- 1) ; \[ bracket.l Gamma tack.r sigma' : sans(L) arrow.r.squiggly sans(K) bracket.r \, bracket.l Gamma \, x : B tack.r \[ sigma \] \( sans(b r) #h(0em) kappa #h(0em) x \) gt.tri sans(K) bracket.r \]\
   & = bracket.l Gamma bracket.r times iota_(sans(L)' \, ell) ; bracket.l Gamma tack.r sigma' : sans(L) arrow.r.squiggly sans(K) bracket.r\
   & = bracket.l Gamma \, x : A tack.r \[ sigma' \] \( sans(b r) #h(0em) ell #h(0em) x \) gt.tri sans(K) bracket.r\
   & = bracket.l Gamma \, x : A tack.r \[ sigma \] \( sans(b r) #h(0em) ell #h(0em) x \) gt.tri sans(K) bracket.r $

~◻

]
#block[
For $Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K)$, where
$sans(L) = \( ell_i \( A_i \) \, \)_i$, we have
$ bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r = bracket.l Gamma bracket.r times alpha_(Sigma_i bracket.l A_i bracket.r) ; delta_Sigma^(- 1) ; \[ bracket.l Gamma \, x_i : A_i tack.r sigma #h(0em) ell_i #h(0em) x_i gt.tri sans(K) bracket.r \, \]_i $
and therefore
$ delta_Sigma^(- 1) ; \[ bracket.l Gamma \, x_i : A_i tack.r sigma #h(0em) ell_i #h(0em) x_i gt.tri sans(K) bracket.r \, \]_i = alpha_(bracket.l sans(L) bracket.r) ; bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r $
In particular, we have that, given
$forall i \, Gamma \, x_i : A_i tack.r t_i gt.tri sans(K)$,
$ bracket.l Gamma tack.r \( ell_i \( x_i \) : { A_i } \, \)_i \) : sans(L) arrow.r.squiggly sans(K) bracket.r = bracket.l Gamma bracket.r times alpha_(Sigma_i bracket.l A_i bracket.r) ; delta_Sigma^(- 1) ; \[ bracket.l Gamma \, x_i : A_i tack.r t_i gt.tri sans(K) bracket.r \, \]_i $
<lem:lsubst-distrib>

]
#block[
Given $sigma = sigma_l \, sigma_r$,
$Gamma tack.r sigma : sans(L) \, sans(R) arrow.r.squiggly sans(L)' \, sans(R)'$,
$Gamma tack.r sigma_l : sans(L) arrow.r.squiggly sans(L)'$,
$Gamma tack.r sigma_r : sans(R) arrow.r.squiggly sans(R)'$, we have
$ bracket.l Gamma tack.r sigma : sans(L) \, sans(R) arrow.r.squiggly sans(L)' \, sans(R)' bracket.r = bracket.l Gamma bracket.r times alpha_(bracket.l sans(L) bracket.r + bracket.l sans(R) bracket.r) ; bracket.l Gamma tack.r sigma_l : sans(L) arrow.r.squiggly sans(L)' bracket.r + bracket.l Gamma tack.r sigma_r : sans(R) arrow.r.squiggly sans(R)' bracket.r ; alpha_(bracket.l sans(L)' \, sans(R)' bracket.r) $
In particular, for
$Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K)$, we have
$ bracket.l Gamma tack.r sigma^harpoon.tl : sans(R) \, sans(L) arrow.r.squiggly sans(R) \, sans(K) bracket.r = bracket.l Gamma bracket.r times alpha_(bracket.l sans(R) bracket.r + bracket.l sans(L) bracket.r)^(+) ; delta^(- 1) ; pi_r + bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r ; alpha_(bracket.l sans(R) \, sans(K) bracket.r)^(+) $
$ bracket.l Gamma tack.r sigma^harpoon.tr : sans(L) \, sans(R) arrow.r.squiggly sans(K) \, sans(R) bracket.r = bracket.l Gamma bracket.r times alpha_(bracket.l sans(L) bracket.r + bracket.l sans(R) bracket.r)^(+) ; delta^(- 1) ; bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r + pi_r ; alpha_(bracket.l sans(K) \, sans(R) bracket.r)^(+) $
since
$ Gamma tack.r sans(i d) : sans(R) arrow.r.squiggly sans(R) = pi_r $

]
<proof:soundness-lsubst>

#block[
#emph[Proof.] Fix
$Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K)$. We begin by
proving the soundness of label substitution for regions as follows:
assuming $Gamma tack.r r gt.tri sans(L)$, we proceed by induction on $r$
as follows:

- If $r = sans(b r) #h(0em) ell #h(0em) a$, then by
  Lemma~#todo[Resolve source reference `lem:lsubst-inj` during integration.] we have that
  $ bracket.l Gamma tack.r \[ sigma \] \( sans(b r) #h(0em) ell #h(0em) a \) gt.tri sans(K) bracket.r & = bracket.l Gamma tack.r \[ a \/ x \] \[ sigma \] \( sans(b r) #h(0em) ell #h(0em) x \) gt.tri sans(K) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_tack.t a : A bracket.r \) ; bracket.l Gamma \, x : A tack.r \[ sigma \] \( sans(b r) #h(0em) ell #h(0em) x \) gt.tri sans(K) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_tack.t a : A bracket.r \) ; bracket.l Gamma bracket.r times iota_(sans(L) \, ell) ; bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_tack.t a : A bracket.r ; iota_(sans(L) \, ell) \) ; bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r sans(b r) #h(0em) ell #h(0em) a gt.tri sans(L) bracket.r \) ; bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r $
  as desired.

- If $r = \( sans(l e t) #h(0em) x = a ; t \)$, then we have by
  induction that
  $  & bracket.l Gamma tack.r \[ sigma \] \( sans(l e t) #h(0em) x = a ; t \) gt.tri sans(K) bracket.r = bracket.l Gamma tack.r sans(l e t) #h(0em) x = a ; \[ sigma \] t gt.tri sans(K) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A bracket.r \) ; bracket.l Gamma \, x : A tack.r \[ sigma \] t gt.tri sans(K) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A bracket.r \) ; sans(l e t) \( bracket.l Gamma \, x : A tack.r t gt.tri sans(L) bracket.r \) ; bracket.l Gamma \, x : A tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A bracket.r \) ; sans(l e t) \( bracket.l Gamma \, x : A tack.r t gt.tri sans(L) bracket.r \) ; pi_l times bracket.l sans(L) bracket.r ; bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r\
   & = sans(l e t) \( sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A bracket.r \) ; bracket.l Gamma \, x : A tack.r t gt.tri sans(L) bracket.r \) ; bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r sans(l e t) #h(0em) x = a ; t gt.tri sans(L) bracket.r \) ; bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r\
   $ as desired.

- If $r = \( sans(l e t) #h(0em) \( x \, y \) = a ; t \)$, then we have
  by induction that
  $  & bracket.l Gamma tack.r \[ sigma \] \( sans(l e t) #h(0em) \( x \, y \) = a ; t \) gt.tri sans(K) bracket.r = bracket.l Gamma tack.r sans(l e t) #h(0em) \( x \, y \) = a ; \[ sigma \] t gt.tri sans(K) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A times B bracket.r \) ; alpha ; bracket.l Gamma \, x : A \, y : B tack.r \[ sigma \] t gt.tri sans(K) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A times B bracket.r \) ; alpha ; sans(l e t) \( bracket.l Gamma \, x : A \, y : B tack.r t gt.tri sans(L) bracket.r \) ; bracket.l Gamma \, x : A \, y : B tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A times B bracket.r \) ; alpha ; sans(l e t) \( bracket.l Gamma \, x : A \, y : B tack.r t gt.tri sans(L) bracket.r \) ; \( pi_l ; pi_l \) times bracket.l sans(L) bracket.r ; bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r\
   & = sans(l e t) \( sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A times B bracket.r \) ; alpha ; bracket.l Gamma \, x : A \, y : B tack.r t gt.tri sans(L) bracket.r \) ; bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r sans(l e t) #h(0em) \( x \, y \) = a ; t gt.tri sans(L) bracket.r \) ; bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r $
  as desired, since

- If
  $r = sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) x : s \, iota_r #h(0em) y : t }$,
  then we have by induction that
  $  & bracket.l Gamma tack.r \[ sigma \] \( sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) x : s \, iota_r #h(0em) y : t } \) gt.tri sans(K) bracket.r = bracket.l Gamma tack.r sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) x : \[ sigma \] s \, iota_r #h(0em) y : \[ sigma \] t } gt.tri sans(K) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A + B bracket.r \) ; delta^(- 1) ; \[ bracket.l Gamma \, x : A tack.r \[ sigma \] s gt.tri sans(K) bracket.r \, bracket.l Gamma \, y : B tack.r \[ sigma \] t gt.tri sans(K) bracket.r \]\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A + B bracket.r \) ; delta^(- 1) ; \[\
   & #h(2em) sans(l e t) \( bracket.l Gamma \, x : A tack.r s gt.tri sans(L) bracket.r \) ; bracket.l Gamma \, x : A tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r \,\
   & #h(2em) sans(l e t) \( bracket.l Gamma \, y : B tack.r t gt.tri sans(L) bracket.r \) ; bracket.l Gamma \, y : B tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r \]\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A + B bracket.r \) ; delta^(- 1) ;\
   & #h(2em) \[ sans(l e t) \( bracket.l Gamma \, x : A tack.r s gt.tri sans(L) bracket.r \) ; pi_l times bracket.l sans(L) bracket.r \, sans(l e t) \( bracket.l Gamma \, y : B tack.r t gt.tri sans(L) bracket.r \) ; pi_l times bracket.l sans(L) bracket.r \] ; bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r\
   & = sans(l e t) \( sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A + B bracket.r \) ; delta^(- 1) ; \[ bracket.l Gamma \, x : A tack.r s gt.tri sans(L) bracket.r \, bracket.l Gamma \, y : B tack.r t gt.tri sans(L) bracket.r \] \) ; bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) x : s \, iota_r #h(0em) y : t } gt.tri sans(L) bracket.r \) ; bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r $
  as desired.

- If
  $r = s #h(0em) sans(w h e r e) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i$,
  then we have by induction, taking
  $sans(R) = \( ell_i \( A_i \) \, \)_i$,
  $  & sans(e s e m)_(Gamma \, sans(K)) \( \[ sigma^harpoon.tr \] s \) = bracket.l Gamma tack.r \[ sigma^harpoon.tr \] s gt.tri sans(K) \, sans(R) bracket.r ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+)\
   & = sans(l e t) \( bracket.l Gamma tack.r s gt.tri sans(L) \, sans(R) bracket.r \) ; bracket.l Gamma tack.r sigma^harpoon.tr : sans(L) \, sans(R) arrow.r.squiggly sans(K) \, sans(R) bracket.r ; alpha_(bracket.l sans(K) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+)\
   & = sans(l e t) \( bracket.l Gamma tack.r s gt.tri sans(L) \, sans(R) bracket.r \) ; bracket.l Gamma bracket.r times alpha_(bracket.l sans(L) bracket.r + bracket.l sans(R) bracket.r)^(+) ; delta^(- 1) ; bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r + pi_r ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+)\
   & = sans(l e t) \( bracket.l Gamma tack.r s gt.tri sans(L) \, sans(R) bracket.r \) ; bracket.l Gamma bracket.r times alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+) ; delta^(- 1) ; bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r + pi_r\
   & = sans(l e t) \( sans(e s e m)_(Gamma \, sans(L)) \( s \) \) ; delta^(- 1) ; bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r + pi_r $
  and
  $  & sans(l s e m)_(Gamma \, sans(K)) \( \( ell_i \( x_i \) : { \[ sigma^harpoon.tr \] t_i } \, \)_i \) = delta_Sigma^(- 1) ; \[ bracket.l Gamma \, x_i : A_i tack.r \[ sigma^harpoon.tr \] t_i gt.tri sans(K) \, sans(R) bracket.r \]_i ; alpha_(bracket.l sans(K) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+)\
   & = delta_Sigma^(- 1) ; \[ sans(l e t) \( bracket.l Gamma \, x_i : A_i tack.r t_i gt.tri sans(L) \, sans(R) bracket.r \) ; bracket.l Gamma \, x_i : A_i tack.r sigma^harpoon.tr : sans(L) \, sans(R) arrow.r.squiggly sans(K) \, sans(R) bracket.r \]_i ; alpha_(bracket.l sans(K) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+)\
   & = delta_Sigma^(- 1) ; \[ sans(l e t) \( bracket.l Gamma \, x_i : A_i tack.r t_i gt.tri sans(L) \, sans(R) bracket.r \) ; pi_l times bracket.l sans(L) \, sans(R) bracket.r \]_i ; bracket.l Gamma tack.r sigma^harpoon.tr : sans(L) \, sans(R) arrow.r.squiggly sans(K) \, sans(R) bracket.r ; alpha_(bracket.l sans(K) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+)\
   & = delta_Sigma^(- 1) ; \[ sans(l e t) \( bracket.l Gamma \, x_i : A_i tack.r t_i gt.tri sans(L) \, sans(R) bracket.r \) ; pi_l times alpha_(bracket.l sans(L) bracket.r + Sigma_j bracket.l A_j bracket.r)^(+) \]_i ; delta^(- 1) ; bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r + pi_r\
   & = sans(l e t) \( delta_Sigma^(- 1) ; \[ bracket.l Gamma \, x_i : A_i tack.r t_i gt.tri sans(L) \, sans(R) bracket.r ; alpha_(bracket.l sans(L) bracket.r + Sigma_j bracket.l A_j bracket.r)^(+) \, \]_i \) ; pi_l times - ; delta^(- 1) ; bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r + pi_r\
   & = sans(l e t) \( delta_Sigma^(- 1) ; \[ bracket.l Gamma \, x_i : A_i tack.r t_i gt.tri sans(L) \, sans(R) bracket.r \, \]_i ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+) \) ; pi_l times - ; delta^(- 1) ; bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r + pi_r\
   & = sans(l e t) \( sans(l s e m)_(Gamma \, sans(L)) \( \( ell_i \( x_i \) : { t_i } \, \)_i \) \) ; pi_l times - ; delta^(- 1) ; bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r + pi_r $
  Letting
  $L = sans(l s e m)_(Gamma \, sans(L)) \( \( ell_i \( x_i \) : { t_i } \, \)_i \)$
  and
  $S = bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r$,
  we have that
  $  & sans(r c a s e) \( sans(l s e m)_(Gamma \, sans(K)) \( \( ell_i \( x_i \) : { \[ sigma^harpoon.tr \] t_i } \, \)_i \) \)\
   & = sans(l e t) \( sans(l e t) \( L \) ; pi_l times \( bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r \) ; delta^(- 1) ; S + pi_r \) ; pi_l times \( bracket.l sans(K) bracket.r + Sigma_i bracket.l A_i bracket.r \) ; delta^(- 1)\
   & = sans(l e t) \( sans(l e t) \( L \) \) ; \( bracket.l Gamma bracket.r times Sigma_i bracket.l A_i bracket.r \) times \( pi_l times \( bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r \) ; delta^(- 1) ; S + pi_r \) ; pi_l times \( bracket.l sans(K) bracket.r + Sigma_i bracket.l A_i bracket.r \) ; delta^(- 1)\
   & = sans(l e t) \( L \) ; Delta_(bracket.l Gamma bracket.r times Sigma_i bracket.l A_i bracket.r) times - ; alpha ; \( bracket.l Gamma bracket.r times Sigma_i bracket.l A_i bracket.r \) times \( pi_l times \( bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r \) ; delta^(- 1) ; S + pi_r \) ; pi_l times - ; delta^(- 1)\
   & = sans(l e t) \( L \) ; \( pi_l ; Delta_(bracket.l Gamma bracket.r) \) times \( bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r \) ; alpha ; bracket.l Gamma bracket.r times \( delta^(- 1) ; S + pi_r \) ; delta^(- 1)\
   & = sans(l e t) \( L \) ; \( pi_l ; Delta_(bracket.l Gamma bracket.r) \) times \( bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r \) ; alpha ; bracket.l Gamma bracket.r times delta^(- 1) ; delta^(- 1) ; \( bracket.l Gamma bracket.r times bracket.l Gamma bracket.r \) times S + \( bracket.l Gamma bracket.r times bracket.l Gamma bracket.r \) times pi_r\
   & = sans(l e t) \( L \) ; pi_l times \( bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r \) ; delta^(- 1) ; \( Delta_(bracket.l Gamma bracket.r) times bracket.l sans(L) bracket.r ; alpha ; bracket.l Gamma bracket.r times S \) + \( Delta_(bracket.l Gamma bracket.r) times Sigma_i bracket.l A_i bracket.r ; alpha ; bracket.l Gamma bracket.r times pi_r \)\
   & = sans(r c a s e) \( L \) ; Delta_(bracket.l Gamma bracket.r) times bracket.l sans(L) bracket.r ; alpha ; bracket.l Gamma bracket.r times S + bracket.l Gamma bracket.r times Sigma_i bracket.l A_i bracket.r $
  implying by naturality that
  $ sans(r f i x) \( sans(l s e m)_(Gamma \, sans(K)) \( \( ell_i \( x_i \) : { \[ sigma^harpoon.tr \] t_i } \, \)_i \) \) & = \( sans(r c a s e) \( L \) ; Delta_(bracket.l Gamma bracket.r) times bracket.l sans(L) bracket.r ; alpha ; bracket.l Gamma bracket.r times S + bracket.l Gamma bracket.r times Sigma_i bracket.l A_i bracket.r \)^dagger ; pi_r\
   & = \( sans(r c a s e) \( L \) \)^dagger ; Delta_(bracket.l Gamma bracket.r) times bracket.l sans(L) bracket.r ; alpha ; bracket.l Gamma bracket.r times S ; pi_r\
   & = \( sans(r c a s e) \( L \) \)^dagger ; S $ Hence, we have that
  $  & bracket.l Gamma tack.r \[ sigma \] \( s #h(0em) sans(w h e r e) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i \) gt.tri sans(K) bracket.r = bracket.l Gamma tack.r \[ sigma^harpoon.tr \] s #h(0em) sans(w h e r e) #h(0em) \( ell_i \( x_i \) : { \[ sigma^harpoon.tr \] t_i } \, \)_i gt.tri sans(K) bracket.r\
   & = sans(l e t) \( sans(e s e m)_(Gamma \, sans(K)) \( \[ sigma^harpoon.tr \] s \) \) ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( sans(l s e m)_(Gamma \, sans(K)) \( \( ell_i \( x_i \) : { \[ sigma^harpoon.tr \] t_i } \, \)_i \) \) \]\
   & = sans(l e t) \( sans(l e t) \( sans(e s e m)_(Gamma \, sans(L)) \( s \) \) ; delta^(- 1) ; S + pi_r \) ; delta^(- 1) ; \[ pi_r \, \( sans(r c a s e) \( L \) \)^dagger ; S \]\
   & = sans(l e t) \( sans(l e t) \( sans(e s e m)_(Gamma \, sans(L)) \( s \) \) \) ; bracket.l Gamma bracket.r times \( delta^(- 1) ; S + pi_r \) ; delta^(- 1) ; \[ pi_r \, \( sans(r c a s e) \( L \) \)^dagger ; S \]\
   & = sans(l e t) \( sans(l e t) \( sans(e s e m)_(Gamma \, sans(L)) \( s \) \) \) ; bracket.l Gamma bracket.r times delta^(- 1) ; delta^(- 1) ; \[ bracket.l Gamma bracket.r times S ; pi_r \, bracket.l Gamma bracket.r times pi_r ; \( sans(r c a s e) \( L \) \)^dagger ; S \]\
   & = sans(l e t) \( sans(l e t) \( sans(e s e m)_(Gamma \, sans(L)) \( s \) \) \) ; bracket.l Gamma bracket.r times delta^(- 1) ; delta^(- 1) ; \[ pi_r \, bracket.l Gamma bracket.r times pi_r ; \( sans(r c a s e) \( L \) \)^dagger \] ; S\
   & = sans(l e t) \( sans(e s e m)_(Gamma \, sans(L)) \( s \) \) ; Delta_(bracket.l Gamma bracket.r) times \( bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r \) ; alpha ; bracket.l Gamma bracket.r times delta^(- 1) ; delta^(- 1) ; \[ pi_r \, bracket.l Gamma bracket.r times pi_r ; \( sans(r c a s e) \( L \) \)^dagger \] ; S\
   & = sans(l e t) \( sans(e s e m)_(Gamma \, sans(L)) \( s \) \) ; delta^(- 1) ; \[ Delta_(bracket.l Gamma bracket.r) times bracket.l sans(L) bracket.r ; alpha ; pi_r \, Delta_(bracket.l Gamma bracket.r) times Sigma_i bracket.l A_i bracket.r ; alpha ; bracket.l Gamma bracket.r times pi_r ; \( sans(r c a s e) \( L \) \)^dagger \] ; S\
   & = sans(l e t) \( sans(e s e m)_(Gamma \, sans(L)) \( s \) \) ; delta^(- 1) ; \[ Delta_(bracket.l Gamma bracket.r) times bracket.l sans(L) bracket.r ; alpha ; bracket.l Gamma bracket.r times pi_r \, \( sans(r c a s e) \( L \) \)^dagger \] ; S\
   & = sans(l e t) \( sans(e s e m)_(Gamma \, sans(L)) \( s \) \) ; delta^(- 1) ; \[ Delta_(bracket.l Gamma bracket.r) times bracket.l sans(L) bracket.r ; alpha ; bracket.l Gamma bracket.r times pi_r \, sans(l e t) \( sans(r f i x) \( L \) \) ; pi_l times \( bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r \) \] ; S\
   & = sans(l e t) \( sans(e s e m)_(Gamma \, sans(L)) \( s \) \) ; delta^(- 1) ; \[ Delta_(bracket.l Gamma bracket.r) times bracket.l sans(L) bracket.r ; alpha ; bracket.l Gamma bracket.r times pi_r \, Delta_(bracket.l Gamma bracket.r) times Sigma_i bracket.l A_i bracket.r ; alpha ; bracket.l Gamma bracket.r times sans(r f i x) \( L \) \] ; S\
   & = sans(l e t) \( sans(e s e m)_(Gamma \, sans(L)) \( s \) \) ; Delta_(bracket.l Gamma bracket.r) times \( bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r \) ; alpha ; bracket.l Gamma bracket.r times delta^(- 1) ; delta^(- 1) ; \[ bracket.l Gamma bracket.r times pi_r \, bracket.l Gamma bracket.r times sans(r f i x) \( L \) \] ; S\
   & = sans(l e t) \( sans(e s e m)_(Gamma \, sans(L)) \( s \) \) ; Delta_(bracket.l Gamma bracket.r) times \( bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r \) ; alpha ; bracket.l Gamma bracket.r times \( delta^(- 1) ; \[ pi_r \, sans(r f i x) \( L \) \] \) ; S\
   & = sans(l e t) \( sans(l e t) \( sans(e s e m)_(Gamma \, sans(L)) \( s \) \) \) ; bracket.l Gamma bracket.r times \( delta^(- 1) ; \[ pi_r \, sans(r f i x) \( L \) \] \) ; S\
   & = sans(l e t) \( sans(l e t) \( sans(e s e m)_(Gamma \, sans(L)) \( s \) \) ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( L \) \] \) ; S\
   & = sans(l e t) \( bracket.l Gamma tack.r s #h(0em) sans(w h e r e) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i gt.tri sans(L) bracket.r \) ; bracket.l Gamma tack.r sigma : sans(L) arrow.r.squiggly sans(K) bracket.r $
  as desired.

Composition of label substitutions then follows by a trivial
induction.~◻

]
== Equational Theory
<equational-theory>
<proof:soundness-eqn>

#block[
#emph[Proof.] We begin our proof by showing soundness of the equational
theory for expressions, i.e. #todo[Resolve source reference `itm:eqn-sound-expr` during integration.], by rule induction.

- #emph[Congruence]: these follow trivially by induction

- initial, terminal: both of these follow trivially from the universal
  property of the initial/terminal object, respectively.

- let$""_1$-$beta$: this follows directly from
  Corollary~#todo[Resolve source reference `corr:single-subst` during integration.]

- let$""_1$-$eta$: we have
  $  & bracket.l Gamma tack.r_epsilon.alt sans(l e t) #h(0em) x = a ; #h(0em) x : A bracket.r\
   & = Delta_(bracket.l Gamma bracket.r) ; bracket.l Gamma bracket.r times bracket.l Gamma tack.r_epsilon.alt a : A bracket.r ; bracket.l Gamma \, x : A tack.r_epsilon.alt x : A bracket.r\
   & = Delta_(bracket.l Gamma bracket.r) ; bracket.l Gamma bracket.r times bracket.l Gamma tack.r_epsilon.alt a : A bracket.r ; pi_r\
   & = bracket.l Gamma tack.r_epsilon.alt a : A bracket.r $
  as desired.

- let$""_1$-op: we have
  $  & bracket.l Gamma tack.r_epsilon.alt sans(l e t) #h(0em) x = a ; #h(0em) sans(l e t) #h(0em) y = f #h(0em) x ; #h(0em) c : C bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A bracket.r \) ; sans(l e t) \( bracket.l Gamma \, x : A tack.r_epsilon.alt f #h(0em) x : B bracket.r \) ; bracket.l Gamma \, x : A \, y : B tack.r_epsilon.alt c : C bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A bracket.r \) ; sans(l e t) \( pi_r ; bracket.l f bracket.r \) ; pi_l times bracket.l B bracket.r ; bracket.l Gamma \, y : B tack.r_epsilon.alt c : C bracket.r\
   & = sans(l e t) \( sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A bracket.r \) ; pi_r ; bracket.l f bracket.r \) ; bracket.l Gamma \, y : B tack.r_epsilon.alt c : C bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A bracket.r ; bracket.l f bracket.r \) ; bracket.l Gamma \, y : B tack.r_epsilon.alt c : C bracket.r\
   & = bracket.l Gamma tack.r_epsilon.alt sans(l e t) #h(0em) y = f #h(0em) a ; #h(0em) c : C bracket.r $
  as desired. The let$""_1$-abort case is analogous.

- let$""_1$-let$""_1$: we have that
  $  & bracket.l Gamma tack.r_epsilon.alt sans(l e t) #h(0em) y = \( sans(l e t) #h(0em) x = a ; #h(0em) b ; #h(0em) c \) : C bracket.r\
   & = sans(l e t) \( sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A bracket.r \) ; bracket.l Gamma \, x : A tack.r_epsilon.alt b : B bracket.r \) ; bracket.l Gamma \, y : B tack.r_epsilon.alt c : C bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A bracket.r \) ; sans(l e t) \( bracket.l Gamma \, x : A tack.r_epsilon.alt b : B bracket.r \) ; pi_l times bracket.l B bracket.r ; bracket.l Gamma \, y : B tack.r_epsilon.alt c : C bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt a : A bracket.r \) ; sans(l e t) \( bracket.l Gamma \, x : A tack.r_epsilon.alt b : B bracket.r \) ; bracket.l Gamma \, x : A \, y : B tack.r_epsilon.alt c : C bracket.r\
   & = bracket.l Gamma tack.r_epsilon.alt sans(l e t) #h(0em) x = a ; #h(0em) sans(l e t) #h(0em) y = b ; #h(0em) c : C bracket.r $
  as desired.

- let$""_1$-let$""_2$: we have that
  $  & bracket.l Gamma tack.r_epsilon.alt sans(l e t) #h(0em) z = \( sans(l e t) #h(0em) \( x \, y \) = e ; #h(0em) c \) ; #h(0em) d : D bracket.r\
   & = sans(l e t) \( sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt e : A times B bracket.r \) ; alpha ; bracket.l Gamma \, x : A \, y : B tack.r_epsilon.alt c : C bracket.r \) ; bracket.l Gamma \, z : C tack.r_epsilon.alt d : D bracket.r\
   & = sans(l e t) \( Gamma tack.r_epsilon.alt e : A times B \) ; alpha ; sans(l e t) \( bracket.l Gamma \, x : A \, y : B tack.r_epsilon.alt c : C bracket.r \) ; \( pi_l ; pi_l \) times bracket.l sans(C) bracket.r ; bracket.l Gamma \, z : C tack.r_epsilon.alt d : D bracket.r\
   & = sans(l e t) \( Gamma tack.r_epsilon.alt e : A times B \) ; alpha ; sans(l e t) \( bracket.l Gamma \, x : A \, y : B tack.r_epsilon.alt c : C bracket.r \) ; bracket.l Gamma \, x : A \, y : B \, z : C tack.r_epsilon.alt d : D bracket.r\
   & = bracket.l Gamma tack.r_epsilon.alt sans(l e t) #h(0em) \( x \, y \) = e ; #h(0em) sans(l e t) #h(0em) z = c ; #h(0em) d : D bracket.r $
  as desired.

- let$""_1$-case: follows from the properties of the coproduct; in
  particular, we have that
  $  & bracket.l Gamma tack.r_epsilon.alt sans(c a s e) #h(0em) e #h(0em) { iota_l #h(0em) x : sans(l e t) #h(0em) z = a ; #h(0em) d \, iota_r #h(0em) y : sans(l e t) #h(0em) z = b ; #h(0em) d } : D bracket.r\
   & = Delta ; bracket.l Gamma bracket.r times bracket.l Gamma tack.r_epsilon.alt e : A + B bracket.r ; delta^(- 1) ; \[\
   & #h(2em) Delta ; bracket.l Gamma \, x : A bracket.r times bracket.l Gamma \, x : A tack.r_epsilon.alt a : C bracket.r ; bracket.l Gamma \, x : A \, z : C tack.r_epsilon.alt d : D bracket.r \,\
   & #h(2em) Delta ; bracket.l Gamma \, y : B bracket.r times bracket.l Gamma \, y : B tack.r_epsilon.alt b : C bracket.r ; bracket.l Gamma \, y : B \, z : C tack.r_epsilon.alt d : D bracket.r \]\
   & = Delta ; bracket.l Gamma bracket.r times bracket.l Gamma tack.r_epsilon.alt e : A + B bracket.r ; delta^(- 1) ; \[\
   & #h(2em) Delta times bracket.l A bracket.r ; alpha ; bracket.l Gamma bracket.r times bracket.l Gamma \, x : A tack.r_epsilon.alt a : C bracket.r ; bracket.l Gamma \, z : C tack.r_epsilon.alt d : D bracket.r \,\
   & #h(2em) Delta times bracket.l B bracket.r ; alpha ; bracket.l Gamma bracket.r times bracket.l Gamma \, y : B tack.r_epsilon.alt b : C bracket.r ; bracket.l Gamma \, z : C tack.r_epsilon.alt d : D bracket.r \]\
   & = Delta ; bracket.l Gamma bracket.r times bracket.l Gamma tack.r_epsilon.alt e : A + B bracket.r ; delta^(- 1) ; \[\
   & #h(2em) Delta times bracket.l A bracket.r ; alpha ; bracket.l Gamma bracket.r times bracket.l Gamma \, x : A tack.r_epsilon.alt a : C bracket.r \,\
   & #h(2em) Delta times bracket.l B bracket.r ; alpha ; bracket.l Gamma bracket.r times bracket.l Gamma \, y : B tack.r_epsilon.alt b : C bracket.r \] ; bracket.l Gamma \, z : C tack.r_epsilon.alt d : D bracket.r\
   & = Delta ; Delta times bracket.l Gamma tack.r_epsilon.alt e : A + B bracket.r ; delta^(- 1) ;\
   & #h(2em) \[ alpha ; bracket.l Gamma bracket.r times bracket.l Gamma \, x : A tack.r_epsilon.alt a : C bracket.r \, alpha ; bracket.l Gamma bracket.r times bracket.l Gamma \, y : B tack.r_epsilon.alt b : C bracket.r \] ; bracket.l Gamma \, z : C tack.r_epsilon.alt d : D bracket.r\
   & = Delta ; Delta times bracket.l Gamma tack.r_epsilon.alt e : A + B bracket.r ; alpha ; bracket.l Gamma bracket.r times \( delta^(- 1) ; \[ bracket.l Gamma \, x : A tack.r_epsilon.alt a : C bracket.r \, bracket.l Gamma \, y : B tack.r_epsilon.alt b : C bracket.r \] \) ;\
   & #h(2em) bracket.l Gamma \, z : C tack.r_epsilon.alt d : D bracket.r\
   & = Delta ; bracket.l Gamma bracket.r times \( Delta ; bracket.l Gamma bracket.r times bracket.l Gamma tack.r_epsilon.alt e : A + B bracket.r ; delta^(- 1) ; \[ bracket.l Gamma \, x : A tack.r_epsilon.alt a : C bracket.r \, bracket.l Gamma \, y : B tack.r_epsilon.alt b : C bracket.r \] \) ;\
   & #h(2em) bracket.l Gamma \, z : C tack.r_epsilon.alt d : D bracket.r\
   & = bracket.l Gamma tack.r_epsilon.alt sans(l e t) #h(0em) z = \( sans(c a s e) #h(0em) e #h(0em) { iota_l #h(0em) x : a \, iota_r #h(0em) y : b } \) ; #h(0em) d : D bracket.r $

- let$""_2$-bind: we have
  $  & bracket.l Gamma tack.r_epsilon.alt sans(l e t) #h(0em) z = e ; #h(0em) sans(l e t) #h(0em) \( x \, y \) = z ; #h(0em) c : C bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt e : A times B bracket.r \) ; sans(l e t) \( bracket.l Gamma \, z : A times B tack.r_epsilon.alt z : A times B bracket.r \) ; alpha ; bracket.l Gamma \, z : A times B \, x : A \, y : B tack.r_epsilon.alt c : C bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt e : A times B bracket.r \) ; sans(l e t) \( pi_r \) ; pi_l times \( bracket.l A bracket.r times bracket.l B bracket.r \) ; alpha ; bracket.l Gamma \, x : A \, y : B tack.r_epsilon.alt c : C bracket.r\
   & = sans(l e t) \( sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt e : A times B bracket.r \) ; pi_r \) ; alpha ; bracket.l Gamma \, x : A \, y : B tack.r_epsilon.alt c : C bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r_epsilon.alt e : A times B bracket.r \) ; alpha ; bracket.l Gamma \, x : A \, y : B tack.r_epsilon.alt c : C bracket.r\
   & = bracket.l Gamma tack.r_epsilon.alt sans(l e t) #h(0em) \( x \, y \) = e ; #h(0em) c : C bracket.r $

- let$""_2$-$eta$: follows from the properties of the product; in
  particular, we have that
  $  & bracket.l Gamma tack.r_epsilon.alt sans(l e t) #h(0em) \( x \, y \) = e ; #h(0em) \( x \, y \) : A times B bracket.r\
   & = Delta ; bracket.l Gamma bracket.r times bracket.l Gamma tack.r_epsilon.alt e : A times B bracket.r ; Delta ; bracket.l Gamma \, x : A \, y : B tack.r_tack.t x : A bracket.r times bracket.l Gamma \, x : A \, y : B tack.r_tack.t y : B bracket.r\
   & = Delta ; bracket.l Gamma bracket.r times bracket.l Gamma tack.r_epsilon.alt e : A times B bracket.r ; Delta ; \( pi_l ; pi_r \) times pi_r = bracket.l Gamma tack.r_epsilon.alt e : A times B bracket.r $

- case-inl: follows from the properties of the coproduct and inverse
  distributor; in particular, we have that
  $  & bracket.l Gamma tack.r_epsilon.alt sans(c a s e) #h(0em) iota_l #h(0em) a #h(0em) { iota_l #h(0em) x : c \, iota_r #h(0em) y : d } : C bracket.r\
   & = Delta ; bracket.l Gamma bracket.r times \( bracket.l Gamma tack.r_epsilon.alt a : A bracket.r ; iota_l \) ; delta^(- 1) ; \[ bracket.l Gamma \, x : A tack.r_epsilon.alt c : C bracket.r \, bracket.l Gamma \, y : B tack.r_epsilon.alt d : C bracket.r \]\
   & = Delta ; bracket.l Gamma bracket.r times bracket.l Gamma tack.r_epsilon.alt a : A bracket.r ; iota_l ; \[ bracket.l Gamma \, x : A tack.r_epsilon.alt c : C bracket.r \, bracket.l Gamma \, y : B tack.r_epsilon.alt d : C bracket.r \]\
   & = Delta ; bracket.l Gamma bracket.r times bracket.l Gamma tack.r_epsilon.alt a : A bracket.r ; iota_l ; bracket.l Gamma \, x : A tack.r_epsilon.alt c : C bracket.r\
   & = bracket.l Gamma tack.r_epsilon.alt sans(l e t) #h(0em) x = a ; #h(0em) c : C bracket.r $
  We can validate case-inr analogously

- case-$eta$: follows from the properties of the coproduct and
  distributor; in particular, we have
  $  & bracket.l Gamma tack.r_epsilon.alt sans(c a s e) #h(0em) e #h(0em) { iota_l #h(0em) x : iota_l #h(0em) x \, iota_r #h(0em) y : iota_r #h(0em) y } : A + B bracket.r\
   & = Delta ; bracket.l Gamma bracket.r times bracket.l Gamma tack.r_epsilon.alt e : A + B bracket.r ; delta^(- 1) ; \[ bracket.l Gamma \, x : A tack.r_epsilon.alt x : A bracket.r ; iota_l \, bracket.l Gamma \, y : B tack.r_epsilon.alt y : B ; iota_r bracket.r \]\
   & = Delta ; bracket.l Gamma bracket.r times bracket.l Gamma tack.r_epsilon.alt e : A + B bracket.r ; delta^(- 1) ; \( pi_r + pi_r \) = bracket.l Gamma tack.r_epsilon.alt e : A + B bracket.r $

We now proceed to tackle the equational theory for regions $r$ in the
same manner. In particular, we proceed by rule induction as follows:

- cfg-$beta_1$: Define
  $P = bracket.l Gamma tack.r_tack.t a : A_k bracket.r$,
  $L = sans(l s e m)_(Gamma \, sans(L)) \( \( ell_i \( x_i \) : { t_i } \, \)_i \)$
  and $sans(R) = \( ell_i \( A_i \) \, \)_i$. We have that
  $  & bracket.l Gamma tack.r sans(b r) #h(0em) ell_k #h(0em) a #h(0em) sans(w h e r e) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i gt.tri sans(L) bracket.r\
   & = sans(l e t) \( P ; iota_(\( sans(L) \, sans(R) \) \, ell_k) ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+) \) ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( L \) \]\
   & = sans(l e t) \( P ; iota_k \) ; bracket.l Gamma bracket.r times iota_r ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( L \) \]\
   & = sans(l e t) \( P ; iota_k \) ; sans(r f i x) \( L \)\
   & = sans(l e t) \( P ; iota_k \) ; sans(r c a s e) \( L \) ; \[ pi_r \, sans(r f i x) \( L \) \]\
   & = sans(l e t) \( P \) ; sans(r c a s e) \( bracket.l Gamma bracket.r times iota_k ; L \) ; \[ pi_r \, sans(r f i x) \( L \) \]\
   & = sans(l e t) \( P \) ; sans(r c a s e) \( bracket.l Gamma \, x_k : A_k tack.r t_k gt.tri sans(L) \, sans(R) bracket.r ; alpha_(bracket.l L bracket.r + Sigma_i bracket.l A_i bracket.r)^(+) \) ; \[ pi_r \, sans(r f i x) \( L \) \]\
   & = sans(l e t) \( P \) ; sans(r l e t) \( bracket.l Gamma \, x_k : A_k tack.r t_k gt.tri sans(L) \, sans(R) bracket.r ; alpha_(bracket.l L bracket.r + Sigma_i bracket.l A_i bracket.r)^(+) \) ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( L \) \]\
   & = sans(l e t) \( sans(l e t) \( P \) ; bracket.l Gamma \, x_k : A_k tack.r t_k gt.tri sans(L) \, sans(R) bracket.r ; alpha_(bracket.l L bracket.r + Sigma_i bracket.l A_i bracket.r)^(+) \) ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( L \) \]\
   & = sans(l e t) \( bracket.l Gamma tack.r sans(l e t) #h(0em) x_k = a ; t_k gt.tri sans(L) \, sans(R) bracket.r ; alpha_(bracket.l L bracket.r + Sigma_i bracket.l A_i bracket.r)^(+) \) ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( L \) \]\
   & = bracket.l Gamma tack.r sans(l e t) #h(0em) x_k = a ; t_k #h(0em) sans(w h e r e) #h(0em) \( ell_i \( x_i \) : { A_i } \, \)_i gt.tri sans(L) bracket.r $
  as desired.

- cfg-$beta_2$: Define
  $P = bracket.l Gamma tack.r_tack.t b : B bracket.r$,
  $L = sans(l s e m)_(Gamma \, sans(L)) \( \( ell_i \( x_i \) : { t_i } \, \)_i \)$
  and $sans(R) = \( ell_i \( A_i \) \, \)_i$. We have that
  $  & bracket.l Gamma tack.r sans(b r) #h(0em) kappa #h(0em) b #h(0em) sans(w h e r e) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i gt.tri sans(L) bracket.r\
   & = sans(l e t) \( P ; iota_(\( sans(L) \, sans(R) \) \, kappa) ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+) \) ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( L \) \]\
   & = sans(l e t) \( P ; iota_(sans(L) \, kappa) \) ; bracket.l Gamma bracket.r times iota_l ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( L \) \]\
   & = sans(l e t) \( P ; iota_(sans(L) \, kappa) \) ; pi_r = P ; iota_(sans(L) \, kappa) = bracket.l Gamma tack.r sans(b r) #h(0em) kappa #h(0em) b gt.tri sans(L) bracket.r $
  as desired.

- cfg-$eta$: Let $sans(L) = \( kappa_j \( B_j \) \, \)_j$, and define
  $sans(R) = \( ell_i \( A_i \) \, \)_i$ and
  $L = sans(l s e m)_(Gamma \, sans(L)) \( \( ell_i \( x_i \) : { t_i } \, \)_i \)$.
  Using the cfg-$beta_1$ and cfg-$beta_2$ cases proved above, we have
  that
  $  & bracket.l Gamma tack.r sans(c f g s) #h(0em) { \( ell_i \( x_i \) : { t_i } \, \)_i } : sans(L) \, sans(R) arrow.r.squiggly sans(L) bracket.r\
   & = bracket.l Gamma bracket.r times alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r) ; delta^(- 1) ; \[\
   & #h(2em) bracket.l Gamma tack.r sans(c f g s) #h(0em) { \( ell_i \( x_i \) : { t_i } \, \)_i } : sans(L) arrow.r.squiggly sans(L) bracket.r \,\
   & #h(2em) bracket.l Gamma tack.r sans(c f g s) #h(0em) { \( ell_i \( x_i \) : { t_i } \, \)_i } : sans(R) arrow.r.squiggly sans(L) bracket.r \]\
   & = bracket.l Gamma bracket.r times alpha_(Sigma_i bracket.l B_i bracket.r + Sigma_i bracket.l A_i bracket.r) ; delta^(- 1) ; \[\
   & #h(2em) delta_Sigma^(- 1) ; \[ bracket.l Gamma \, y_j : B_j tack.r sans(b r) #h(0em) kappa_j #h(0em) y_j #h(0em) sans(w h e r e) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i gt.tri sans(L) bracket.r \, \]_j \,\
   & #h(2em) delta_Sigma^(- 1) ; \[ bracket.l Gamma \, x_j : A_j tack.r sans(b r) #h(0em) ell_j #h(0em) x_j #h(0em) sans(w h e r e) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i gt.tri sans(L) bracket.r \, \]_j \]\
   & = bracket.l Gamma bracket.r times alpha_(Sigma_i bracket.l B_i bracket.r + Sigma_i bracket.l A_i bracket.r) ; delta^(- 1) ; \[\
   & #h(2em) delta_Sigma^(- 1) ; \[ bracket.l Gamma \, y_j : B_j tack.r_tack.t y_j : B_j bracket.r ; iota_(sans(L) \, kappa_j) \, \]_j \,\
   & #h(2em) delta_Sigma^(- 1) ; \[ sans(l e t) \( bracket.l Gamma \, x_j : A_j tack.r_tack.t x_j : A_j bracket.r ; iota_j \) ; sans(r f i x) \( pi_l times Sigma_k bracket.l A_k bracket.r ; L \) \]_j \]\
   & = bracket.l Gamma bracket.r times alpha_(Sigma_i bracket.l B_i bracket.r + Sigma_i bracket.l A_i bracket.r) ; delta^(- 1) ; \[ delta_Sigma^(- 1) ; \[ pi_r ; iota_(sans(L) \, kappa_j) \, \]_j \, delta_Sigma^(- 1) ; \[ sans(l e t) \( pi_r ; iota_j \) ; pi_l times Sigma_k bracket.l A_k bracket.r \]_j ; sans(r f i x) \( L \) \]\
   & = bracket.l Gamma bracket.r times alpha_(Sigma_i bracket.l B_i bracket.r + Sigma_i bracket.l A_i bracket.r) ; delta^(- 1) ; \[ pi_r ; alpha_(sans(L)) \, sans(r l e t) \( delta_Sigma^(- 1) ; \[ pi_r ; iota_j \]_j \) ; sans(r f i x) \( L \) \]\
   & = bracket.l Gamma bracket.r times alpha_(sans(L) + Sigma_i bracket.l A_i bracket.r) ; delta^(- 1) ; \[ pi_r \, sans(r l e t) \( pi_r \) ; sans(r f i x) \( L \) \]\
   & = bracket.l Gamma bracket.r times alpha_(sans(L) + Sigma_i bracket.l A_i bracket.r) ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( L \) \] $
  It follows by label-substitution that that
  $  & bracket.l Gamma tack.r \[ sans(c f g s) #h(0em) { \( ell_i \( x_i \) : { t_i } \, \)_i } \] r gt.tri sans(L) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r r gt.tri sans(L) \, sans(R) bracket.r \) ; bracket.l Gamma tack.r sans(c f g s) #h(0em) { \( ell_i \( x_i \) : { t_i } \, \)_i } : sans(L) \, sans(R) arrow.r.squiggly sans(L) bracket.r\
   & = sans(l e t) \( bracket.l Gamma tack.r r gt.tri sans(L) \, sans(R) bracket.r \) ; bracket.l Gamma bracket.r times alpha_(sans(L) + Sigma_i bracket.l A_i bracket.r) ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( L \) \]\
   & = sans(e s e m)_(Gamma \, sans(L)) \( r \) ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( L \) \]\
   & bracket.l Gamma tack.r r #h(0em) sans(w h e r e) #h(0em) \( ell_i \( x_i \) : { t_i } \, \)_i gt.tri sans(L) bracket.r $
  as desired.

- codiag: Define
  $R = bracket.l Gamma tack.r r gt.tri sans(L) \, ell \( A \) bracket.r$,
  and
  $S = bracket.l Gamma \, y : A tack.r s gt.tri sans(L) \, ell \( A \) \, kappa \( A \) bracket.r$
  We have that
  $  & bracket.l Gamma tack.r r #h(0em) sans(w h e r e) #h(0em) ell \( x \) : { sans(b r) #h(0em) kappa #h(0em) x #h(0em) sans(w h e r e) #h(0em) kappa \( y \) : { s } } gt.tri sans(L) bracket.r\
   & = sans(l e t) \( R \) ; delta^(- 1) ; \[ sans(i d) \, sans(r f i x) \( bracket.l Gamma \, x : A tack.r sans(b r) #h(0em) kappa #h(0em) x #h(0em) sans(w h e r e) #h(0em) kappa \( y \) : { s } gt.tri sans(L) \, ell \( A \) bracket.r \) \]\
   & = sans(l e t) \( R \) ; delta^(- 1) ; \[ sans(i d) \, sans(r f i x) \( sans(l e t) \( pi_r ; iota_r \) ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( bracket.l Gamma \, x : A \, y : A tack.r s gt.tri sans(L) \, ell \( A \) \, kappa \( A \) bracket.r \) \] \) \]\
   & = sans(l e t) \( R \) ; delta^(- 1) ; \[ sans(i d) \, sans(r f i x) \( sans(l e t) \( pi_r ; iota_r \) ; delta^(- 1) ; \[ pi_l times A ; pi_r \, sans(r f i x) \( pi_l times bracket.l A bracket.r ; S \) \] \) \]\
   & = sans(l e t) \( R \) ; delta^(- 1) ; \[ sans(i d) \, sans(r f i x) \( sans(l e t) \( pi_r ; iota_r \) ; pi_l times bracket.l A bracket.r ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( S \) \] \) \]\
   & = sans(l e t) \( R \) ; delta^(- 1) ; \[ sans(i d) \, sans(r f i x) \( iota_r^(bracket.l Gamma bracket.r) gt.double_() \[ pi_r \, sans(r f i x) \( S \) \]_(bracket.l Gamma bracket.r) \) \]\
   & = sans(l e t) \( R \) ; delta^(- 1) ; \[ sans(i d) \, sans(r f i x) \( sans(r f i x) \( S \) \) \] = sans(l e t) \( R \) ; delta^(- 1) ; \[ sans(i d) \, sans(r f i x) \( S gt.double_() \[ pi_r \, iota_r^(bracket.l Gamma bracket.r) \]_(bracket.l Gamma bracket.r) \) \]\
   & = sans(l e t) \( R \) ; delta^(- 1) ; \[ sans(i d) \, sans(r f i x) \( sans(l e t) \( S \) ; delta^(- 1) ; \[ pi_r \, pi_r ; iota_r \] \) \] = sans(l e t) \( R \) ; delta^(- 1) ; \[ sans(i d) \, sans(r f i x) \( S ; \[ sans(i d) \, iota_r \] \) \]\
   & = sans(l e t) \( R \) ; delta^(- 1) ; \[ sans(i d) \, sans(r f i x) \( bracket.l Gamma \, y : A tack.r \[ ell \/ kappa \] s gt.tri sans(L) \, ell \( A \) bracket.r \) \] = bracket.l Gamma tack.r r #h(0em) sans(w h e r e) #h(0em) ell \( y \) : { \[ ell \/ kappa \] s } gt.tri sans(L) bracket.r $
  as desired.

- uni: Define
  $R = bracket.l Gamma tack.r r gt.tri sans(L) \, ell \( A \) bracket.r$,
  $E = bracket.l Gamma \, x : A tack.r_tack.t e : B bracket.r$,
  $S = bracket.l Gamma \, y : B tack.r s gt.tri sans(L) \, kappa \( B \) bracket.r$,
  and
  $T = bracket.l Gamma \, x : A tack.r s gt.tri sans(L) \, ell \( A \) bracket.r$.
  We have by induction that
  $ bracket.l Gamma \, x : A tack.r sans(l e t) #h(0em) y = e ; s gt.tri sans(L) \, kappa \( B \) bracket.r & = sans(r l e t) \( E \) ; S =\
  bracket.l Gamma \, x : A tack.r t #h(0em) sans(w h e r e) #h(0em) ell \( x \) : { sans(b r) #h(0em) kappa #h(0em) e } gt.tri sans(L) \, kappa \( B \) bracket.r & = sans(r c a s e) \( T \) ; bracket.l sans(L) bracket.r + E $
  It follows in particular that
  $ sans(r l e t) \( E \) ; sans(r f i x) \( S \) = sans(r f i x) \( T \) $
  and hence that
  $  & bracket.l Gamma tack.r \( r #h(0em) sans(w h e r e) #h(0em) ell \( x \) : { sans(b r) #h(0em) kappa #h(0em) e } \) #h(0em) sans(w h e r e) #h(0em) kappa \( y \) : { s } gt.tri sans(L) bracket.r\
   & = sans(l e t) \( sans(l e t) \( R \) ; delta^(- 1) ; pi_r + E \) ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( S \) \]\
   & = sans(l e t) \( R \) ; delta^(- 1) ; \( bracket.l Gamma bracket.r times bracket.l sans(L) bracket.r \) + sans(r l e t) \( E \) ; \[ pi_r \, sans(r f i x) \( S \) \] = sans(l e t) \( R \) ; delta^(- 1) ; \[ pi_r \, sans(r l e t) \( E \) ; sans(r f i x) \( S \) \]\
   & = sans(l e t) \( R \) ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( T \) \] = bracket.l Gamma tack.r r #h(0em) sans(w h e r e) #h(0em) ell \( x \) : { t } gt.tri sans(L) bracket.r\
   $ as desired.

- dinat: We define $sans(R) = \( ell_i \( A_i \) \, \)_i$,
  $sans(R)' = \( kappa_j \( B_j \) \, \)_j$,
  $S = bracket.l Gamma tack.r sigma : sans(R) arrow.r.squiggly sans(R)' bracket.r$,
  and
  $S' = bracket.l Gamma bracket.r times alpha_(bracket.l R bracket.r)^(+) ; S ; alpha_(Sigma_j bracket.l B_j bracket.r)^(+)$.
  We have that
  $  & sans(e s e m)_(Gamma \, sans(L)) \( \[ sigma^harpoon.tl \] r \) = bracket.l Gamma tack.r \[ sigma^harpoon.tl \] r gt.tri sans(L) \, sans(R)' bracket.r ; alpha_(bracket.l sans(L) bracket.r + Sigma_j bracket.l B_j bracket.r)^(+)\
   & = sans(l e t) \( bracket.l Gamma tack.r r gt.tri sans(L) \, sans(R) bracket.r \) ; bracket.l Gamma bracket.r times alpha_(bracket.l sans(L) bracket.r + bracket.l sans(R) bracket.r)^(+) ; delta^(- 1) ; pi_r + \( S ; alpha_(Sigma_j bracket.l B_j bracket.r)^(+) \)\
   & = sans(l e t) \( sans(e s e m)_(Gamma \, sans(L)) \( r \) \) ; delta^(- 1) ; pi_r + S'\
   $ and, writing
  $L = sans(l s e m)_(Gamma \, sans(L)) \( \( ell_i \( x_i \) : { t_i } \, \)_i \)$,
  $  & sans(l e t) \( \( kappa_i \( x_i \) : { \[ sigma^harpoon.tl \] t_i } \, \)_i \) = delta_Sigma^(- 1) ; \[ bracket.l Gamma \, x_i : B_i tack.r \[ sigma^harpoon.tl \] t_i gt.tri sans(L) \, sans(R)' bracket.r \, \]_i ; alpha_(bracket.l sans(L) bracket.r + Sigma_j bracket.l B_j bracket.r)^(+)\
   & = delta_Sigma^(- 1) ; \[ sans(l e t) \( bracket.l Gamma \, x_i : B_i tack.r t_i gt.tri sans(L) \, sans(R) bracket.r \) ; bracket.l Gamma \, x_i : B_i tack.r sigma^harpoon.tl : sans(L) \, sans(R) arrow.r.squiggly sans(L) \, sans(R)' bracket.r \, \]_i ; alpha_(bracket.l sans(L) bracket.r + Sigma_j bracket.l B_j bracket.r)^(+)\
   & = delta_Sigma^(- 1) ; \[ sans(r l e t) \( bracket.l Gamma \, x_i : B_i tack.r t_i gt.tri sans(L) \, sans(R) bracket.r \) \, \]_i ; bracket.l Gamma tack.r sigma^harpoon.tl : sans(L) \, sans(R) arrow.r.squiggly sans(L) \, sans(R)' bracket.r ; alpha_(bracket.l sans(L) bracket.r + Sigma_j bracket.l B_j bracket.r)^(+)\
   & = sans(r l e t) \( delta_Sigma^(- 1) ; \[ bracket.l Gamma \, x_i : B_i tack.r t_i gt.tri sans(L) \, sans(R) bracket.r \]_i \) ; bracket.l Gamma bracket.r times alpha_(bracket.l sans(L) bracket.r + bracket.l sans(R) bracket.r)^(+) ; delta^(- 1) ; pi_r + \( S ; alpha_(Sigma_j bracket.l B_j bracket.r)^(+) \)\
   & = sans(r l e t) \( delta_Sigma^(- 1) ; \[ bracket.l Gamma \, x_i : B_i tack.r t_i gt.tri sans(L) \, sans(R) bracket.r \, \]_i ; alpha_(bracket.l sans(L) bracket.r + Sigma_j bracket.l B_j bracket.r)^(+) \) ; delta^(- 1) ; pi_r + S'\
   & = sans(r c a s e) \( L \) ; pi_r + S'\
   $ Furthermore, we have that, letting
  $G = bracket.l Gamma tack.r \( kappa_j \( x_j \) mapsto t_j \, \)_j : sans(R)' arrow.r.squiggly sans(L) \, sans(R) bracket.r$,
  $  & bracket.l Gamma \, x_i : A_i tack.r \[ \( kappa_j \( x_j \) mapsto t_j \, \)_j^harpoon.tl \] \( sigma #h(0em) ell_i #h(0em) x_i \) gt.tri sans(L) \, sans(R) bracket.r\
   & = sans(l e t) \( bracket.l Gamma \, x_i : A_i tack.r sigma #h(0em) ell_i #h(0em) x_i gt.tri sans(L) \, sans(R)' bracket.r \) ; bracket.l Gamma \, x_i : A_i tack.r \( kappa_j \( x_j \) mapsto t_j \, \)_j^harpoon.tl : sans(L) \, sans(R)' arrow.r.squiggly sans(L) \, sans(R) bracket.r\
   & = sans(l e t) \( bracket.l Gamma \, x_i : A_i tack.r sigma #h(0em) ell_i #h(0em) x_i gt.tri sans(L) \, sans(R)' bracket.r \) ; pi_l times bracket.l sans(L) \, sans(R') bracket.r ; bracket.l Gamma tack.r \( kappa_j \( x_j \) mapsto t_j \, \)_j^harpoon.tl : sans(L) \, sans(R)' arrow.r.squiggly sans(L) \, sans(R) bracket.r\
   & = sans(r l e t) \( bracket.l Gamma \, x_i : A_i tack.r sigma #h(0em) ell_i #h(0em) x_i gt.tri sans(L) \, sans(R)' bracket.r \) ; bracket.l Gamma bracket.r times alpha_(bracket.l sans(L) bracket.r + bracket.l sans(R)' bracket.r)^(+) ; delta^(- 1) ; \[ pi_r ; iota_l ; alpha_(bracket.l sans(L) \, sans(R) bracket.r)^(+) \, G \]\
   & = sans(r l e t) \( bracket.l Gamma \, x_i : A_i tack.r sigma #h(0em) ell_i #h(0em) x_i gt.tri sans(L) \, sans(R)' bracket.r ; alpha_(bracket.l sans(L) bracket.r + bracket.l sans(R)' bracket.r)^(+) \) ; delta^(- 1) ; \[ pi_r ; iota_l ; alpha_(bracket.l sans(L) \, sans(R) bracket.r)^(+) \, G \]\
   & = sans(r c a s e) \( bracket.l Gamma \, x_i : A_i tack.r sigma #h(0em) ell_i #h(0em) x_i gt.tri sans(L) \, sans(R)' bracket.r ; alpha_(bracket.l sans(L) bracket.r + bracket.l sans(R)' bracket.r)^(+) \) ; \[ pi_r ; iota_l ; alpha_(bracket.l sans(L) \, sans(R) bracket.r)^(+) \, G \]\
   & = sans(r c a s e) \( bracket.l Gamma \, x_i : A_i tack.r sigma #h(0em) ell_i #h(0em) x_i gt.tri sans(R)' bracket.r ; iota_r \) ; \[ pi_r ; iota_l ; alpha_(bracket.l sans(L) \, sans(R) bracket.r)^(+) \, G \]\
   & = sans(r l e t) \( bracket.l Gamma \, x_i : A_i tack.r sigma #h(0em) ell_i #h(0em) x_i gt.tri sans(R)' bracket.r \) ; G\
   $ It follows that
  $  & sans(l s e m)_(Gamma \, sans(L)) \( \( ell_i \( x_i \) : { \[ \( kappa_j \( x_j \) mapsto t_j \, \)^harpoon.tl \] \( sigma #h(0em) ell_i #h(0em) x_i \) } \, \)_i \)\
   & = delta_Sigma^(- 1) ; \[ bracket.l Gamma \, x_i : A_i tack.r \[ \( kappa_j \( x_j \) mapsto t_j \, \)_j^harpoon.tl \] \( sigma #h(0em) ell_i #h(0em) x_i \) gt.tri sans(L) \, sans(R) bracket.r \, \]_i ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+)\
   & = delta_Sigma^(- 1) ; \[ sans(r l e t) \( bracket.l Gamma \, x_i : A_i tack.r sigma #h(0em) ell_i #h(0em) x_i gt.tri sans(R)' bracket.r \) ; G \]_i ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+)\
   & = delta_Sigma^(- 1) ; \[ sans(r l e t) \( bracket.l Gamma \, x_i : A_i tack.r sigma #h(0em) ell_i #h(0em) x_i gt.tri sans(R)' bracket.r \) ; G \]_i ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+)\
   & = delta_Sigma^(- 1) ; \[ sans(r l e t) \( bracket.l Gamma \, x_i : A_i tack.r sigma #h(0em) ell_i #h(0em) x_i gt.tri sans(R)' bracket.r \) \]_i ; G ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+)\
   & = sans(r l e t) \( delta_Sigma^(- 1) ; \[ bracket.l Gamma \, x_i : A_i tack.r sigma #h(0em) ell_i #h(0em) x_i gt.tri sans(R)' bracket.r \]_i \) ; G ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+)\
   & = sans(r l e t) \( delta_Sigma^(- 1) ; \[ bracket.l Gamma \, x_i : A_i tack.r sigma #h(0em) ell_i #h(0em) x_i gt.tri sans(R)' bracket.r \]_i \) ; G ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+)\
   & = sans(r l e t) \( bracket.l Gamma bracket.r times alpha_(bracket.l sans(R) bracket.r) ; S \) ; G ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+)\
   & = sans(r l e t) \( S' \) ; bracket.l Gamma bracket.r times alpha_(bracket.l sans(R') bracket.r) ; bracket.l Gamma tack.r \( kappa_j \( x_j \) mapsto t_j \, \)_j : sans(R)' arrow.r.squiggly sans(L) \, sans(R) bracket.r ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+)\
   & = sans(r l e t) \( S' \) ; delta_Sigma^(- 1) ; \[ bracket.l Gamma \, x_i : A_i tack.r t_i gt.tri sans(R)' sans(L) \, sans(R) bracket.r \, \]_i ; alpha_(bracket.l sans(L) bracket.r + Sigma_i bracket.l A_i bracket.r)^(+)\
   & = sans(r l e t) \( S' \) ; L\
   $ We therefore have
  $  & bracket.l Gamma tack.r \[ sigma^harpoon.tl \] r #h(0em) sans(w h e r e) #h(0em) \( kappa_i \( x_i \) : { \[ sigma^harpoon.tl \] t_i } \, \)_i gt.tri sans(L) bracket.r\
   & = sans(l e t) \( sans(e s e m)_(Gamma \, sans(L)) \( \[ sigma^harpoon.tl \] r \) \) ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( sans(l s e m)_(Gamma \, sans(L)) \( \( kappa_i \( x_i \) : { \[ sigma^harpoon.tl \] t_i } \, \)_i \) \) \]\
   & = sans(l e t) \( sans(l e t) \( sans(e s e m)_(Gamma \, sans(L)) \( r \) \) ; delta^(- 1) ; pi_r + S' \) ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( sans(r c a s e) \( L \) ; pi_r + S' \) \]\
   & = sans(l e t) \( sans(e s e m)_(Gamma \, sans(L)) \( r \) \) ; delta^(- 1) ; bracket.l Gamma bracket.r times bracket.l sans(L) bracket.r + sans(r l e t) \( S \) ; \[ pi_r \, sans(r f i x) \( sans(r c a s e) \( L \) ; pi_r + S' \) \]\
   & = sans(l e t) \( sans(e s e m)_(Gamma \, sans(L)) \( r \) \) ; delta^(- 1) ; \[ pi_r \, sans(r l e t) \( S' \) ; sans(r f i x) \( sans(r c a s e) \( L \) ; pi_r + S' \) \]\
   & = sans(l e t) \( sans(e s e m)_(Gamma \, sans(L)) \( r \) \) ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( sans(r l e t) \( S' \) ; L \) \]\
   & = sans(l e t) \( sans(e s e m)_(Gamma \, sans(L)) \( r \) \) ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( sans(l s e m)_(Gamma \, sans(L)) \( \( ell_i \( x_i \) : { \[ \( kappa_j \( x_j \) mapsto t_j \, \)^harpoon.tl \] \( sigma #h(0em) ell_i #h(0em) x_i \) } \, \)_i \) \) \]\
   & = bracket.l Gamma tack.r r #h(0em) sans(w h e r e) #h(0em) \[ \( kappa_j \( x_j \) mapsto t_j \, \)^harpoon.tl \] \( sigma #h(0em) ell_i #h(0em) x_i \) \, \)_i gt.tri sans(L) bracket.r $
  as desired.

All other cases are analogous to those for expressions, and so
omitted.~◻

]
#block[
The rewrite rules cfg-fuse$""_1$ (Eqn.~#todo[Resolve source reference `eqn:where-fusion-1` during integration.]) and
cfg-fuse$""_2$ are sound, where we define
#todo[Port the following preserved source equation or proof-tree display to native Typst.]
\$\$\\prftree\[r\]{{\\scriptsize\\textsf{cfg-fuse\$\_2\$}}}
    {\\Gamma \\vdash r \\rhd \\ensuremath{\\mathsf{L}}, (\\ell\_i(A\_i),)\_i, \\kappa(B)}
    {
      \\prfStackPremises{
        \\forall i \\in I. \\Gamma, x\_i : A\_i \\vdash t\_i \\rhd
          \\ensuremath{\\mathsf{L}}, (\\ell\_j(A\_j),)\_{j \\in I}, \\kappa(B)
      }{
        \\Gamma, y : B \\vdash s \\rhd
          \\ensuremath{\\mathsf{L}}, (\\ell\_j(A\_j),)\_{j \\in I}, \\kappa(B),
            (\\ell\_{j\'}\'(A\_{j\'}\'),)\_{j\' \\in I\'},
      }{
        \\forall i\' \\in I\'. \\Gamma, x\_{i\'}\' : A\_{i\'}\' \\vdash t\_{i\'}\' \\rhd
          \\ensuremath{\\mathsf{L}}, (\\ell\_j(A\_j),)\_{j \\in I}, \\kappa(B),
            (\\ell\_{j\'}\'(A\_{j\'}\'),)\_{j\' \\in I\'}
      }
    }
    {
      \\prfStackPremises{
        \\Gamma \\vdash
          r\\;\\ensuremath{\\mathsf{where}}\\;(\\ell\_i(x\_i) :\\{t\_i\\},)\_{i \\in I},
            \\kappa(y) :\\{s\\;\\ensuremath{\\mathsf{where}}\\;(\\ell\_{i\'}\'(x\_{i\'}\') :\\{t\_{i\'}\'\\},)\_{i\' \\in I\'}\\}
      }{
        \\hspace{8em}
        \\approx r\\;\\ensuremath{\\mathsf{where}}\\;(\\ell\_i(x\_i) :\\{t\_i\\},)\_{i \\in I},
            \\kappa(y) :\\{s\\}, (\\ell\_{i\'}\'(x\_{i\'}\') :\\{t\_{i\'}\'\\},)\_{i\' \\in I\'}
        \\rhd \\ensuremath{\\mathsf{L}}
      }
    }
    \\label{eqn:where-fusion-2}\$\$ <lem:where-fusion>

]
#block[
#emph[Proof.] We begin with cfg-fuse$""_1$. Let
$sans(R) = \( ell_j \( A_j \) \, \)_j$,
$sans(K) = \( kappa_k \( B_k \) \, \)_k$,
$S = \( kappa_i \( y_i \) : { s_i } \, \)_i$,
$T = \( ell_i \( x_i \) : { t_i } \, \)_j$, and
$D_S = sans(l s e m)_(Gamma \, sans(L) \, sans(R)) \( S \)$,
$D_T = sans(l s e m)_(Gamma \, sans(L)) \( T \)$,
$D_G = sans(l s e m)_(Gamma \, sans(L)) \( S \, T \)$ We have that
$  & bracket.l Gamma tack.r \( r #h(0em) sans(w h e r e) #h(0em) S \) #h(0em) sans(w h e r e) #h(0em) T gt.tri sans(L) bracket.r\
 & = sans(l e t) \( sans(l e t) \( sans(e s e m)_(Gamma \, \( sans(L) \, sans(R) \)) \( r \) \) ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( D_S \) \] ; alpha_(bracket.l sans(L) bracket.r + Sigma_j bracket.l A_j bracket.r)^(+) \) ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( D_T \) \]\
 & = sans(l e t) \( sans(e s e m)_(Gamma \, \( sans(L) \, sans(R) \)) \( r \) \) ; sans(r l e t) \( delta^(- 1) ; \[ pi_r \, sans(r f i x) \( D_S \) \] ; alpha_(bracket.l sans(L) bracket.r + Sigma_j bracket.l A_j bracket.r)^(+) \) ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( D_T \) \]\
 & = sans(l e t) \( sans(e s e m)_(Gamma \, \( sans(L) \, sans(R) \)) \( r \) \) ; delta^(- 1) ; \[ sans(r l e t) \( pi_r ; alpha_(bracket.l sans(L) bracket.r + Sigma_j bracket.l A_j bracket.r)^(+) \) \, sans(r l e t) \( sans(r f i x) \( D_S \) ; alpha_(bracket.l sans(L) bracket.r + Sigma_j bracket.l A_j bracket.r)^(+) \) \] ; delta^(- 1) ; \[ pi_r \, sans(r f i x) \( D_T \) \]\
 & = sans(l e t) \( sans(e s e m)_(Gamma \, \( sans(L) \, sans(R) \)) \( r \) \) ; \[\
 & #h(2em) pi_r ; alpha_(bracket.l sans(L) bracket.r + Sigma_j bracket.l A_j bracket.r)^(+) gt.double_() \[ pi_r \, sans(r f i x) \( D_T \) \]_(bracket.l Gamma bracket.r) \,\
 & #h(2em) sans(r f i x) \( D_S \) ; alpha_(bracket.l sans(L) bracket.r + Sigma_j bracket.l A_j bracket.r)^(+) gt.double_() \[ pi_r \, sans(r f i x) \( D_T \) \]_(bracket.l Gamma bracket.r) \]_(bracket.l Gamma bracket.r)\
 & = sans(l e t) \( sans(e s e m)_(Gamma \, \( sans(L) \, sans(R) \)) \( r \) \) ; \[\
 & #h(2em) alpha_(bracket.l sans(L) bracket.r + Sigma_j bracket.l A_j bracket.r)^(R +) gt.double_() \[ pi_r \, sans(r f i x) \( D_T \) \]_(bracket.l Gamma bracket.r) \,\
 & #h(2em) sans(r f i x) \( D_S \) ; alpha_(bracket.l sans(L) bracket.r + Sigma_j bracket.l A_j bracket.r)^(+) gt.double_() \[ pi_r \, sans(r f i x) \( D_T \) \]_(bracket.l Gamma bracket.r) \]_(bracket.l Gamma bracket.r)\
 & = sans(l e t) \( Gamma tack.r r gt.tri sans(L) \, sans(R) \, sans(K) \) ; alpha_(bracket.l sans(L) bracket.r + \( bracket.l R bracket.r + Sigma_j bracket.l A_j bracket.r \))^(sans(R) +) gt.double_() \[ pi_r \,\
 & #h(2em) \[ sans(r f i x) \( D_T \) \, sans(r f i x) \( D_S \) ; alpha_(bracket.l sans(L) bracket.r + Sigma_j bracket.l A_j bracket.r)^(+) gt.double_() \[ pi_r \, sans(r f i x) \( D_T \) \]_(bracket.l Gamma bracket.r) \]_(bracket.l Gamma bracket.r) \]_(bracket.l Gamma bracket.r)\
 & = sans(l e t) \( Gamma tack.r r gt.tri sans(L) \, sans(R) \, sans(K) ; alpha_(bracket.l sans(L) bracket.r + \( bracket.l R bracket.r + Sigma_j bracket.l A_j bracket.r \))^(sans(R) +) \) ; delta^(- 1) ;\
 & #h(2em) \[ pi_r \, \[ sans(r f i x) \( D_T \) \, sans(r f i x) \( D_S \) ; alpha_(bracket.l sans(L) bracket.r + Sigma_j bracket.l A_j bracket.r)^(+) gt.double_() \[ pi_r \, sans(r f i x) \( D_T \) \]_(bracket.l Gamma bracket.r) \]_(bracket.l Gamma bracket.r) \]\
 & = sans(l e t) \( sans(e s e m)_(Gamma \, sans(L)) \( r \) \) ; delta^(- 1) ; \[ pi_r \, \[ sans(r f i x) \( D_T \) \, sans(r f i x) \( D_S \) ; alpha_(bracket.l sans(L) bracket.r + Sigma_j bracket.l A_j bracket.r)^(+) gt.double_() \[ pi_r \, sans(r f i x) \( D_T \) \]_(bracket.l Gamma bracket.r) \]_(bracket.l Gamma bracket.r) \]\
 $ For this to be equal to
$bracket.l Gamma tack.r r #h(0em) sans(w h e r e) #h(0em) S \, T gt.tri sans(L) bracket.r$,
it therefore suffices to show that
$ sans(r f i x) \( D_G \) & = \[ sans(r f i x) \( D_T \) \, sans(r f i x) \( D_S \) ; alpha_(bracket.l sans(L) bracket.r + Sigma_j bracket.l A_j bracket.r)^(+) gt.double_() \[ pi_r \, sans(r f i x) \( D_T \) \]_(bracket.l Gamma bracket.r) \]_(bracket.l Gamma bracket.r) $<eqn:dgdt>
We note that, by re-association and weakening, we have that
$ D_G & = bracket.l Gamma bracket.r times alpha_(bracket.l sans(R) bracket.r + bracket.l sans(K) bracket.r)^(+) ; delta^(- 1) ; \[ delta_Sigma^(- 1) ; \[ bracket.l Gamma \, x_i : A_i tack.r t_i gt.tri sans(L) \, sans(R) \, sans(K) bracket.r ; alpha_(bracket.l sans(L) bracket.r + Sigma_j bracket.l C_j bracket.r)^(+) \, \]_i \, D_S \]\
 & = bracket.l Gamma bracket.r times alpha_(bracket.l sans(R) bracket.r + bracket.l sans(K) bracket.r)^(+) ; delta^(- 1) ; \[ D_T ; bracket.l sans(L) bracket.r + \( alpha_(sans(R))^(+) ; bracket.l sans(R) lt.eq sans(R \, K) bracket.r ; alpha_(Sigma_i bracket.l C_i bracket.r)^(+) \) \, D_S \]\
 & = bracket.l Gamma bracket.r times alpha_(bracket.l sans(R) bracket.r + bracket.l sans(K) bracket.r)^(+) ; delta^(- 1) ; \[ D_T ; bracket.l sans(L) bracket.r + \( iota_(l \, Sigma_i bracket.l A_i bracket.r + Sigma_i bracket.l B_i bracket.r) ; alpha_(Sigma_i bracket.l C_i bracket.r)^(+) \) \, D_S \]\
 & = alpha_(sans(R) + sans(K))^(+ bracket.l Gamma bracket.r) gt.double_() \[ D_T gt.double_() bracket.l sans(L) bracket.r +_R \( iota_l^(bracket.l Gamma bracket.r) ; alpha_(Sigma_i bracket.l C_i bracket.r)^(+) \) \, \]_(bracket.l Gamma bracket.r) $<eqn:dg-rhs>
where $C_(1 . . k) = A_(1 . . k)$ and
$C_(k + 1 . . n) = B_(1 . . n - k)$. We note in particular that
$bracket.l sans(R) lt.eq sans(R \, K) bracket.r$ is up to
isomorphism the left injection
$iota_l : Sigma_i bracket.l A_i bracket.r arrow.r Sigma_i bracket.l A_i bracket.r + Sigma_i bracket.l B_i bracket.r$.
We can now derive Equation~#todo[Resolve source reference `eqn:dgdt` during integration.], and hence the soundness of
cfg-fuse$""_1$, via the string-diagrams in
Figure~#todo[Resolve source reference `fig:string-diagram-fusion` during integration.], which are drawn in the co-Kleisli
category inducted by $bracket.l Gamma bracket.r$.
cfg-fuse$""_2$ then follows by repeated application of cfg-fuse$""_1$,
as desired.~◻

]
#figure([#figure([],
    caption: [
      $sans(r f i x) \( D_G \)$, with $D_G$ drawn as per the right of
      Eqn.~#todo[Resolve source reference `eqn:dg-rhs` during integration.]
    ]
  )
  <fig:rfix-dg>

  #figure([],
    caption: [
      Equivalent to #todo[Resolve source reference `fig:rfix-dg` during integration.] by isotopy and associativity of the
      codiagonal. We highlight $sans(r f i x) \( D_T \)$, which is used
      in the next step.
    ]
  )
  <fig:rfix-isotopy>

  #figure([],
    caption: [

      $\[ sans(r f i x) \( D_T \) \, sans(r f i x) \( D_S \) ; alpha_(bracket.l sans(L) bracket.r + Sigma_j bracket.l A_j bracket.r)^(+) gt.double_() \[ pi_r \, sans(r f i x) \( D_T \) \]_(bracket.l Gamma bracket.r) \]_(bracket.l Gamma bracket.r)$.
      \
      Equivalent to #todo[Resolve source reference `fig:rfix-isotopy` during integration.] by duplication of
      $sans(r f i x) \( D_T \)$.
    ]
  )
  <fig:rfix-lhs>

  ],
  caption: [
    String diagrams validating the soundness of cfg-fuse$""_1$
    (Eqn.~#todo[Resolve source reference `eqn:where-fusion-1` during integration.]), drawn in the co-Kleisli category induced
    by $bracket.l Gamma bracket.r$
  ]
)
<fig:string-diagram-fusion>

== Completeness
<completeness>
<proof:complete-expr>

#block[
#emph[Proof.] We begin by showing $sans(T h)^times \( Gamma \)$
is an #lssa expression model by validating all the
equations for a distributive Freyd category. These are formalized as
follows:

- $sans(T h)^times \( Gamma \)$ is a category: formalized in
  `Rewrite/Term/Compose/Seq.lean`

- $sans(T h)^times \( Gamma \)$ is a Freyd category: formalized
  in `Rewrite/Term/Compose/Product.lean`

- $sans(T h)^times \( Gamma \)$ has coproducts: formalized in
  `Rewrite/Term/Compose/Sum.lean`

- $sans(T h)^times \( Gamma \)$ is distributive: formalized in
  `Rewrite/Term/Compose/Distrib.lean`

We then prove that the packing of each type constructor is equivalent to
its denotational semantics in $sans(T h)^times \( Gamma \)$ in
`Rewrite/Term/Compose/Completeness.lean`. Finally, we show that packing
and unpacking are mutual inverses for $Gamma$ pure in
`Term.Eqv.packed_unpacked` and `Term.Eqv.unpacked_packed` in
`Rewrite/Term/Structural/Product.lean`, completing the proof of
initiality.~◻

]
<proof:complete-reg>

#block[
#emph[Proof.] We begin by showing $sans(T h) \( Gamma \, sans(L) \)$ is
an #lssa region model by validating all the equations
for a distributive Elgot category. These are formalized as follows:

- $sans(T h) \( Gamma \, sans(L) \)$ is a category: formalized in
  `Rewrite/Region/Compose/Seq.lean`

- $sans(T h) \( Gamma \, sans(L) \)$ is a Freyd category: formalized in
  `Rewrite/Region/Compose/Product.lean`

- $sans(T h) \( Gamma \, sans(L) \)$ has coproducts: formalized in
  `Rewrite/Region/Compose/Sum.lean`

- $sans(T h) \( Gamma \, sans(L) \)$ is distributive: formalized in
  `Rewrite/Region/Compose/Distrib.lean`

- $sans(T h) \( Gamma \, sans(L) \)$ is a strong Elgot category:
  formalized in `Rewrite/Region/Compose/Elgot.lean`

We then prove that the packing of each type constructor is equivalent to
its denotational semantics in $sans(T h) \( Gamma \, sans(L) \)$ in
`Rewrite/Region/Compose/Completeness.lean`. Finally, we show that
packing and unpacking are mutual inverses for $Gamma$ pure in
`Region.Eqv.packed_unpacked` and `Region.Eqv.unpacked_packed` in
`Rewrite/Region/Structural.lean`, completing the proof of initiality.~◻

]
