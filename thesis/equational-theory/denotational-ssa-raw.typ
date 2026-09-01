// VERBATIM TRANSCRIPTION — markup translated from LaTeX to Typst.
// Source: papers/isotope/denotational-semantics-of-ssa.tex @ afa82558acf643f53a3e038e635ed9520ace88c6
// Coverage: lines 1615–3084, “Equational Theory”.
#import "/lib/prelude.typ": *

#set math.equation(numbering: "(1)")
= Equational Theory
<sec:equations>
== Expressions
<expressions>
We can now give an equational theory for #lssa
expressions. In particular, we will inductively define an equivalence
relation $Gamma tack.r_epsilon.alt a approx a' : A$ on terms $a \, a'$
for each context $Gamma$, effect $epsilon.alt$, and type $A$. For each
of the rules we will present, we assume the rule is valid if and only if
#emph[both sides] of the rule are well-typed. We also assume that
variables are $alpha$-converted as appropriate to avoid shadowing; our
formalization uses de Bruijn indices, but we stick with names in this
exposition for simplicity.

The rules for this relation can be roughly split into #emph[rewriting
rules], which denote when two particular expressions have equivalent
semantics, and #emph[congruence rules], which govern how rewrites can
be composed to enable equational reasoning. In particular, our
congruence rules, given in Figure~@fig:ssa-expr-congr-rules, consist of:

- refl, symm, trans, which state that
  $Gamma tack.r_epsilon.alt dot.op approx dot.op : A$ is reflexive,
  transitive, and symmetric respectively for each choice of
  $Gamma \, epsilon.alt \, A$, and therefore an equivalence relation.

- let$""_1$, let$""_2$, pair, inl, inr, case, and abort, which state
  that $Gamma tack.r_epsilon.alt dot.op approx dot.op : A$ is a
  #emph[congruence] with respect to the corresponding expression
  constructor, and, in particular, that the expression constructors are
  well-defined functions on the quotient of expressions up to $approx$.

We also include the following #emph[type-directed] rules as part of our
congruence relation:

- initial, which equates #emph[all] terms in a context containing the
  empty type $upright(bold(0))$, since we will deem any such context to
  be #emph[unreachable] by control flow. In particular, any instruction
  or function call returning $upright(bold(0))$ is assumed to diverge.

- terminal, which equates all #emph[pure] terms of unit type
  $upright(bold(1))$. Note that #emph[impure] terms may be disequal,
  since while their result values are the same, their side effects may
  differ!

#figure([
  #rule-set(
    prooftree(rule(label: msc("refl"), eff-typing($Gamma$, $epsilon$, $a$, $A$), eff-typing($Gamma$, $epsilon$, $a approx a$, $A$))),
    prooftree(rule(label: msc("trans"), eff-typing($Gamma$, $epsilon$, $a approx b$, $A$), eff-typing($Gamma$, $epsilon$, $b approx c$, $A$), eff-typing($Gamma$, $epsilon$, $a approx c$, $A$))),
    prooftree(rule(label: msc("symm"), eff-typing($Gamma$, $epsilon$, $a approx b$, $A$), eff-typing($Gamma$, $epsilon$, $b approx a$, $A$))),
    prooftree(rule(label: msc("let1"), eff-typing($Gamma$, $epsilon$, $a approx a'$, $A$), eff-typing($Gamma, x : A$, $epsilon$, $b approx b'$, $B$), eff-typing($Gamma$, $epsilon$, $sans("let") x = a; b approx sans("let") x = a'; b'$, $B$))),
    prooftree(rule(label: msc("pair"), eff-typing($Gamma$, $epsilon$, $a approx a'$, $A$), eff-typing($Gamma$, $epsilon$, $b approx b'$, $B$), eff-typing($Gamma$, $epsilon$, $(a, b) approx (a', b)$, $A times B$))),
    prooftree(rule(label: msc("let2"), eff-typing($Gamma$, $epsilon$, $e approx e'$, $A times B$), eff-typing($Gamma, x : A, y : B$, $epsilon$, $c approx c'$, $C$), eff-typing($Gamma$, $epsilon$, $sans("let") (x, y) = e; c approx sans("let") (x, y) = e'; c'$, $C$))),
    prooftree(rule(label: msc("inl"), eff-typing($Gamma$, $epsilon$, $a approx a'$, $A$), eff-typing($Gamma$, $epsilon$, $iota_l a approx iota_l a'$, $A + B$))),
    prooftree(rule(label: msc("inr"), eff-typing($Gamma$, $epsilon$, $b approx b'$, $B$), eff-typing($Gamma$, $epsilon$, $iota_r b approx iota_r b'$, $A + B$))),
    prooftree(rule(label: msc("case"), eff-typing($Gamma$, $epsilon$, $e approx e'$, $A + B$), eff-typing($Gamma, x : A$, $epsilon$, $a approx a'$, $C$), eff-typing($Gamma, y : B$, $epsilon$, $b approx b'$, $C$), eff-typing($Gamma$, $epsilon$, $sans("case") e {iota_l x : a, iota_r y : b} approx sans("case") e' {iota_l x : a', iota_r y : b'}$, $C$))),
    prooftree(rule(label: msc("abort"), eff-typing($Gamma$, $epsilon$, $a approx a'$, $upright(bold(0))$), eff-typing($Gamma$, $epsilon$, $sans("abort") a approx sans("abort") a'$, $A$))),
    prooftree(rule(label: msc("initial"), eff-typing($Gamma$, $epsilon$, $a$, $A$), eff-typing($Gamma$, $epsilon$, $a'$, $A$), eff-typing($Gamma$, $bot$, $e$, $upright(bold(0))$), eff-typing($Gamma$, $epsilon$, $a approx a'$, $A$))),
    prooftree(rule(label: msc("terminal"), eff-typing($Gamma$, $bot$, $a$, $upright(bold(1))$), eff-typing($Gamma$, $bot$, $a'$, $upright(bold(1))$), eff-typing($Gamma$, $epsilon$, $a approx a'$, $upright(bold(1))$))),
  )
], caption: [Congruence rules for #lssa expressions])
<fig:ssa-expr-congr-rules>

We may group the rest of our rules according to the relevant
constructor, i.e. $sans(l e t)$ (unary and binary) and $sans(c a s e)$.
In particular, for unary $sans(l e t)$, we have the following rules,
summarized in Figure~@fig:ssa-unary-let-expr

- let$""_1$-$beta$, which allows us to substitute the bound variable in
  $x$ the let-statement $kw("let") med x = a ; #h(0em) b$ with its
  definition $a$, yielding $\[ a \/ x \] b$. Note that we require
  $Gamma tack.r_tack.t a : A$; i.e., $a$ must be #emph[pure].

- let$""_1$-$eta$, which is the standard $eta$-rule for $sans(l e t)$.
  This is included as a separate rule since, while it follows trivially
  from $beta$ for pure $a$, we also want to consider #emph[impure]
  expressions.

- Rules let$""_1$-op, let$""_1$-let$""_1$, let$""_1$-let$""_2$,
  let$""_1$-abort, and let$""_1$-case which allow us to "pull" a
  let-statement out of any of the other expression constructors;
  operationally, this is saying that the bound expression we pull out is
  evaluated before the rest of the $sans(l e t)$-binding.

  For example, let$""_1$-case says that, if both
  $kw("let") med z = kw("case") med e #h(0em) { iota_l #h(0em) x : a \, iota_r #h(0em) y : b } ; #h(0em) d$
  and
  $kw("case") med e #h(0em) { iota_l #h(0em) x : kw("let") med z = a ; #h(0em) d \, iota_r #h(0em) y : kw("let") med z = b ; #h(0em) d } y$,
  are well typed, then both must have the same behaviour:

  + Compute $e$

  + If $e = iota_l #h(0em) e_l$, compute $\[ e_l \/ x \] a$, else, if
    $e = iota_r #h(0em) e_r$, compute $\[ e_r \/ y \] b$; store this
    value as $z$

  + Compute $d$ given our value for $z$

  Note in particular that, since both sides are well-typed, $d$ cannot
  depend on either $x$ or $y$.

#figure([
  #rule-set(
    prooftree(rule(label: msc("let1-beta"), eff-typing($Gamma$, $bot$, $a$, $A$), eff-typing($Gamma, x : A$, $epsilon$, $b$, $B$), eff-typing($Gamma$, $epsilon$, $sans("let") x = a; b approx [b/x]a$, $B$))),
    prooftree(rule(label: msc("let1-eta"), eff-typing($Gamma$, $epsilon$, $a$, $A$), eff-typing($Gamma$, $epsilon$, $sans("let") x = a; x approx a$, $A$))),
    prooftree(rule(label: msc("let1-op"), $f in cal(I)_epsilon(A, B)$, eff-typing($Gamma$, $epsilon$, $a$, $A$), eff-typing($Gamma, y : B$, $epsilon$, $c$, $C$), eff-typing($Gamma$, $epsilon$, $sans("let") y = f a; c approx sans("let") x = a; sans("let") y = f x; c$, $C$))),
    prooftree(rule(label: msc("let1-let1"), eff-typing($Gamma$, $epsilon$, $a$, $A$), eff-typing($Gamma, x : A$, $epsilon$, $b$, $B$), eff-typing($Gamma, y : B$, $epsilon$, $c$, $C$), eff-typing($Gamma$, $epsilon$, $sans("let") y = (sans("let") x = a; b); c approx sans("let") x = a; sans("let") y = b; c$, $C$))),
    prooftree(rule(label: msc("let1-let2"), eff-typing($Gamma$, $epsilon$, $e$, $A times B$), eff-typing($Gamma, x : A, y : C$, $epsilon$, $c$, $C$), eff-typing($Gamma, z : C$, $epsilon$, $d$, $D$), eff-typing($Gamma$, $epsilon$, $sans("let") z = (sans("let") (x, y) = e; c); d approx sans("let") (x, y) = e; sans("let") z = c; d$, $D$))),
    prooftree(rule(label: msc("let1-abort"), eff-typing($Gamma$, $epsilon$, $a$, $upright(bold(0))$), eff-typing($Gamma, y : A$, $epsilon$, $b$, $B$), eff-typing($Gamma$, $epsilon$, $sans("let") y = sans("abort") b; b approx sans("let") x = a; sans("let") y = sans("abort") x; b$, $B$))),
    prooftree(rule(label: msc("let1-case"), eff-typing($Gamma$, $epsilon$, $e$, $A + B$), eff-typing($Gamma, x : A$, $epsilon$, $a$, $C$), eff-typing($Gamma, y : B$, $epsilon$, $b$, $C$), eff-typing($Gamma, z : C$, $epsilon$, $d$, $D$), eff-typing($Gamma$, $epsilon$, $sans("let") z = (sans("case") e {iota_l x : a, iota_r y : b}); d approx sans("case") e {iota_l x : sans("let") z = a; d, iota_r y : sans("let") z = b; d}$, $D$))),
  )
], caption: [Rewriting rules for #lssa unary $sans("let")$ expressions])
<fig:ssa-unary-let-expr>

Handling the other type constructors is a little simpler: by providing a
"binding" rule, we generally only need to specify how to interact with
$sans(l e t)_1$, as well as an $eta$ and $beta$ rule; interactions with
the other constructors can then be derived. For example, consider the
rules for $sans(l e t)_2$ given in @fig:ssa-let2-case-expr; we have:

- let$""_2$-$eta$, which is the standard $eta$-rule for binary
  $sans(l e t)$-bindings

- let$""_2$-pair, which acts like a slightly generalized $beta$-rule,
  since we can derive $beta$ reduction as follows: given pure
  $Gamma tack.r_tack.t a : A$ and $Gamma tack.r_tack.t b : B$, we have
  $ \( kw("let") med \( x \, y \) = \( a \, b \) ; #h(0em) c \) approx \( kw("let") med x = a ; #h(0em) kw("let") med y = b ; #h(0em) c \) approx \( \[ a \/ x \] \( kw("let") med y = b ; #h(0em) c \) \) approx \( \[ a \/ x \] \[ b \/ y \] c \) $
  We state the rule in a more general form to allow for impure $a$ and
  $b$, as well as to simplify certain proofs.

- let$""_2$-bind, which allows us to "pull" out the bound value of a
  binary $sans(l e t)$-expression into its own unary
  $sans(l e t)$-expression; operationally, this just says that we
  execute the bound value before executing the binding itself.

This is enough to allow us to define our interactions with the other
expression constructors: for example, to show that we can lift an
operation $f$ out of a binary $sans(l e t)$-binding, rather than adding
a separate rule, we can instead derive (types omitted for simplicity) it
from let$""_2$-bind and let$""_1$-op as follows:
$ \( kw("let") med \( x \, y \) = f #h(0em) a ; #h(0em) b \) & approx \( kw("let") med z_f = f #h(0em) a ; #h(0em) kw("let") med \( x \, y \) = z ; #h(0em) b \)\
 & approx \( kw("let") med z_a = a ; #h(0em) kw("let") med z_f = f #h(0em) z_a ; #h(0em) kw("let") med \( x \, y \) = z ; #h(0em) b \)\
 & approx \( kw("let") med z_a = a ; #h(0em) kw("let") med \( x \, y \) = f #h(0em) z_a ; #h(0em) b \) $

#figure([
  #rule-set(
    prooftree(rule(label: msc("let2-pair"), eff-typing($Gamma$, $epsilon$, $a$, $A$), eff-typing($Gamma$, $epsilon$, $b$, $B$), eff-typing($Gamma, x : A, y : B$, $epsilon$, $c$, $C$), eff-typing($Gamma$, $epsilon$, $sans("let") (x, y) = (a, b); c approx sans("let") x = a; sans("let") y = b; c$, $C$))),
    prooftree(rule(label: msc("let2-eta"), eff-typing($Gamma$, $epsilon$, $e$, $A times B$), eff-typing($Gamma$, $epsilon$, $sans("let") (x, y) = e; (x, y) approx e$, $A times B$))),
    prooftree(rule(label: msc("let2-bind"), eff-typing($Gamma$, $epsilon$, $e$, $A times B$), eff-typing($Gamma, x : A, y : B$, $epsilon$, $c$, $C$), eff-typing($Gamma$, $epsilon$, $sans("let") (x, y) = e; c approx sans("let") z = e; sans("let") (x, y) = z; c$, $C$))),
    prooftree(rule(label: msc("case-inl"), eff-typing($Gamma$, $epsilon$, $a$, $A$), eff-typing($Gamma, x : A$, $epsilon$, $c$, $C$), eff-typing($Gamma, y : B$, $epsilon$, $d$, $C$), eff-typing($Gamma$, $epsilon$, $sans("case") iota_l a {iota_l x : c, iota_r y : d} approx sans("let") x = a; c$, $C$))),
    prooftree(rule(label: msc("case-inr"), eff-typing($Gamma$, $epsilon$, $b$, $B$), eff-typing($Gamma, x : A$, $epsilon$, $c$, $C$), eff-typing($Gamma, y : B$, $epsilon$, $d$, $C$), eff-typing($Gamma$, $epsilon$, $sans("case") iota_r b {iota_l x : c, iota_r y : d} approx sans("let") y = b; d$, $C$))),
    prooftree(rule(label: msc("case-eta"), eff-typing($Gamma$, $epsilon$, $e$, $A + B$), eff-typing($Gamma$, $epsilon$, $sans("case") e {iota_l x : iota_l x, iota_r y : iota_r y} approx e$, $A + B$))),
    prooftree(rule(label: msc("case-bind"), eff-typing($Gamma$, $epsilon$, $e$, $A + B$), eff-typing($Gamma, x : A$, $epsilon$, $c$, $C$), eff-typing($Gamma, y : B$, $epsilon$, $d$, $C$), eff-typing($Gamma$, $epsilon$, $sans("case") e {iota_l x : c, iota_r y : d} approx sans("let") z = e; sans("case") z {iota_l x : c, iota_r y : d}$, $C$))),
  )
], caption: [Rewriting rules for #lssa binary $sans("let")$ and $sans("case")$ expressions])
<fig:ssa-let2-case-expr>

Similarly, it is enough to give $eta$, $beta$, and binding rules for
case expressions. In particular, we have that

- case-inl and case-inr serve as $beta$-reduction rules, telling us that
  $sans(c a s e)$-expressions given an injection as an argument have the
  expected operational behaviour. Note that we reduce to a
  $sans(l e t)$-expression rather than perform a substitution to allow
  for impure discriminants.

- case-$eta$ is the standard $eta$-rule for $sans(c a s e)$-expressions.

- case-bind allows us to "pull" out the bound value of the discriminant
  into it's own $sans(l e t)$-expression; again, operationally, this
  just says that we need to evaluate the discriminant before executing
  the $sans(c a s e)$-expression.

It's interesting that this is enough, along with the let-case rule and
friends, to derive the distributivity properties we would expect
well-behaved $sans(c a s e)$-expressions to have. For example, we have
that
$ f \( kw("case") med e #h(0em) { iota_l #h(0em) x : a \, iota_r #h(0em) y : b } \) & approx \( kw("let") med z = kw("case") med e #h(0em) { iota_l #h(0em) x : a \, iota_r #h(0em) y : b } ; #h(0em) f #h(0em) z \)\
 & approx kw("case") med e #h(0em) { iota_l #h(0em) x : kw("let") med z = a ; #h(0em) f #h(0em) z \, iota_r #h(0em) y : kw("let") med z = b ; #h(0em) f #h(0em) z }\
 & approx kw("case") med e #h(0em) { iota_l #h(0em) x : f #h(0em) a \, iota_r #h(0em) y : f #h(0em) b } $
and likewise for more complicated distributivity properties involving,
e.g., $sans(l e t)$-bindings.

The case for the other constructors is even more convenient: no
additional rules are required at all to handle operations, pairs, and
injections. For example, we can derive the expected bind-rule for
operations as follows:
$ f #h(0em) a approx \( kw("let") med y = f #h(0em) a ; #h(0em) y \) approx \( kw("let") med x = a ; #h(0em) kw("let") med y = f #h(0em) x ; #h(0em) y \) approx \( kw("let") med x = a ; #h(0em) f #h(0em) x \) $

This completes the equational theory for #lssa terms;
in @ssec:completeness, we will show that this is enough to state
a completeness theorem.

== Regions
<regions>
We now come to the equational theory for regions, which is similar to
that for terms, except that we also need to support control-flow graphs.
As before, we will split our rules into a set of #emph[congruence rules]
and, for each region constructor, #emph[rewriting rules] based on that
constructor's semantics. Our congruence rules, given in
Figure~@fig:ssa-reg-congr-rules, are quite standard; we have:

- As for terms, refl, trans, and symm state that
  $Gamma tack.r dot.op approx dot.op gt.tri sans(L)$ is an equivalence
  relation for all $Gamma$, $sans(L)$.

- Similarly, let$""_1$, let$""_2$, case, and cfg state that
  $Gamma tack.r dot.op approx dot.op gt.tri sans(L)$ is a congruence
  over the respective region constructors; #emph[as well as] the
  equivalence relation on terms
  $Gamma tack.r_epsilon.alt dot.op approx dot.op : A$.

- initial states that any context containing the empty type
  $upright(bold(0))$ equates all regions, by a similar reasoning to the
  rules for terms. Note that we do not require an analogue to the
  terminal rule (for example, for regions targeting
  $sans(L) = ell \( upright(bold(1)) \)$), since it will follow from the
  version for terms; this is good, since the concept of a "pure" region
  has not yet been defined.

Our rewriting rules for unary $sans(l e t)$-statements, given in
Figure~@fig:ssa-reg-unary-let, are analogous to those for unary
$sans(l e t)$-expressions:

- let$""_1$-$beta$ allows us to perform $beta$-reduction of #emph[pure]
  expressions into regions; unlike for terms, we do not need an
  $eta$-rule

- Exactly like for $sans(l e t)$-expressions, let$""_1$-op,
  let$""_1$-let$""_1$, let$""_1$-let$""_2$, let$""_1$-abort, and
  let$""_1$-case allow us to pull out nested subexpressions of the bound
  value of a $sans(l e t)$-statement into their own unary
  $sans(l e t)$-statement

Similarly to expressions, binary $sans(l e t)$-statements and
$sans(c a s e)$-statements need only the obvious $beta$ rule and binding
rule, with all the interactions with other constructors derivable; these
rules are given in Figure~@fig:ssa-reg-let2-case-expr Note in
particular that $eta$-rules are not necessary, as these are derivable
from binding and the $eta$-rules for expressions.

#figure([
  #rule-set(
    prooftree(rule(label: msc("refl"), $Gamma tack.r r gt.tri sans("L")$, $Gamma tack.r r approx r gt.tri sans("L")$)),
    prooftree(rule(label: msc("trans"), $Gamma tack.r r approx s gt.tri sans("L")$, $Gamma tack.r s approx t gt.tri sans("L")$, $Gamma tack.r r approx t gt.tri sans("L")$)),
    prooftree(rule(label: msc("symm"), $Gamma tack.r r approx s gt.tri sans("L")$, $Gamma tack.r s approx r gt.tri sans("L")$)),
    prooftree(rule(label: msc("let1"), eff-typing($Gamma$, $epsilon$, $a approx a'$, $A$), $Gamma, x : A tack.r r approx r' gt.tri sans("L")$, $Gamma tack.r sans("let") x = a; r approx sans("let") x = a'; r' gt.tri sans("L")$)),
    prooftree(rule(label: msc("let2"), eff-typing($Gamma$, $epsilon$, $e approx e'$, $A times B$), $Gamma, x : A, y : B tack.r r approx r' gt.tri sans("L")$, $Gamma tack.r sans("let") (x, y) = e; r approx sans("let") (x, y) = e'; r' gt.tri sans("L")$)),
    prooftree(rule(label: msc("case"), eff-typing($Gamma$, $epsilon$, $e approx e'$, $A + B$), $Gamma, x : A tack.r r approx r' gt.tri sans("L")$, $Gamma, y : B tack.r s approx s' gt.tri sans("L")$, $Gamma tack.r sans("case") e {iota_l x : r, iota_r y : s} approx sans("case") e' {iota_l x : r', iota_r y : s'} gt.tri sans("L")$)),
    prooftree(rule(label: msc("cfg"), $Gamma tack.r r approx r' gt.tri sans("L"), (ell_i(A_i),)_(i in I)$, $forall i in I. Gamma, x_i : A_i tack.r t_i approx t_i' gt.tri sans("L"), (ell_j(A_j),)_(j in I)$, $Gamma tack.r r sans("where") (ell_i(x_i : A_i) : {t_i},)_(i in I) approx r' sans("where") (ell_i(x_i : A_i) : {t_i'},)_(i in I) gt.tri sans("L")$)),
    prooftree(rule(label: msc("initial"), $Gamma tack.r r gt.tri sans("L")$, $Gamma tack.r s gt.tri sans("L")$, $exists x, Gamma x = upright(bold(0))$, $Gamma tack.r r approx s gt.tri sans("L")$)),
  )
], caption: [Congruence rules for #lssa regions])
<fig:ssa-reg-congr-rules>

#figure([
  #rule-set(
    prooftree(rule(label: msc("let1-beta"), eff-typing($Gamma$, $bot$, $a$, $A$), $Gamma, x : A tack.r r gt.tri sans("L")$, $Gamma tack.r sans("let") x = a; r approx [a/x]r gt.tri sans("L")$)),
    prooftree(rule(label: msc("let1-op"), $f in cal(I)_epsilon(A, B)$, eff-typing($Gamma$, $epsilon$, $a$, $A$), $Gamma, y : B tack.r r gt.tri sans("L")$, $Gamma tack.r sans("let") y = f a; r approx sans("let") x = a; sans("let") y = f x; r gt.tri sans("L")$)),
    prooftree(rule(label: msc("let1-let1"), eff-typing($Gamma$, $epsilon$, $a$, $A$), eff-typing($Gamma, x : A$, $epsilon$, $b$, $B$), $Gamma, y : B tack.r r gt.tri sans("L")$, $Gamma tack.r sans("let") y = (sans("let") x = a; b); r approx sans("let") x = a; sans("let") y = b; r gt.tri sans("L")$)),
    prooftree(rule(label: msc("let1-let2"), eff-typing($Gamma$, $epsilon$, $e$, $A times B$), eff-typing($Gamma, x : A, y : B$, $epsilon$, $c$, $C$), $Gamma, z : C tack.r r gt.tri sans("L")$, $Gamma tack.r sans("let") z = (sans("let") (x, y) = e; c); r approx sans("let") (x, y) = e; sans("let") z = c; r gt.tri sans("L")$)),
    prooftree(rule(label: msc("let1-case"), eff-typing($Gamma$, $epsilon$, $e$, $A + B$), eff-typing($Gamma, x : A$, $epsilon$, $a$, $C$), eff-typing($Gamma, y : B$, $epsilon$, $b$, $C$), $Gamma, z : C tack.r r gt.tri sans("L")$, $Gamma tack.r sans("let") z = (sans("case") e {iota_l x : a, iota_r y : b}); r approx sans("case") e {iota_l x : sans("let") z = a; r, iota_r y : sans("let") z = b; r} gt.tri sans("L")$)),
    prooftree(rule(label: msc("let1-abort"), eff-typing($Gamma$, $epsilon$, $a$, $upright(bold(0))$), $Gamma, y : A tack.r r gt.tri sans("L")$, $Gamma tack.r sans("let") y = sans("abort") a; r approx sans("let") x = a; sans("let") y = sans("abort") x; r gt.tri sans("L")$)),
  )
], caption: [Rewriting rules for #lssa unary $sans("let")$-statements])
<fig:ssa-reg-unary-let>

#figure([
  #rule-set(
    prooftree(rule(label: msc("let2-pair"), eff-typing($Gamma$, $epsilon$, $a$, $A$), eff-typing($Gamma$, $epsilon$, $b$, $B$), $Gamma, x : A, y : B tack.r r gt.tri sans("L")$, $Gamma tack.r sans("let") (x, y) = (a, b); r approx sans("let") x = a; sans("let") y = b; r gt.tri sans("L")$)),
    prooftree(rule(label: msc("let2-bind"), eff-typing($Gamma$, $epsilon$, $e$, $A times B$), $Gamma, x : A, y : B tack.r r gt.tri sans("L")$, $Gamma tack.r sans("let") (x, y) = e; r approx sans("let") z = e; sans("let") (x, y) = z; r gt.tri sans("L")$)),
    prooftree(rule(label: msc("case-inl"), eff-typing($Gamma$, $epsilon$, $a$, $A$), $Gamma, x : A tack.r r gt.tri sans("L")$, $Gamma, y : B tack.r s gt.tri sans("L")$, $Gamma tack.r sans("case") iota_l a {iota_l x : r, iota_r y : s} approx sans("let") x = a; r gt.tri sans("L")$)),
    prooftree(rule(label: msc("case-inr"), eff-typing($Gamma$, $epsilon$, $b$, $B$), $Gamma, x : A tack.r r gt.tri sans("L")$, $Gamma, y : B tack.r s gt.tri sans("L")$, $Gamma tack.r sans("case") iota_r b {iota_l x : r, iota_r y : s} approx sans("let") y = b; s gt.tri sans("L")$)),
    prooftree(rule(label: msc("case-bind"), eff-typing($Gamma$, $epsilon$, $e$, $A + B$), $Gamma, x : A tack.r r gt.tri sans("L")$, $Gamma, y : B tack.r s gt.tri sans("L")$, $Gamma tack.r sans("case") e {iota_l x : r, iota_r y : s} approx sans("let") z = e; sans("case") z {iota_l x : r, iota_r y : s} gt.tri sans("L")$)),
  )
], caption: [Rewriting rules for #lssa binary $sans("let")$-statements and $sans("case")$-statements])
<fig:ssa-reg-let2-case-expr>

Dealing with $sans(w h e r e)$-blocks, on the other hand, is a little
bit more complicated, as shown by the number of rules in
Figure~@fig:ssa-where-rules One difficulty is that, unlike the other
region constructors, we will need an $eta$-rule as well as #emph[two]
$beta$-rules. The latter are simple enough to state:

- For $ell_k$ defined in a $sans(w h e r e)$-block, cfg-$beta_1$ says
  that we can replace a branch to $ell_k$ with argument $a$ with a
  $sans(l e t)$-statement binding $a$ to the corresponding body $t_k$'s
  argument $x_k$.

- For $kappa$ #emph[not] defined in a $sans(w h e r e)$-block,
  cfg-$beta_2$ says that a branch to $kappa$ within the
  $sans(w h e r e)$-block has the same semantics as if the
  $sans(w h e r e)$-block was not there; hence, it can be removed.

To state our $eta$-rule, however, we will need to introduce some more
machinery. Given a mapping from a set of labels $ell_i$ to associated
regions $t_i$, we may define the #emph[control-flow graph substitution]
$sans(c f g s) #h(0em) { \( ell_i \( x_i \) : { t_i } \, \)_i }$
pointwise as follows:
$ sans(c f g s) #h(0em) { \( ell_i \( x_i \) : { t_i } \, \)_i } #h(0em) kappa #h(0em) a := \( kw("br") med kappa #h(0em) a #h(0em) kw("where") med \( ell_i \( x_i \) : { t_i } \, \)_i \) $
In general, we may derive, for any label-context $sans(L)$ (assuming
$sans(c f g s) #h(0em) { dot.op }$ acts uniformly on the labels $kappa$
in $sans(L)$ as described above), the following rule:
#align(center, prooftree(rule(
  label: msc("cfgs"),
  $forall i in I. Gamma, x_i : A_i tack.r t_i gt.tri sans("L"), (ell_j(A_j),)_(j in I)$,
  $Gamma tack.r sans("cfgs") {(ell_i(x_i) : {t_i},)_(i in I)} : sans("L"), (ell_j(A_j),)_(j in I) arrow.r.squiggly sans("L")$,
)))
Our $eta$-rule, cfg-$eta$, says that any $sans(w h e r e)$-block of the
form
$r #h(0em) kw("where") med \( ell_i \( x_i \) : { t_i } \, \)_i$
has the same semantics as the label-substitution
$\[ sans(c f g s) #h(0em) { \( ell_i \( x_i \) : { t_i } \, \)_i } \] r$,
which in effect propagates the where-block to the branches of $r$, if
any. While we called this rule cfg-$eta$, it also functions similarly to
a binding rule in that it allows us to derive many of the expected
commutativity properties of $sans(w h e r e)$; for example, we have that
$ kw("let") med y = a ; #h(0em) r #h(0em) kw("where") med \( ell_i \( x_i \) : { kw("br") med ell_j #h(0em) a_j } \, \)_i & approx \[ sans(c f g s) #h(0em) { \( ell_i \( x_i \) : { kw("br") med ell_j #h(0em) a_j } \, \)_i } \] \( kw("let") med y = a ; #h(0em) r \)\
 & approx kw("let") med y = a ; #h(0em) \[ sans(c f g s) #h(0em) { \( ell_i \( x_i \) : { kw("br") med ell_j #h(0em) a_j } \, \)_i } \] r\
 & approx kw("let") med y = a ; #h(0em) r #h(0em) kw("where") med \( ell_i \( x_i \) : { kw("br") med ell_j #h(0em) a_j } \, \)_i $
One particularly important application of the $eta$-rule for
control-flow graphs is in validating the rewrite
#align(center, prooftree(rule(
  label: msc("case2cfg"),
  eff-typing($Gamma$, $epsilon$, $a$, $A + B$),
  region-typing($Gamma, x : A$, $s$, $sans("L")$),
  region-typing($Gamma, y : B$, $t$, $sans("L")$),
  $Gamma tack.r sans("case") a {iota_l x : s, iota_r y : t}
    approx (sans("case") a {iota_l x : sans("br") ell x, iota_r y : sans("br") ell' y})
    sans("where") ell(x) : {s}, ell'(y) : {t} gt.tri sans("L")$,
))) In addition, we also add as an axiom the ability to get rid of
a single, trivially nested $sans(w h e r e)$-block; this is given as the
rule codiag.

To be able to soundly perform equational rewriting, we will need the
#emph[uniformity] property, which is described by the rule uni. In
essence, this lets us commute pure expressions with loop bodies,
enabling rewrites (in imperative style) like
$ sans(l o o p) #h(0em) { x = x + 1 ; sans(i f) #h(0em) p #h(0em) 3 x #h(0em) { sans(r e t) #h(0em) 3 x } } #h(2em) approx #h(2em) y = 3 x ; sans(l o o p) #h(0em) { y = y + 3 ; sans(i f) #h(0em) p #h(0em) y #h(0em) { sans(r e t) #h(0em) y } } $<eqn:simple-loop-comm>
Note that substitution alone would not allow us to derive
Equation~@eqn:simple-loop-comm above, since $x$ and $y$ change each
iteration, and hence, in SSA, would need to become parameters as
follows:
$ kw("br") med ell #h(0em) x #h(0em) kw("where") med ell \( y \) : { kw("let") med x' = y + 1 ; sans(i f) #h(0em) p #h(0em) 3 x' #h(0em) { sans(r e t) #h(0em) 3 x' } #h(0em) sans(e l s e) #h(0em) { kw("br") med ell #h(0em) x' } }\
approx kw("let") med y = 3 x ; kw("br") med kappa #h(0em) y #h(0em) kw("where") med kappa \( y \) : { kw("let") med y' = y + 3 ; sans(i f) #h(0em) p #h(0em) y' #h(0em) { sans(r e t) #h(0em) y' } #h(0em) sans(e l s e) #h(0em) { kw("br") med kappa #h(0em) y' } } $<eqn:loop-comm-ssa>
The actual rule is quite complicated, so let's break it down point by
point. Assume we are given:

- A region $Gamma \, y : B tack.r s gt.tri sans(L) \, kappa \( B \)$
  taking "input" $y$ of type $B$ and, as "output," jumping to a label
  $kappa$ with an argument of type $B$. We'll interpret branches to any
  other label (i.e. any label in $sans(L)$) as a (divergent) "side
  effect."

- A region $Gamma \, x : A tack.r t gt.tri sans(L) \, ell \( A \)$
  taking "input" $x$ of type $A$ and, as "output," jumping to a label
  $ell$ with an argument of type $A$.

- A #emph[pure] expression $Gamma \, x : A tack.r_tack.t e : B$
  parameterised by a value $x$ of type $A$

Suppose further that the following condition holds:
$ Gamma \, x : A tack.r \[ e \/ y \] s approx t #h(0em) kw("where") med ell \( x \) : { kw("br") med kappa #h(0em) e } gt.tri sans(L) \, kappa \( B \) $
That is, the following two programs are equivalent:

+ Given input $x$, evaluate $e$ and, taking it's output to be input $y$,
  evaluate $s$, (implicitly) yielding as output a new value of $y$. In
  imperative pseudocode, $ y = e ; y = s $

+ Given input $x$, evaluate $t$ and, taking it's output to be the
  #emph[new] value of $x$, evaluate $e$, (implicitly) yielding as output
  a new value $y$. In imperative pseudocode, $ x = t ; y = e $

#emph[Then], for any well-typed entry block
$Gamma tack.r r gt.tri sans(L) \, ell \( A \)$ (which can produce an
appropriate input $x : A$ at label $ell$), we have that
$ Gamma tack.r \( r #h(0em) kw("where") med ell \( x \) : { kw("br") med kappa #h(0em) e } \) #h(0em) kw("where") med kappa \( y \) : { s } approx r #h(0em) kw("where") med t gt.tri sans(L) $
i.e., in imperative pseudocode,
$ x = r ; y = e ; sans(l o o p) #h(0em) { y = s } & approx x = r ; sans(l o o p) #h(0em) { x = t } $
since
$ y = e ; y = s ; y = s ; dots.h #h(0em) #h(0em) approx #h(0em) #h(0em) x = t ; y = e ; y = s ; dots.h #h(0em) #h(0em) approx #h(0em) #h(0em) x = t ; x = t ; y = e ; dots.h #h(0em) #h(0em) approx #h(0em) #h(0em) dots.h.c $
where $s$ and $t$ may branch out of the loop. Note that, due to
let$""_1$-$beta$, cfg-$eta$, and cfg-$beta_1$, this is equivalent to the
rule
#align(center)[
  #prooftree(rule(
    label: msc("uni'"),
    $Gamma, x : A tack.r [e/y]s approx [ell(x) mapsto sans("br") kappa e]t gt.tri sans("L"), kappa(B)$,
    $Gamma tack.r (([ell(x) mapsto sans("br") kappa e]r) sans("where") kappa(y) : {s}) approx (r sans("where") ell(x) : {t}) gt.tri sans("L")$,
  ))
  #align(center, $upright("where") quad
    Gamma tack.r r gt.tri sans("L"), ell(A) quad
    #eff-typing($Gamma, x : A$, $bot$, $e$, $B$) quad
    Gamma, y : B tack.r s gt.tri sans("L"), kappa(B) quad
    Gamma, x : A tack.r t gt.tri sans("L"), ell(A)$)
]
<eqn:uni-variant>
Going back to our concrete example from
Equation~@eqn:loop-comm-ssa, if we first substitute the let-binding
$y = 3 x$ on the RHS, we get
$ kw("br") med ell #h(0em) x #h(0em) kw("where") med ell \( y \) : { kw("let") med x' = y + 1 ; sans(i f) #h(0em) p #h(0em) 3 x' #h(0em) { sans(r e t) #h(0em) 3 x' } #h(0em) sans(e l s e) #h(0em) { kw("br") med ell #h(0em) x' } }\
approx kw("br") med kappa #h(0em) 3 x #h(0em) kw("where") med kappa \( y \) : { kw("let") med y' = y + 3 ; sans(i f) #h(0em) p #h(0em) y' #h(0em) { sans(r e t) #h(0em) y' } #h(0em) sans(e l s e) #h(0em) { kw("br") med kappa #h(0em) y' } } $<eqn:loop-comm-red>
Now, instantiate $sans("uni")'$ (Equation~#todo[Resolve source reference `eqn:uni-variant` during integration.]) by taking:

- $s = kw("let") med y' = y + 3 ; #h(0em) sans(i f) #h(0em) p #h(0em) y' #h(0em) { sans(r e t) #h(0em) y' } #h(0em) sans(e l s e) #h(0em) { kw("br") med kappa #h(0em) y' }$
  to be the loop body on the RHS

- $e = 3 x$

- $r = kw("br") med ell #h(0em) x$

- $t = kw("let") med x' = y + 1 ; sans(i f) #h(0em) p #h(0em) 3 x' #h(0em) { sans(r e t) #h(0em) 3 x' } #h(0em) sans(e l s e) #h(0em) { kw("br") med ell #h(0em) x' }$
  to be the loop body on the LHS

It's easy to see that
$\( \( \[ ell \( x \) mapsto kw("br") med kappa #h(0em) e \] r \) #h(0em) kw("where") med kappa \( y \) : { s } \)$
and $\( r #h(0em) kw("where") med t \)$ are syntactically equal
to the #emph[RHS] and #emph[LHS] of our desired result
(Equation~@eqn:loop-comm-red). So, it suffices to verify that
$ Gamma \, x : A tack.r & \[ e \/ y \] s approx kw("let") med y' = 3 x + 3 ; #h(0em) sans(i f) #h(0em) p #h(0em) y' #h(0em) { sans(r e t) #h(0em) y' } #h(0em) sans(e l s e) #h(0em) { kw("br") med kappa #h(0em) y' }\
 & approx kw("let") med y' = 3 \( x + 1 \) ; #h(0em) sans(i f) #h(0em) p #h(0em) y' #h(0em) { sans(r e t) #h(0em) y' } #h(0em) sans(e l s e) #h(0em) { kw("br") med kappa #h(0em) y' }\
 & approx kw("let") med x' = x + 1 ; #h(0em) kw("let") med y' = 3 x' ; #h(0em) sans(i f) #h(0em) p #h(0em) y' #h(0em) { sans(r e t) #h(0em) y' } #h(0em) sans(e l s e) #h(0em) { kw("br") med kappa #h(0em) y' }\
 & approx kw("let") med x' = x + 1 ; #h(0em) sans(i f) #h(0em) p #h(0em) 3 x' #h(0em) { sans(r e t) #h(0em) 3 x' } #h(0em) sans(e l s e) #h(0em) { kw("br") med kappa #h(0em) 3 x' }\
 & approx \[ ell \( x \) mapsto kw("br") med kappa #h(0em) e \] t $
as desired. The reason why we require $e$ to be #emph[pure] in the
uniformity rule is that impure expressions do not necessarily commute
with infinite loops, even if they commute with any finite number of
iterations of the loop. For example, if $sans(h i)$ is some effectful
operation (say, printing "hello"), it is quite obvious that,
#align(center, $
  sans("hi") ; x = x + 1 ; sans("if") x = y {sans("ret") y}
    & approx x = x + 1 ; sans("if") x = y {sans("hi") ; sans("ret") y} ; sans("hi") \
  & upright("whereas") \
  sans("hi") ; sans("loop") {x = x + 1 ; sans("if") x = y {sans("ret") y}}
    & not approx sans("loop") {x = x + 1 ; sans("if") x = y {sans("hi") ; sans("ret") y}} ; sans("hi")
$) since, in particular, we may have $y lt.eq x$, in
which case the loop will never exit and hence $sans(h i)$ will never be
executed.

#figure([
  #rule-set(
    prooftree(rule(label: msc("cfg-beta1"), eff-typing($Gamma$, $bot$, $a$, $A_k$), $forall i in I. Gamma, x_i : A_i tack.r t_i gt.tri sans("L"), (ell_j(A_j),)_(j in I)$, $Gamma tack.r sans("br") ell_k a sans("where") (ell_i(x_i) : {t_i},)_(i in I) approx (sans("let") x_k = a; t_k) sans("where") (ell_i(x_i) : {t_i},)_(i in I) gt.tri sans("L")$)),
    prooftree(rule(label: msc("cfg-beta2"), eff-typing($Gamma$, $bot$, $b$, $B$), $forall i in I. Gamma, x_i : A_i tack.r t_i gt.tri sans("L"), (ell_j(A_j),)_(j in I)$, $sans("L") kappa = B$, $kappa in.not {ell_i | i in I}$, $Gamma tack.r sans("br") kappa b sans("where") (ell_i(x_i) : {t_i},)_(i in I) approx sans("br") kappa b gt.tri sans("L")$)),
    prooftree(rule(label: msc("cfg-eta"), $Gamma tack.r r gt.tri sans("L"), (ell_i(A_i),)_(i in I)$, $forall i in I. Gamma, x_i : A_i tack.r t_i gt.tri sans("L"), (ell_j(A_j),)_(j in I)$, $Gamma tack.r r sans("where") (ell_i(x_i) : {t_i},)_(i in I) approx [sans("cfgs") {(ell_i(x_i) : {t_i},)_(i in I)}] r gt.tri sans("L")$)),
    prooftree(rule(label: msc("codiag"), $Gamma tack.r r gt.tri sans("L"), ell(A)$, $Gamma, y : A tack.r s gt.tri sans("L"), ell(A), kappa(A)$, $Gamma tack.r r sans("where") ell(x) : {sans("br") kappa x sans("where") kappa(y) : {s}} approx r sans("where") ell(y) : {[ell/kappa]s} gt.tri sans("L")$)),
    prooftree(rule(label: msc("uni"), $Gamma tack.r r gt.tri sans("L"), ell(A)$, $Gamma, x : A tack.r sans("let") y = e; s approx t sans("where") ell(x) : {sans("br") kappa e} gt.tri sans("L"), kappa(B)$, $Gamma tack.r (r sans("where") ell(x) : {sans("br") kappa e}) sans("where") kappa(y) : {s} approx r sans("where") t gt.tri sans("L")$)),
    $upright("where") quad #eff-typing($Gamma, x : A$, $bot$, $e$, $B$), quad Gamma, y : B tack.r s gt.tri sans("L"), kappa(B), quad upright("and") quad Gamma, x : A tack.r t gt.tri sans("L"), ell(A)$,
    text(size: 7.5pt)[#prooftree(rule(label: msc("dinat"), $Gamma tack.r r gt.tri sans("L"), (ell_i(A_i),)_(i in I)$, $Gamma tack.r sigma : (ell_i(A_i),)_(i in I) arrow.r.squiggly (kappa_j(B_j),)_(j in J)$, $forall j in J. Gamma, x_j : B_j tack.r t_j gt.tri sans("L"), (ell_i(A_i),)_(i in I)$, $Gamma tack.r ([sigma^harpoon.tl]r) sans("where") (kappa_j(x_j) : {[sigma^harpoon.tl]t_j},)_(j in J) approx r sans("where") (ell_i(x_i) : {[(kappa_j(x_j) mapsto t_j,)_(j in J)^harpoon.tl](sigma ell_i x_i)},)_(i in I)$))],
  )
], caption: [Rewriting rules for #lssa $sans("where")$-blocks])
<fig:ssa-where-rules>

#figure([#block[
  #figure([$  & kw("let") med n = 10 ;\
     & kw("br") med sans(l o o p) \( 1 \, 1 \)\
     & kw("where") med sans(l o o p) \( i_0 \, a_0 \) : {\
     & quad sans(i f) #h(0em) i_0 < n #h(0em) {\
     & #h(2em) kw("br") med sans(l o o p) \( i_0 + 1 \, a_0 \* \( i_0 + 1 \) \)\
     & quad } #h(0em) sans(e l s e) #h(0em) {\
     & #h(2em) sans(r e t) #h(0em) a_0\
     & quad }\
     & } $

    ],
    caption: [
      Program from @fig:dominance-to-lexical after substituting
      $sans(l e t)$s.
    ]
  )
  <fig:fact-subst-2>

  #figure([$  & kw("let") med n = 10 ;\
     & kw("br") med sans(l o o p) #h(0em) \( 0 \, 1 \)\
     & kw("where") med sans(l o o p) \( x \, y \) : {\
     & quad kw("let") med \( i_0 \, a_0 \) = \( x + 1 \, y \* \( x + 1 \) \) ;\
     & quad sans(i f) #h(0em) i_0 < n #h(0em) {\
     & #h(2em) kw("br") med sans(l o o p) \( i_0 \, a_0 \)\
     & quad } #h(0em) sans(e l s e) #h(0em) {\
     & #h(2em) sans(r e t) #h(0em) a_0\
     & quad }\
     & } $

    ],
    caption: [
      Equivalent to @fig:fact-zero by #emph[dinaturality]
    ]
  )
  <fig:fact-dinat>

  ]
  #figure([$  & kw("let") med n = 10 ;\
     & kw("br") med sans(l o o p) \(\
     & quad kw("let") med \( x \, y \) = \( 0 \, 1 \) ;\
     & quad \( x + 1 \, y \* \( x + 1 \) \)\
     & \)\
     & kw("where") med sans(l o o p) \( i_0 \, a_0 \) : {\
     & quad sans(i f) #h(0em) i_0 < n #h(0em) {\
     & #h(2em) kw("br") med sans(l o o p) \(\
     & #h(2em) quad kw("let") med \( x \, y \) = \( i_0 \, a_0 \) ;\
     & #h(2em) quad \( x + 1 \, y \* \( x + 1 \) \)\
     & #h(2em) \)\
     & quad } #h(0em) sans(e l s e) #h(0em) {\
     & #h(2em) sans(r e t) #h(0em) a_0\
     & quad }\
     & } $

    ],
    caption: [
      Equivalent to @fig:fact-subst-2 by congruence
    ]
  )
  <fig:fact-zero>

  ],
  caption: [
    Decomposing multi-block rewrites (from @fig:fact-zero to
    @fig:fact-subst-2, and therefore to the more optimal program
    @fig:fact-dinat) into simple algebraic steps. By verifying each
    step, we can verify complex optimizations through decomposition.
  ]
)
<fig:fact-dinat-rewrites>

The derivable rule uni' (Equation~#todo[Resolve source reference `eqn:uni-variant` during integration.]) illuminates a very
important potential use for uniformity; namely, formalizing rewrites
like those in Figure~@fig:fact-dinat-rewrites In particular, consider a
program of the form
$ Gamma tack.r \( \[ ell \( x \) mapsto kw("br") med kappa #h(0em) e \] r \) #h(0em) kw("where") med kappa \( y \) : { \[ ell \( x \) mapsto kw("br") med kappa #h(0em) e \] s } gt.tri sans(L) $
where

- $Gamma tack.r r gt.tri sans(L) \, ell \( A \)$

- $Gamma \, y : B tack.r s gt.tri sans(L) \, ell \( A \)$

- $Gamma \, x : A tack.r_tack.t e : B$ is pure

Then we have that
$ \[ e \/ y \] \[ ell \( x \) mapsto kw("br") med kappa #h(0em) \( e \) \] s\
approx \[ ell \( x \) mapsto kw("br") med kappa #h(0em) \[ e \/ y \] \( e \) \] \[ e \/ y \] s\
approx \[ ell \( x \) mapsto kw("br") med kappa #h(0em) \( e \) \] \[ e \/ y \] s $
and therefore that
$ Gamma tack.r \( \[ ell \( x \) mapsto kw("br") med kappa #h(0em) e \] r \) #h(0em) kw("where") med kappa \( z \) : { \[ ell \( x \) mapsto kw("br") med kappa #h(0em) e \] s }\
approx r #h(0em) kw("where") med ell \( x \) : { \[ e \/ y \] s }\
approx r #h(0em) kw("where") med ell \( x \) : { kw("let") med y = e ; s } $
In particular, for example, we can then easily derive the rewrite from
Figure~@fig:fact-dinat to Figure~@fig:fact-zero by noting the
#emph[equalities] (an equivalence would be enough, of course)
$  & sans(i f) #h(0em) i_0 < n #h(0em) {\
 & quad kw("br") med sans(l o o p) \( kw("let") med \( x \, y \) = \( i_0 \, a_0 \) ; #h(0em) \( x + 1 \, y \* x + 1 \) \)\
 & } #h(0em) sans(e l s e) #h(0em) { sans(r e t) \( a_0 \) }\
 & =\
 & \[ sans(l o o p) \( i_0 \, a_0 \) mapsto kw("let") med \( x \, y \) = \( i_0 \, a_0 \) ; #h(0em) \( x + 1 \, y \* x + 1 \) \] \( sans(i f) #h(0em) i_0 < n #h(0em) {\
 & #h(2em) kw("br") med sans(l o o p) \( i_0 \, a_0 \)\
 & quad } #h(0em) sans(e l s e) #h(0em) { sans(r e t) \( a_0 \) } \) $
and
$ kw("let") med n = 10 ; kw("br") med sans(l o o p) \( kw("let") med \( x \, y \) = \( 0 \, 1 \) ; \( x + 1 \, y \* \( x + 1 \) \) \)\
= \[ sans(l o o p) \( i_0 \, a_0 \) mapsto kw("let") med \( x \, y \) = \( i_0 \, a_0 \) ; #h(0em) \( x + 1 \, y \* x + 1 \) \] \( kw("let") med n = 10 ; kw("br") med sans(l o o p) \( 0 \, 1 \) \) $
Rewrites like this are an instance of the principle we call
#emph[dinaturality], which, for structured control-flow, can be best
expressed as an equivalence between the control-flow graphs in
Figure~@fig:dinat-struct-cfg Unlike in the case of uniformity, however,
this is true even when the program fragment $P$ is #emph[impure],
since, unlike in the case of general uniformity, we do not commute $P$
over an infinite number of iterations. Our final rewriting rule, dinat,
generalises the above rewrite from sequential composition on a
structured control-flow graph to label substitution on an arbitrary
control-flow graph.

#figure([],
  caption: [
    Dinaturality on a structured loop
  ]
)
<fig:dinat-struct-cfg>

We require a separate rule for impure dinaturality as it allows us to
relate unary and $n$-ary $sans(w h e r e)$-blocks and, in particular,
use this relationship to interconvert between data-flow and
control-flow. This means we now have enough equations to derive the
flattening of nested $sans(w h e r e)$-blocks:
#align(center, text(size: 7.5pt)[#prooftree(rule(
  label: msc("cfg-fuse"),
  $Gamma tack.r r gt.tri sans("L"), (ell_i(A_i),)_(i in I), (kappa_j(B_j),)_(j in I)$,
  $forall i in I. Gamma, x_i : A_i tack.r t_i gt.tri sans("L"), (ell_j(A_j),)_(j in I)$,
  $forall i in I. Gamma, y_i : B_i tack.r s_i gt.tri sans("L"), (ell_j(A_j),)_(j in J), (kappa_k(B_k),)_(k in K)$,
  $Gamma tack.r (r sans("where") (kappa_k(y_k) : {s_k}),)_(k in K)
    sans("where") (ell_i(x_i) : {t_i}),)_(i in I)
    approx r sans("where") (kappa_k(y_k) : {s_k},)_(k in K),
      (ell_i(x_i) : {t_i}),)_(i in I) gt.tri sans("L")$,
))]) <eqn:where-fusion-1> Rather than directly giving
derivation trees for such auxilliary rules, it is more convenient to
give a denotational proof. However, the completeness of our equational
theory (proved in Section~@ssec:completeness) means that the semantic
equality implies the existence of the requisite derivation tree. A proof
can be found in Lemma~#todo[Resolve source reference `lem:where-fusion` during integration.] in the appendix. This is one of
the benefits of having a completeness result: it lets us switch freely
between equational and denotational modes of reasoning.

There are some other basic rules we may want to use which turn out to be
derivable from our existing set. For example, while re-ordering labels
in a $sans(w h e r e)$-block looks like a no-op in our named syntax, to
rigorously justify the following rule actually requires dinaturality
(with the permutation done via a label-substitution):
#align(center, prooftree(rule(
  label: msc("perm-cfg"),
  $Gamma tack.r r gt.tri sans("L"), (ell_i(A_i),)_(i in I)$,
  $forall i in I. Gamma, x_i : A_i tack.r t_i gt.tri sans("L"), (ell_j(A_j),)_(j in I)$,
  $sigma upright("permutation")$,
  $Gamma tack.r r sans("where") (ell_i(x_i) : {t_i},)_(i in I)
    approx r sans("where") (ell_(sigma_i)(x_(sigma_i)) : {t_(sigma_i)},)_(i in I) gt.tri sans("L")$,
)))
Note the implicit use of the fact that if some region $r$ typechecks in
some label-context $sans(L)$, then it typechecks in any permutation of
$sans(L)$, which is again proven by label-substitution.

== Metatheory
<metatheory>
We can now begin to investigate the metatheoretic properties of our
equational theory. As a first sanity check, we can verify that
weakening, label-weakening, and loosening of effects all respect our
equivalence relation, as stated in the following lemma:

#block[
Given $Gamma lt.eq Delta$, $sans(L) lt.eq sans(K)$, and
$epsilon.alt lt.eq epsilon.alt'$, we have that

+ $Delta tack.r_epsilon.alt a approx a' : A arrow.r.double.long Gamma tack.r_(epsilon.alt') a approx a' : A$

+ $Delta tack.r r approx r' gt.tri sans(L) arrow.r.double.long Gamma tack.r r approx r' gt.tri sans(K)$

]
#block[
#emph[Proof.] These are formalized as:

+ `Term.InS.wk_congr` and `Term.InS.wk_eff_congr` in
  `Rewrite/Term/Setoid.lean`

+ `Region.InS.vwk_congr` and `Region.InS.lwk_congr` in
  `Rewrite/Region/Setoid.lean`

~◻

]
It is straightforward to verify that these are indeed equivalence
relations. In fact, it turns out that substitution and
label-substitution both respect these equivalences, in the following
precise sense:

#block[
Given $gamma approx gamma' : Gamma mapsto Delta$, we have that

+ $Delta tack.r_epsilon.alt a approx a' : A arrow.r.double.long Gamma tack.r_epsilon.alt \[ gamma \] a approx \[ gamma' \] a' : A$

+ $Delta tack.r r approx r' gt.tri sans(L) arrow.r.double.long Gamma tack.r \[ gamma \] r approx \[ gamma' \] r' gt.tri sans(L)$

+ $rho approx rho' : Delta mapsto Xi arrow.r.double.long \[ gamma \] rho approx \[ gamma' \] rho' : Gamma mapsto Xi$

+ $sigma approx sigma' tack.r Delta : sans(L) arrow.r.squiggly sans(K) arrow.r.double.long \[ gamma \] sigma approx \[ gamma' \] sigma' tack.r Gamma : sans(L) arrow.r.squiggly sans(K)$

]
#block[
#emph[Proof.] These are formalized as:

+ `Term.InS.subst_congr` in `Rewrite/Term/Setoid.lean`

+ `Region.InS.vsubst_congr` in `Rewrite/Region/Setoid.lean`

+ `Term.Subst.InS.comp_congr` in `Rewrite/Term/Setoid.lean`

+ `Region.Subst.InS.vsubst_congr` in `Rewrite/Region/LSubst.lean`

~◻

]
In particular, note that this lemma uses an equivalence relation on
substitutions and label-substitutions: this is just the obvious
pointwise extension of the equivalence relation on terms and regions
respectively. We give the rules for this relation in
Figure~@fig:ssa-subst-equiv in the interests of explicitness.

#block[
Given
$sigma approx sigma' tack.r Gamma : sans(L) arrow.r.squiggly sans(K)$,
we have that

+ $Gamma tack.r r approx r' gt.tri sans(L) arrow.r.double.long Gamma tack.r \[ sigma \] r approx \[ sigma' \] r' gt.tri sans(K)$

+ $kappa approx kappa' tack.r Gamma : sans(L) arrow.r.squiggly sans(J) arrow.r.double.long \[ sigma \] kappa approx \[ sigma' \] kappa' tack.r Gamma : sans(K) arrow.r.squiggly sans(J)$

]
#block[
#emph[Proof.] These are formalized as:

+ `Region.InS.lsubst_congr` in `Rewrite/Region/LSubst.lean`

+ `Region.LSubst.InS.comp_congr` in `Rewrite/Region/LSubst.lean`

~◻

]
This means, in particular, that, substitution and label-substitution are
well-defined operators on equivalence classes of terms, which will come
in handy later as we set out to prove completeness in
Section~@ssec:completeness

#figure([
  #rule-set(
    prooftree(rule(label: msc("sb-nil"), $dot.op approx dot.op : Gamma mapsto dot.op$)),
    prooftree(rule(label: msc("sb-cons"), eff-typing($Gamma$, $bot$, $a approx a'$, $A$), $gamma approx gamma' : Gamma mapsto Delta$, $gamma, x mapsto a approx gamma', x mapsto a' : Gamma mapsto Delta, x : A$)),
    prooftree(rule(label: msc("sb-skip-l"), $gamma approx gamma' : Gamma mapsto Delta$, $gamma, x mapsto a approx gamma' : Gamma mapsto Delta$)),
    prooftree(rule(label: msc("sb-skip-r"), $gamma approx gamma' : Gamma mapsto Delta$, $gamma approx gamma', x mapsto a' : Gamma mapsto Delta$)),
    prooftree(rule(label: msc("ls-nil"), $dot.op approx dot.op tack.r Gamma : dot.op arrow.r.squiggly sans("K")$)),
    prooftree(rule(label: msc("ls-cons"), $Gamma, x : A tack.r r approx r' gt.tri sans("K")$, $sigma approx sigma' tack.r Gamma : sans("L") arrow.r.squiggly sans("K")$, $sigma, ell(x) mapsto r approx sigma', ell(x) mapsto r' tack.r Gamma : sans("L"), ell(A) arrow.r.squiggly sans("K")$)),
    prooftree(rule(label: msc("ls-skip-l"), $sigma approx sigma' tack.r Gamma : sans("L") arrow.r.squiggly sans("K")$, $sigma, ell(x) mapsto r approx sigma' tack.r Gamma : sans("L") arrow.r.squiggly sans("K")$)),
    prooftree(rule(label: msc("ls-skip-r"), $sigma approx sigma' tack.r Gamma : sans("L") arrow.r.squiggly sans("K")$, $sigma approx sigma', ell(x) mapsto r' tack.r Gamma : sans("L") arrow.r.squiggly sans("K")$)),
    prooftree(rule(label: msc("sb-id"), $gamma approx gamma' : Gamma, x : A mapsto Delta, x : A$, $gamma approx gamma' : Gamma mapsto Delta$)),
    prooftree(rule(label: msc("ls-id"), $sigma approx sigma' tack.r Gamma : sans("L"), ell(A) arrow.r.squiggly sans("K"), ell(A)$, $sigma approx sigma' tack.r Gamma : sans("L") arrow.r.squiggly sans("K")$)),
  )
], caption: [Rules for the equivalence relation on #lssa substitutions and label-substitutions])
<fig:ssa-subst-equiv>

== Standard SSA
<ssec:ssa-normal>
The relaxation of SSA to #lssa allows us to state our
equational theory and handle substitution more conveniently. However,
this approach may lead readers to question whether we have truly
provided a type-theoretic presentation of SSA as it is used in practice.
The argument given in the introduction for why this is the case can be
re-stated as the following series of explicit claims:

+ Every #lssa region can be converted to an equivalent
  lexical SSA region <claim:ssa-conv>

+ <claim:ssa-erase> Every lexical SSA region can be erased to a
  well-formed SSA program by removing "$sans(w h e r e)$"

+ Every well-formed SSA program can be typed as a lexical SSA region
  purely by adding "$sans(w h e r e)$" <claim:ssa-wf>. Moreover, a way
  to do this can be found in nearly linear time.

+ Two lexical SSA regions which erase to the same SSA program are
  equivalent <claim:ssa-inj>

Claim~#todo[Resolve source reference `claim:ssa-inj` during integration.] implies that the mappings given in
Claim~#todo[Resolve source reference `claim:ssa-erase` during integration.] and Claim~#todo[Resolve source reference `claim:ssa-wf` during integration.] establish an equivalence
(up to our equational theory) between lexical SSA and traditional SSA.
This means that the choice of where-bracketing that converts an SSA
program into a lexical SSA program is semantically irrelevant. In other
words, where-bracketing only makes dominance syntactically apparent,
letting us give syntax-directed rules for typing SSA programs.

We establish this claim in two phases. First, we will show that
#lssa can be transformed (in linear space) into an
equivalent lexical SSA program. Next, we will show that ordinary and
lexical SSA can be transformed into one another by adding and removing
where-blocks.

Converting #lssa directly to lexical SSA can be
unwieldy. Therefore, we break the transformation down into two lowering
passes:

+ We first convert #lssa into to a subset corresponding
  to A-normal form (ANF) extended with mutually recursive
  $sans(w h e r e)$-bindings

+ We then convert the resulting ANF regions into lexical SSA

=== From #lssa to A-Normal Form
<from-lambda_ensuremathmathsfssa-to-a-normal-form>
Our first step is to extend the work of
#todo[Restore prose citation `chakravarty-functional-ssa-2003` during integration.];, by providing
an algorithm for converting between #lssa and ANF in an
equivalence-preserving way. We define the ANF regions, whose grammar is
given in Figure~@fig:anf-grammar, to be #lssa regions
with expressions restricted to operations $o$; equivalently, we can view
ANF regions as lexical SSA regions with the syntactic category of
regions $r$ and terminators $tau$ fused. We may now introduce the
following predicates on syntax:

- $sans(I s A N F) \( r \)$ means that the region $r$ is in ANF

- $sans(I s S S A) \( r \)$ means that the region $r$ is a lexical SSA
  region. We note that
  $sans(I s S S A) \( r \) arrow.r.double.long sans(I s A N F) \( r \)$.

- $sans(I s V a l) \( a \)$ means that the expression $a$ can be parsed
  as a value $v$

- $sans(I s O p) \( a \)$ means that the expression $a$ can be parsed as
  an instruction $o$. We note that
  $sans(I s V a l) \( a \) arrow.r.double.long sans(I s O p) \( a \)$.

We can define a syntactic function to convert an #lssa
region to ANF inductively as follows:
$ sans(A N F) \( kw("br") med ell #h(0em) a \) & = sans(A N F)_(sans(l e t)) \( x \, a \, kw("br") med ell #h(0em) x \)\
sans(A N F) \( kw("let") med x = a ; #h(0em) r \) & = sans(A N F)_(sans(l e t)) \( x \, a \, sans(A N F) \( r \) \)\
sans(A N F) \( kw("let") med \( x \, y \) = a ; #h(0em) r \) & = sans(A N F)_(sans(l e t)) \( z \, a \, kw("let") med \( x \, y \) = z ; sans(A N F) \( r \) \)\
sans(A N F) \( kw("case") med a #h(0em) { iota_l #h(0em) x : r \, iota_r #h(0em) y : s } \) & = sans(A N F)_(sans(l e t)) \( z \, a \, kw("case") med z #h(0em) { iota_l #h(0em) x : sans(A N F) \( r \) \, iota_r #h(0em) y : sans(A N F) \( s \) } \)\
sans(A N F) \( r #h(0em) kw("where") med \( ell_i \( x_i \) : { t_i } \, \)_i \) & = sans(A N F) \( r \) #h(0em) kw("where") med \( ell_i \( x_i \) : { sans(A N F) \( t_i \) } \, \)_i $
where we define $sans(A N F)_(sans(l e t)) \( x \, a \, r \)$ by
induction on expressions $a$ as follows
$ sans(A N F)_(sans(l e t)) \( x \, a \, r \) & = \( kw("let") med x = a ; r \) #h(8em) upright("if") #h(0em) sans(I s O p) \( a \)\
sans(A N F)_(sans(l e t)) \( x \, f #h(0em) e \, r \) & = sans(A N F)_(sans(l e t)) \( y \, e \, kw("let") med x = f #h(0em) y ; r \)\
sans(A N F)_(sans(l e t)) \( x \, \( kw("let") med y = e ; #h(0em) a \) \, r \) & = sans(A N F)_(sans(l e t)) \( y \, e \, sans(A N F)_(sans(l e t)) \( x \, a \, r \) \)\
sans(A N F)_(sans(l e t)) \( x \, \( e_1 \, e_2 \) \, r \) & = sans(A N F)_(sans(l e t)) \( y_1 \, e_1 \, sans(A N F)_(sans(l e t)) \( y_2 \, e_2 \, sans(A N F)_(sans(l e t)) \( x \, \( y_1 \, y_2 \) \, r \) \) \)\
sans(A N F)_(sans(l e t)) \( x \, \( kw("let") med \( y \, z \) = e ; #h(0em) a \) \, r \) & = sans(A N F)_(sans(l e t)) \( w \, e \, \( kw("let") med \( y \, z \) = w ; sans(A N F)_(sans(l e t)) \( x \, a \, r \) \) \)\
sans(A N F)_(sans(l e t)) \( x \, iota_l #h(0em) e \, r \) & = sans(A N F)_(sans(l e t)) \( y \, e \, \( kw("let") med x = iota_l #h(0em) y ; r \) \)\
sans(A N F)_(sans(l e t)) \( x \, iota_r #h(0em) e \, r \) & = sans(A N F)_(sans(l e t)) \( y \, e \, \( kw("let") med x = iota_r #h(0em) y ; r \) \)\
sans(A N F)_(sans(l e t)) \( x \, kw("case") med e #h(0em) { iota_l #h(0em) y : a \, iota_r #h(0em) z : b } \, r \) & = sans(A N F)_(sans(l e t)) \( w \, e \, kw("case") med w\
 & #h(2em) #h(0em) { iota_l #h(0em) y : sans(A N F)_(sans(l e t)) \( x \, a \, kw("br") med ell #h(0em) x \) \, iota_r #h(0em) z : sans(A N F)_(sans(l e t)) \( x \, b \, kw("br") med ell #h(0em) x \) }\
 & #h(2em) #h(0em) kw("where") med ell \( x \) : { sans(A N F) \( r \) } \)\
sans(A N F)_(sans(l e t)) \( x \, kw("abort") med e \, r \) & = sans(A N F)_(sans(l e t)) \( y \, e \, \( kw("let") med x = kw("abort") med y ; r \) \) $
We note that, to get to ANF, we don't actually need the new label, and
can instead replace each branch with
$sans(A N F)_(sans(l e t)) \( x \, a \, r \)$; introducing the label is
only necessary to guarantee that the transformation to ANF is
#emph[linear-space]. The specification of the functions we just defined
is given by the following lemma:

#block[
Given an arbitrary region $r$, we have that

- $sans(I s A N F) \( sans(A N F) \( r \) \)$

- If $Gamma tack.r r gt.tri sans(L)$, then
  $Gamma tack.r r approx sans(A N F) \( r \) gt.tri sans(L)$

Similarly, given an arbitrary variable $x$, expression $a$ and region
$r$ If we are also given an arbitrary expression $a$, then

- $sans(I s A N F) \( r \) arrow.r.double.long sans(I s A N F) \( sans(A N F)_(sans(l e t)) \( x \, a \, r \) \)$

- If $Gamma tack.r_epsilon.alt a : A$ and
  $Gamma \, x : A tack.r r gt.tri sans(L)$, then
  $Gamma tack.r kw("let") med x = a ; r approx sans(A N F)_(sans(l e t)) \( x \, a \, r \) gt.tri sans(L)$

]
#block[
#emph[Proof.] See Appendix~@proof:anf-conversion~◻

]
#figure([#block[
  #old-syntax([#block[
  \<$v$\> ::= $x$ | $\( v \, v' \)$ | $\( \)$

  \<$o$\> ::= $v$ | $f #h(0em) v$ | $iota_l #h(0em) v$ |
  $iota_r #h(0em) v$ | $kw("abort") med v$

  \<$r \, s \, t$\> ::= $kw("let") med x = o ; t$ |
  $kw("let") med \( x \, y \) = o ; t$ |
  $t #h(0em) kw("where") med L$ |
  $kw("br") med ell #h(0em) o$ |
  $kw("case") med e #h(0em) { iota_l #h(0em) o : s \, iota_r #h(0em) y : t }$

  \<$L$\> ::= $dot.op$ | $L \, ell \( x \) : { t }$

  ]], family: "angle-grammar", note: [Migrate to the shared grammar figure API.])
  ]],
  caption: [
    Grammar for ANF regions
  ]
)
<fig:anf-grammar>

=== From ANF to (Lexical) SSA
<from-anf-to-lexical-ssa>
We would now like to define a syntactic linear-space transformation from
regions $r$ to equivalent lexical SSA regions $sans(S S A) \( r \)$. We
do this by giving a pair of mutually syntactic transformations
$sans(S S A) \( r \)$ converting a region to SSA, and
$sans(S S A)_(sans(a)) \( r \, L \)$ from ANF regions $r$
#emph[targeting] labels in $L$ to lexical SSA.
$ sans(S S A) \( r \) & = sans(S S A)_(sans(a)) \( sans(A N F) \( r \) \, dot.op \)\
sans(S S A)_(sans(a)) \( t \, \( ell_i \( x_i \) : { t_i } \, \)_i \) & = t #h(0em) kw("where") med \( ell_i \( x_i \) : { t_i } \, \)_i #h(2em) upright("where") #h(0em) t #h(0em) upright("is a terminator")\
sans(S S A)_(sans(a)) \( \( kw("let") med x = a ; r \) \, L \) & = \( kw("let") med x = a ; sans(S S A)_(sans(a)) \( r \, L \) \)\
sans(S S A)_(sans(a)) \( \( kw("let") med \( x \, y \) = a ; r \) \, L \) & = \( kw("let") med \( x \, y \) = a ; sans(S S A)_(sans(a)) \( r \, L \) \)\
sans(S S A)_(sans(a)) \( \( kw("case") med a #h(0em) { iota_l #h(0em) x : s \, iota_r #h(0em) y : t } \) \, L \) & = \( kw("case") med a #h(0em) { iota_l #h(0em) x : kw("br") med ell_l #h(0em) x \, iota_r #h(0em) y : kw("br") med ell_r #h(0em) y } \)\
 & #h(2em) #h(0em) kw("where") med L \, ell_l \( x \) : { sans(S S A) \( s \) } \, ell_r \( y \) : { sans(S S A) \( t \) }\
sans(S S A)_(sans(a)) \( \( r #h(0em) kw("where") med \( ell_i \( x_i \) : { t_i } \, \)_i \) \, L \) & = sans(S S A)_(sans(a)) \( r \, \( L \, \( ell_i \( x_i \) : { sans(S S A) \( t_i \) } \, \)_i \) \) $
The specification of these functions is as follows:

#block[
Given an arbitrary region $r$,

- $sans(I s S S A) \( sans(S S A) \( r \) \)$

- If $Gamma tack.r r gt.tri sans(L)$, then
  $Gamma tack.r r approx sans(S S A) \( r \) gt.tri sans(L)$

In particular,

- If $sans(I s A N F) \( r \)$ and
  $forall i \, sans(I s S S A) \( t_i \)$, then
  $sans(I s S S A) \( sans(S S A)_(sans(a)) \( r \, \( ell_i \( x_i \) : { t_i } \, \)_i \) \)$

- If $Gamma tack.r r gt.tri sans(L) \, \( ell_i \( A_i \) \, \)_i$ and
  $forall i \, Gamma tack.r t_i gt.tri sans(L) \, \( ell_i \( A_i \) \, \)_i$,
  then
  $Gamma tack.r \( r #h(0em) kw("where") med \( ell_i \( x_i \) : { t_i } \, \)_i \) approx sans(S S A)_(sans(a)) \( r \, \( ell_i \( x_i \) : { t_i } \, \)_i \) gt.tri sans(L)$

]
#block[
#emph[Proof.] See Appendix~#todo[Resolve source reference `proof:ssa-conversion` during integration.]~◻

]
=== From (Lexical) SSA to SSA
<from-lexical-ssa-to-ssa>
We now come to the final part of our argument: that lexical SSA is
equivalent to standard SSA, where we take the
basic-blocks-with-arguments dialect described in Figure~@fig:bba-grammar
as standard. We begin by recalling how, in Figure~@fig:ssa-data, we
illustrated how a lexical SSA region can alternatively be interpreted as
a tuple of:

- A basic block $beta$ (the #emph[entry block];), consisting of,

  - A sequence of instructions $kw("let") med x = o ;$

  - A terminator $tau$

- A map from labels $ell$ to subtrees $r$ (the region's
  #emph[children];), $L$

More formally, given a lexical SSA region $r$, we can define the
following functions to compute $r$'s entry block and children as follows
$ sans(e n t r y) \( kw("let") med x = a ; r \) & = \( kw("let") med x = a ; sans(e n t r y) \( r \) \)\
sans(e n t r y) \( kw("let") med \( x \, y \) = a ; r \) & = \( kw("let") med \( x \, y \) = a ; sans(e n t r y) \( r \) \)\
sans(e n t r y) \( tau #h(0em) kw("where") med \( ell_i \( x_i \) : { t_i } \, \)_i \) & = tau $
$ sans(c h i l d r e n) \( kw("let") med x = a ; r \) & = sans(c h i l d r e n) \( r \)\
sans(c h i l d r e n) \( kw("let") med \( x \, y \) = a ; r \) & = sans(c h i l d r e n) \( r \)\
sans(c h i l d r e n) \( tau #h(0em) kw("where") med \( ell_i \( x_i \) : { t_i } \, \)_i \) & = \[ ell_i \( x_i \) : { t_i } \, \]_i $
We can similarly define a function to construct a lexical SSA program
from a basic block $beta$ and a set of children as follows:
#align(center, $
  sans("bb")(sans("let") x = a; beta, L) &= sans("let") x = a; sans("bb")(beta, L) \
  sans("bb")(sans("let") (x, y) = a; beta, L) &= sans("let") (x, y) = a; sans("bb")(beta, L) \
  sans("bb")(tau, L) &= tau sans("where") L
$) It is easy to see that these functions are mutually
inverse: for any lexical SSA region $r$, we have
$ r = sans(b b) \( sans(e n t r y) \( r \) \, sans(c h i l d r e n) \( r \) \) $
Some other useful facts about $sans(b b) \( dot.op \, dot.op \)$
include:

- It is a congruence: if $r approx r'$ and each $t_i approx t_(i')$,
  $sans(b b) \( r \, \( ell_i \( x_i \) : { t_i } \, \)_i \) approx sans(b b) \( r' \, \( ell_i \( x_i \) : { t_(i') } \, \)_i \)$

- It is invariant up to permutations $sigma$:
  $sans(b b) \( r \, \( ell_i \( x_i \) : { t_i } \, \)_i \) approx sans(b b) \( r \, \( ell_(sigma_i) \( x_(sigma_i) \) : { t_(sigma_i) } \, \)_i \)$

- Similarly, #emph[if both sides of the equation are well-typed], i.e.,

  - All $t_i$ do not use $y$ or any of the variables defined in $s$

  - All branches to $ell_i$ come from $kappa$ or $ell_j$ (and not from
    either $r$ or $G$)

  $ sans(b b) \( r \, \( G \, kappa \( y \) : { s } \, \( ell_i \( x_i \) : { t_i } \, \) \) \) approx sans(b b) \( r \, \( G \, kappa \( y \) : { s #h(0em) kw("where") med \( ell_i \( x_i \) : { t_i } \, \) } \) \) $
  and hence
  $ sans(b b) \( r \, \( G \, kappa \( y \) : { s } \, \( ell_i \( x_i \) : { t_i } \, \) \) \) approx sans(b b) \( r \, \( G \, kappa \( y \) : { sans(b b) \( s \, \( ell_i \( x_i \) : { t_i } \, \) \) } \) \) $
  In particular, we may apply this rule twice to obtain
  $ sans(b b) \( r \, \( G \, kappa \( y \) : { sans(b b) \( s \, G' \) } \, \( ell_i \( x_i \) : { t_i } \, \) \) \) approx sans(b b) \( r \, \( G \, kappa \( y \) : { sans(b b) \( s \, G' \, \( ell_i \( x_i \) : { t_i } \, \) \) } \) \) $<eqn:pull-where>

We may hence define a function $sans(c f g) \( dot.op \)$ from lexical
SSA programs $r$ to control-flow graphs $G$ as follows:
$ sans(c f g) \( r \) = sans(e n t r y) \( r \) \, \( ell_i \( x_i \) : { sans(c f g) \( t_i \) } \, \)_(\( ell_i \( x_i \) : { t_i } \) in sans(c h i l d r e n) \( r \)) $
where we recursively flatten
$ G \, ell \( x \) : { beta \, G' } := G \, ell \( x \) : { beta } \, G' $
At the level of program text, all this function is doing is "removing
$sans(w h e r e)$-blocks;" so we'll call the result #emph[reased]. An
SSA program is #emph[well-formed] if:

- All variable uses are well-typed

- All variable uses respect dominance-based scoping

It is easy to see that any erased program is well-formed, since our
typing rules guarantee every expression is well-typed, while our lexical
scoping for values ensures that variables are only visible in the
children of the block $beta$ in which they are defined, which the
lexical scoping of labels guarantees are dominated by $beta$.

On the other hand, we may give an algorithm to convert any well-formed
SSA program $G$ into a well-typed lexical SSA program
$r = sans(r e g) \( G \)$ as follows:

+ Compute the dominance tree of $G$, rooted at its entry block $beta$.

+ For each child $ell_i \( x_i \) : { beta_i }$ of $beta$, let $G_i$
  denote the CFG composed of the descendants of $beta_i$ (with $beta_i$
  as entry block), given in the order they appear in $G$. Recursively
  compute $r_i = sans(r e g) \( G_i \)$.

+ Return the program
  $sans(b b) \( beta \, \( ell_i \( x_i \) : { r_i } \, \)_i \)$

We will write $G tilde.eq G'$ to mean "$G$ is a permutation of $G'$"
(that is, $G$ and $G'$ have the same entry block, but the other labels
may be reordered). It is easy to see that this algorithm yields a
lexical SSA program which erases to a permutation of $G$, i.e.,
$sans(c f g) \( sans(r e g) \( G \) \) tilde.eq G$, as desired. To
complete our argument, it hence suffices to show that, given lexical SSA
regions $Gamma tack.r r gt.tri sans(L)$,
$Gamma tack.r r' gt.tri sans(L)$, such that
$sans(c f g) \( r \) tilde.eq sans(c f g) \( r' \)$, we have that
$Gamma tack.r r approx r' gt.tri sans(L)$. We break this down into two
lemmas:

#block[
If $G tilde.eq G'$ and
$Gamma tack.r sans(r e g) \( G \) gt.tri sans(L)$, then
$Gamma tack.r sans(r e g) \( G' \) gt.tri sans(L)$ and
$Gamma tack.r sans(r e g) \( G \) approx sans(r e g) \( G' \) gt.tri sans(L)$

]
#block[
#emph[Proof.] See Appendix~#todo[Resolve source reference `proof:cfg-perm-invar` during integration.]~◻

]
#block[
Given a lexical SSA region $r$ (i.e., assuming
$sans(I s S S A) \( r \)$) s.t. $Gamma tack.r r gt.tri sans(L)$, we have
that
$Gamma tack.r r approx sans(r e g) \( sans(c f g) \( r \) \) gt.tri sans(L)$.

]
#block[
#emph[Proof.] See Appendix~#todo[Resolve source reference `proof:cfg-conversion` during integration.]~◻

]
It follows that, given lexical SSA regions
$Gamma tack.r r gt.tri sans(L)$ and $Gamma tack.r r' gt.tri sans(L)$, if
$sans(c f g) \( r \) tilde.eq sans(c f g) \( r' \)$, we have that
$Gamma tack.r r approx r' gt.tri sans(L)$, as desired, since in
particular
$ r approx sans(r e g) \( sans(c f g) \( r \) \) approx sans(r e g) \( sans(c f g) \( r' \) \) approx r' $
