// Equational and refinement theory for λ_iter, as reusable `#let` rule
// definitions. Import or copy these into the chapter; nothing here renders on
// its own.
//
//   #import "/thesis/type-theoretic-ssa/lambda-iter/theory.typ": *
//
// Layering (per the chapter's plan):
//   1. EQUIVALENCE (≈)  — symmetric; congruence + the βη/commuting axioms.
//   2. REFINEMENT  (↠)  — directed (a preorder, NOT symmetric); adds directed
//                         substitution gated on *movers* (directed
//                         commutativity), e.g. UB may always be moved forward.
//   3. SUBSTRUCTURALITY — quantities, context splitting, and linearity-gated
//                         laws are introduced LATER and are deliberately absent
//                         here (the effect side conditions are mover-only).
//
// Term/type/judgement notation (letx, casex, iterx, linl, linr, labort,
// tytensor, tysum, tyunit, tyempty, hastye, insttye, effiter, …) comes from
// `/lib/notation/lambda-iter.typ` via the prelude.

#import "/lib/prelude.typ": *

// ===========================================================================
//  New judgement / side-condition notation
// ===========================================================================

// Equivalence judgement Γ ⊢ a ≈ b : A is the effect-free `eqat` from the
// notation lib: equivalence and the effect system are deliberately separate.

// Refinement judgement Γ ⊢_R a ↠ b : A ("a is refined by b"). The subscript is
// the rewrite system R (the base peephole rewrites); the effect lives on the
// typing premises, not the turnstile.
#let tref(g, r, a, b, ty) = $#g attach(⊢, br: #r) #a ↠ #b : #ty$

// Polarity-marked refinement Γ ⊢_R a ↠^p b : A, p ∈ {+, -}: p = + is a ↠ b,
// p = - is b ↠ a. Lets a directed rule and its dual be stated at once.
#let trefp(g, r, a, b, ty, p) = $#g attach(⊢, br: #r) #a attach(↠, tr: #p) #b : #ty$

// R-relative equivalence Γ ⊢_R a ≈ b : A: mutual R-refinement (a ↠ b and b ↠ a).
// Distinct from the effect-free equational `eqat`; here ≈ is indexed by R.
#let treqr(g, r, a, b, ty) = $#g attach(⊢, br: #r) #a ≈ #b : #ty$

// The rewrite-system metavariable.
#let rwsys = $cal(R)$

// Single-variable substitution [a/x]b (subvar), parallel substitution [σ]a
// (subap), and substitution extension (σ, x ↦ a) (subcons) all come from
// `/lib/notation/lambda-iter.typ` via the prelude.

// --- Movers (directed commutativity) ---
// ε ⇀ η : ε is a right-mover over η (an ε-step may be pushed *after* an η-step).
#let rmove(e, n) = $#e ⇀ #n$
// ε ↽ η : ε is a left-mover over η (pushed *before*).
#let lmove(e, n) = $#e ↽ #n$
// ε ⇌ η : ε commutes with η (both a left- and a right-mover).
#let comm(e, n) = $#e ⇌ #n$
// Polarity-selected mover ⇀^p : ⇀^+ = ⇀, ⇀^- = ↽.
#let rmovep(e, n, p) = $#e attach(⇀, tr: #p) #n$

// --- Effect quantity (a teaser for the substructural type system) ---
// αl(ε) ∈ Q is the linearity/quantity of an effect. αl(ε) = ω ("unrestricted",
// `topq`) lets ε be freely dropped and duplicated -- exactly what an arbitrary
// substitution may do to the substituted expression.
#let elin(e) = $alpha_l (#e)$

// ===========================================================================
//  TYPING
// ===========================================================================

// --- Subtyping A <: B ------------------------------------------------------

#let s-base = rule(
  label: msc("base"),
  $X ≤ Y$,
  subty($X$, $Y$),
)
#let s-tensor = rule(
  label: msc("tensor"),
  subty($A$, $A'$), subty($B$, $B'$),
  subty($A tytensor B$, $A' tytensor B'$),
)
#let s-sum = rule(
  label: msc("sum"),
  subty($A$, $A'$), subty($B$, $B'$),
  subty($A tysum B$, $A' tysum B'$),
)
#let s-initial = rule(
  label: msc("initial"),
  subty($tyempty$, $A$),
)
#let s-terminal = rule(
  label: msc("terminal"),
  subty($A$, $tyunit$),
)

// --- Weakening Γ ⊑ Δ -------------------------------------------------------

#let w-nil = rule(
  label: msc("nil"),
  wkns($·$, $·$),
)
#let w-cons = rule(
  label: msc("cons"),
  wkns($Γ$, $Δ$), subty($A$, $B$),
  wkns($Γ, x : A$, $Δ, x : B$),
)
#let w-drop = rule(
  label: msc("drop"),
  wkns($Γ$, $Δ$),
  wkns($Γ, x : A$, $Δ$),
)

// --- Typing Γ ⊢ a : A (pure) -----------------------------------------------

#let t-var = rule(
  label: msc("var"),
  wkns($Γ$, $x : A$),
  hasty($Γ$, $x$, $A$),
)
#let t-inst = rule(
  label: msc("inst"),
  $f ∈ cal(I)$, $subty(A, isrc(f))$, $subty(itrg(f), B)$,
  instty($f$, $A$, $B$),
)
#let t-op = rule(
  label: msc("op"),
  instty($f$, $A$, $B$), hasty($Γ$, $a$, $A$),
  hasty($Γ$, $f med a$, $B$),
)
#let t-let = rule(
  label: msc("let"),
  hasty($Γ$, $a$, $A$), hasty($Γ, x : A$, $b$, $B$),
  hasty($Γ$, letx($x$, $a$, $b$), $B$),
)
#let t-unit = rule(
  label: msc("unit"),
  hasty($Γ$, $()$, $tyunit$),
)
#let t-pair = rule(
  label: msc("pair"),
  hasty($Γ$, $a$, $A$), hasty($Γ$, $b$, $B$),
  hasty($Γ$, $(a, b)$, $A tytensor B$),
)
#let t-let-pair = rule(
  label: msc("let-pair"),
  hasty($Γ$, $a$, $A tytensor B$), hasty($Γ, x : A, y : B$, $c$, $C$),
  hasty($Γ$, letx($(x, y)$, $a$, $c$), $C$),
)
#let t-inl = rule(
  label: msc("inl"),
  hasty($Γ$, $a$, $A$),
  hasty($Γ$, linl($a$), $A tysum B$),
)
#let t-inr = rule(
  label: msc("inr"),
  hasty($Γ$, $b$, $B$),
  hasty($Γ$, linr($b$), $A tysum B$),
)
#let t-abort = rule(
  label: msc("abort"),
  hasty($Γ$, $a$, $tyempty$),
  hasty($Γ$, labort($a$), $C$),
)
#let t-case = rule(
  label: msc("case"),
  hasty($Γ$, $e$, $A tysum B$),
  hasty($Γ, x : A$, $a$, $C$),
  hasty($Γ, y : B$, $b$, $C$),
  hasty($Γ$, casex($e$, $x$, $a$, $y$, $b$), $C$),
)
#let t-iter = rule(
  label: msc("iter"),
  hasty($Γ$, $a$, $A$),
  hasty($Γ, x : A$, $b$, $B tysum A$),
  hasty($Γ$, iterx($a$, $x$, $b$), $B$),
)

// --- Effectful typing Γ ⊢_ε a : A ------------------------------------------

#let te-var = rule(
  label: msc("var"),
  wkns($Γ$, $x : A$),
  hastye($Γ$, $ε$, $x$, $A$),
)
#let te-inst = rule(
  label: msc("inst"),
  $f ∈ cal(I)$, $isrc(f) = A$, $itrg(f) = B$, $ieff(f) ≤ ε$,
  insttye($f$, $A$, $ε$, $B$),
)
#let te-op = rule(
  label: msc("op"),
  insttye($f$, $A$, $ε$, $B$), hastye($Γ$, $ε$, $a$, $A$),
  hastye($Γ$, $ε$, $f med a$, $B$),
)
#let te-let = rule(
  label: msc("let"),
  hastye($Γ$, $ε$, $a$, $A$), hastye($Γ, x : A$, $ε$, $b$, $B$),
  hastye($Γ$, $ε$, letx($x$, $a$, $b$), $B$),
)
#let te-unit = rule(
  label: msc("unit"),
  hastye($Γ$, $ε$, $()$, $tyunit$),
)
#let te-pair = rule(
  label: msc("pair"),
  hastye($Γ$, $ε$, $a$, $A$), hastye($Γ$, $ε$, $b$, $B$),
  hastye($Γ$, $ε$, $(a, b)$, $A tytensor B$),
)
#let te-let-pair = rule(
  label: msc("let-pair"),
  hastye($Γ$, $ε$, $a$, $A tytensor B$), hastye($Γ, x : A, y : B$, $ε$, $c$, $C$),
  hastye($Γ$, $ε$, letx($(x, y)$, $a$, $c$), $C$),
)
#let te-inl = rule(
  label: msc("inl"),
  hastye($Γ$, $ε$, $a$, $A$),
  hastye($Γ$, $ε$, linl($a$), $A tysum B$),
)
#let te-inr = rule(
  label: msc("inr"),
  hastye($Γ$, $ε$, $b$, $B$),
  hastye($Γ$, $ε$, linr($b$), $A tysum B$),
)
#let te-abort = rule(
  label: msc("abort"),
  hastye($Γ$, $ε$, $a$, $tyempty$),
  hastye($Γ$, $ε$, labort($a$), $C$),
)
#let te-case = rule(
  label: msc("case"),
  hastye($Γ$, $ε$, $e$, $A tysum B$),
  hastye($Γ, x : A$, $ε$, $a$, $C$),
  hastye($Γ, y : B$, $ε$, $b$, $C$),
  hastye($Γ$, $ε$, casex($e$, $x$, $a$, $y$, $b$), $C$),
)
#let te-iter = rule(
  label: msc("iter"),
  hastye($Γ$, $ε$, $a$, $A$),
  hastye($Γ, x : A$, $ε$, $b$, $B tysum A$),
  hastye($Γ$, effiter($ε$), iterx($a$, $x$, $b$), $B$),
)

// ===========================================================================
//  SUBSTITUTION
// ===========================================================================

// --- Substitution typing Γ ⊢ σ ▷ Δ (parallel substitutions) ----------------

#let sub-nil = rule(
  label: msc("nil"),
  issub($Γ$, $·$, $·$),
)
#let sub-cons = rule(
  label: msc("cons"),
  issub($Γ$, $σ$, $Δ$), hasty($Γ$, $a$, $A$), $x ∉ σ$,
  issub($Γ$, $σ, x ↦ a$, $Δ, x : A$),
)

// --- Single-variable substitution action [a/x]b ----------------------------
// Replace the variable x by a in b, recursing through every former. Bound
// variables are assumed fresh for x and a (the usual variable convention), so
// no capture-avoiding side conditions clutter the binder cases.

#let subst-var-eqns = (
  $subvar(a, x, x) = a$,
  $subvar(a, x, y) = y "where" x ≠ y$,
  $subvar(a, x, f med b) = f med subvar(a, x, b)$,
  $subvar(a, x, letx(z, b, c)) = letx(z, subvar(a, x, b), subvar(a, x, c))$,
  $subvar(a, x, letx((y, z), b, c))
    = letx((y, z), subvar(a, x, b), subvar(a, x, c))$,
  $subvar(a, x, ()) = ()$,
  $subvar(a, x, (b, c)) = (subvar(a, x, b), subvar(a, x, c))$,
  $subvar(a, x, linl(b)) = linl(subvar(a, x, b))$,
  $subvar(a, x, linr(b)) = linr(subvar(a, x, b))$,
  $subvar(a, x, casex(e, y, b, z, c))
    = casex(subvar(a, x, e), y, subvar(a, x, b), z, subvar(a, x, c))$,
  $subvar(a, x, labort(b)) = labort(subvar(a, x, b))$,
  $subvar(a, x, iterx(b, y, c)) = iterx(subvar(a, x, b), y, subvar(a, x, c))$,
)

// --- Parallel substitution action [σ]a -------------------------------------
// A substitution σ (typed by `sub-nil`/`sub-cons`) acts on a term, recursing
// through every former. Binders are handled by extending σ with the identity
// mapping (σ, x ↦ x), keeping it capture-avoiding under the variable convention.

#let subst-par-eqns = (
  $subap(subcons(σ, x, a), x) = a$,
  $subap(subcons(σ, y, a), x) = subap(σ, x) "where" x ≠ y$,
  $subap(σ, f med a) = f med subap(σ, a)$,
  $subap(σ, letx(x, a, b)) = letx(x, subap(σ, a), subap(subcons(σ, x, x), b))$,
  $subap(σ, letx((x, y), a, b))
    = letx((x, y), subap(σ, a), subap(subcons(subcons(σ, x, x), y, y), b))$,
  $subap(σ, ()) = ()$,
  $subap(σ, (a, b)) = (subap(σ, a), subap(σ, b))$,
  $subap(σ, linl(a)) = linl(subap(σ, a))$,
  $subap(σ, linr(b)) = linr(subap(σ, b))$,
  $subap(σ, casex(e, x, a, y, b))
    = casex(subap(σ, e), x, subap(subcons(σ, x, x), a), y, subap(subcons(σ, y, y), b))$,
  $subap(σ, labort(a)) = labort(subap(σ, a))$,
  $subap(σ, iterx(a, x, b)) = iterx(subap(σ, a), x, subap(subcons(σ, x, x), b))$,
)

// ===========================================================================
//  EQUIVALENCE THEORY
// ===========================================================================

// The equivalence judgement Γ ⊢ a ≈ b : A carries NO effect: it relates terms
// that are well-typed under the (effect-free) typing judgement Γ ⊢ a : A.
// `let-β` is absent here -- substitution is sound only up to the effect/mover
// conditions of the refinement theory, so it lives there as `ref-let-beta`.

// --- Congruence (reflexivity, symmetry, transitivity + one rule per former) --

#let eqv-refl = rule(
  label: msc("refl"),
  hasty($Γ$, $a$, $A$),
  eqat($Γ$, $a$, $a$, $A$),
)
#let eqv-symm = rule(
  label: msc("symm"),
  eqat($Γ$, $a$, $b$, $A$),
  eqat($Γ$, $b$, $a$, $A$),
)
#let eqv-trans = rule(
  label: msc("trans"),
  eqat($Γ$, $a$, $b$, $A$),
  eqat($Γ$, $b$, $c$, $A$),
  eqat($Γ$, $a$, $c$, $A$),
)
#let eqv-op = rule(
  label: msc("op"),
  instty($f$, $A$, $B$),
  eqat($Γ$, $a$, $a'$, $A$),
  eqat($Γ$, $f med a$, $f med a'$, $B$),
)
#let eqv-let = rule(
  label: msc("let"),
  eqat($Γ$, $a$, $a'$, $A$),
  eqat($Γ, x : A$, $b$, $b'$, $B$),
  eqat($Γ$, letx($x$, $a$, $b$), letx($x$, $a'$, $b'$), $B$),
)
#let eqv-pair = rule(
  label: msc("pair"),
  eqat($Γ$, $a$, $a'$, $A$),
  eqat($Γ$, $b$, $b'$, $B$),
  eqat($Γ$, $(a, b)$, $(a', b')$, $A tytensor B$),
)
#let eqv-let-pair = rule(
  label: msc("let-pair"),
  eqat($Γ$, $e$, $e'$, $A tytensor B$),
  eqat($Γ, x : A, y : B$, $c$, $c'$, $C$),
  eqat($Γ$, letx($(x, y)$, $e$, $c$), letx($(x, y)$, $e'$, $c'$), $C$),
)
#let eqv-inl = rule(
  label: msc("inl"),
  eqat($Γ$, $a$, $a'$, $A$),
  eqat($Γ$, linl($a$), linl($a'$), $A tysum B$),
)
#let eqv-inr = rule(
  label: msc("inr"),
  eqat($Γ$, $b$, $b'$, $B$),
  eqat($Γ$, linr($b$), linr($b'$), $A tysum B$),
)
#let eqv-case = rule(
  label: msc("case"),
  eqat($Γ$, $e$, $e'$, $A tysum B$),
  eqat($Γ, x : A$, $a$, $a'$, $C$),
  eqat($Γ, y : B$, $b$, $b'$, $C$),
  eqat($Γ$, casex($e$, $x$, $a$, $y$, $b$), casex($e'$, $x$, $a'$, $y$, $b'$), $C$),
)
#let eqv-abort = rule(
  label: msc("abort"),
  eqat($Γ$, $a$, $a'$, $tyempty$),
  eqat($Γ$, labort($a$), labort($a'$), $C$),
)
#let eqv-iter = rule(
  label: msc("iter"),
  eqat($Γ$, $a$, $a'$, $A$),
  eqat($Γ, x : A$, $b$, $b'$, $B tysum A$),
  eqat($Γ$, iterx($a$, $x$, $b$), iterx($a'$, $x$, $b'$), $B$),
)

// --- Binding / let-normalisation (commuting conversions) -------------------

#let eqv-let-op = rule(
  label: msc("let-op"),
  instty($f$, $A$, $B$),
  hasty($Γ$, $a$, $A$),
  hasty($Γ, y : B$, $c$, $C$),
  eqat($Γ$,
    letx($y$, $f med a$, $c$),
    letx($x$, $a$, letx($y$, $f med x$, $c$)),
    $C$),
)
#let eqv-let-let = rule(
  label: msc("let-let"),
  hasty($Γ$, $a$, $A$),
  hasty($Γ, x : A$, $b$, $B$),
  hasty($Γ, y : B$, $c$, $C$),
  eqat($Γ$,
    letx($y$, $(#letx($x$, $a$, $b$))$, $c$),
    letx($x$, $a$, letx($y$, $b$, $c$)),
    $C$),
)
#let eqv-let-let-pair = rule(
  label: msc("let-let-pair"),
  hasty($Γ$, $e$, $A tytensor B$),
  hasty($Γ, x : A, y : B$, $c$, $C$),
  hasty($Γ, z : C$, $d$, $D$),
  eqat($Γ$,
    letx($z$, $(#letx($(x, y)$, $e$, $c$))$, $d$),
    letx($(x, y)$, $e$, letx($z$, $c$, $d$)),
    $D$),
)
#let eqv-let-case = rule(
  label: msc("let-case"),
  hasty($Γ$, $e$, $A tysum B$),
  hasty($Γ, x : A$, $a$, $C$),
  hasty($Γ, y : B$, $b$, $C$),
  hasty($Γ, z : C$, $d$, $D$),
  eqat($Γ$,
    letx($z$, casex($e$, $x$, $a$, $y$, $b$), $d$),
    casex($e$, $x$, letx($z$, $a$, $d$), $y$, letx($z$, $b$, $d$)),
    $D$),
)
#let eqv-let-pair-bind = rule(
  label: msc("let-pair-bind"),
  hasty($Γ$, $a$, $A tytensor B$),
  hasty($Γ, x : A, y : B$, $c$, $C$),
  eqat($Γ$,
    letx($(x, y)$, $a$, $c$),
    letx($z$, $a$, letx($(x, y)$, $z$, $c$)),
    $C$),
)
#let eqv-case-bind = rule(
  label: msc("case-bind"),
  hasty($Γ$, $e$, $A tysum B$),
  hasty($Γ, x : A$, $a$, $C$),
  hasty($Γ, y : B$, $b$, $C$),
  eqat($Γ$,
    casex($e$, $x$, $a$, $y$, $b$),
    letx($z$, $e$, casex($z$, $x$, $a$, $y$, $b$)),
    $C$),
)

// --- β / η reductions ------------------------------------------------------

// let-β, restricted to a PURE bound expression (Γ ⊢_⊥ a : A). A pure a commutes
// with everything and may be freely dropped or duplicated, so substituting it is
// sound with no further side conditions; the effectful, directed generalisation
// is `ref-let-beta` in the refinement theory.
#let eqv-let-beta = rule(
  label: msc("let-β"),
  hastye($Γ$, $effpure$, $a$, $A$),
  hasty($Γ, x : A$, $b$, $B$),
  eqat($Γ$, letx($x$, $a$, $b$), subvar($a$, $x$, $b$), $B$),
)
// let-η: a let whose body is just the bound variable is the bound expression.
#let eqv-let-eta = rule(
  label: msc("let-η"),
  hasty($Γ$, $a$, $A$),
  eqat($Γ$, letx($x$, $a$, $x$), $a$, $A$),
)
// Unit η: a unit-typed result is its own sequencing.
#let eqv-unit = rule(
  label: msc("unit"),
  hasty($Γ$, $a$, $tyunit$),
  eqat($Γ$, letx($x$, $a$, $()$), $a$, $tyunit$),
)
// Empty type: everything after an aborting binding is equated (dead code).
#let eqv-init = rule(
  label: msc("init"),
  hasty($Γ$, $a$, $tyempty$),
  hasty($Γ, x : A$, $b$, $B$),
  hasty($Γ, x : A$, $b'$, $B$),
  eqat($Γ$, letx($x$, labort($a$), $b$), letx($x$, labort($a$), $b'$), $B$),
)
#let eqv-pair-beta = rule(
  label: msc("pair-β"),
  hasty($Γ$, $a$, $A$),
  hasty($Γ$, $b$, $B$),
  hasty($Γ, x : A, y : B$, $c$, $C$),
  eqat($Γ$,
    letx($(x, y)$, $(a, b)$, $c$),
    letx($x$, $a$, letx($y$, $b$, $c$)),
    $C$),
)
#let eqv-pair-eta = rule(
  label: msc("pair-η"),
  hasty($Γ$, $a$, $A tytensor B$),
  eqat($Γ$, letx($(x, y)$, $a$, $(x, y)$), $a$, $A tytensor B$),
)
#let eqv-case-betal = rule(
  label: msc("case-βl"),
  hasty($Γ$, $e$, $A$),
  hasty($Γ, x : A$, $a$, $C$),
  hasty($Γ, y : B$, $b$, $C$),
  eqat($Γ$, casex(linl($e$), $x$, $a$, $y$, $b$), letx($x$, $e$, $a$), $C$),
)
#let eqv-case-betar = rule(
  label: msc("case-βr"),
  hasty($Γ$, $e$, $B$),
  hasty($Γ, x : A$, $a$, $C$),
  hasty($Γ, y : B$, $b$, $C$),
  eqat($Γ$, casex(linr($e$), $x$, $a$, $y$, $b$), letx($y$, $e$, $b$), $C$),
)
#let eqv-case-eta = rule(
  label: msc("case-η"),
  hasty($Γ$, $e$, $A tysum B$),
  eqat($Γ$, casex($e$, $x$, linl($x$), $y$, linr($y$)), $e$, $A tysum B$),
)

// --- Iteration (Conway / Elgot axioms) -------------------------------------

// Fixpoint unfolding: one pass of the loop.
#let eqv-iter-beta = rule(
  label: msc("iter-β"),
  hasty($Γ$, $a$, $A$),
  hasty($Γ, x : A$, $b$, $B tysum A$),
  eqat($Γ$,
    iterx($a$, $x$, $b$),
    letx($x$, $a$, casex($b$, $y$, $y$, $z$, iterx($z$, $x$, $b$))),
    $B$),
)
// Naturality: a continuation after a loop moves into the loop's exit branch.
#let eqv-iter-nat = rule(
  label: msc("let-iter"),
  hasty($Γ$, $a$, $A$),
  hasty($Γ, x : A$, $b$, $B tysum A$),
  hasty($Γ, y : B$, $c$, $C$),
  eqat($Γ$,
    letx($y$, iterx($a$, $x$, $b$), $c$),
    iterx($a$, $x$, casex($b$, $y$, linl($c$), $z$, linr($z$))),
    $C$),
)
// Codiagonal: a loop nested on the same parameter collapses to a single loop.
#let eqv-iter-codiag = rule(
  label: msc("codiag"),
  hasty($Γ$, $a$, $A$),
  hasty($Γ, x : A$, $b$, $(B tysum A) tysum A$),
  eqat($Γ$,
    iterx($a$, $x$, iterx($x$, $y$, $b$)),
    iterx($a$, $y$, casex($b$, $x$, $x$, $y$, linr($y$))),
    $B$),
)
// Uniformity: two loops whose states are related by a PURE comparison h agree.
// h : A → A' transports the A-loop to the A'-loop; the middle premise is the
// commuting square `f ; (id + h) = h ; g`. This is NOT derivable from
// fixpoint/naturality/codiagonal (uniformity is independent of the Conway
// axioms); restricting h to be pure makes the general rule's mover side
// condition trivial, so only h's purity appears.
#let eqv-uniformity = rule(
  label: msc("uniformity"),
  hasty($Γ$, $a$, $A$),
  hastye($Γ, x : A$, $effpure$, $h$, $A'$),
  eqat($Γ, x : A$,
    casex($b$, $y$, linl($y$), $x$, linr($h$)),
    subvar($h$, $x'$, $b'$),
    $B tysum A'$),
  eqat($Γ$,
    iterx($a$, $x$, $b$),
    iterx($(#letx($x$, $a$, $h$))$, $x'$, $b'$),
    $B$),
)
// Binding: float the loop's initial value out into a let.
#let eqv-iter-bind = rule(
  label: msc("iter-bind"),
  hasty($Γ$, $a$, $A$),
  hasty($Γ, x : A$, $b$, $B tysum A$),
  eqat($Γ$,
    iterx($a$, $x$, $b$),
    letx($y$, $a$, iterx($y$, $x$, $b$)),
    $B$),
)

// --- Pure let-distribution (deriving let-β) ---------------------------------
// For a PURE bound expression (Γ ⊢_⊥ e : A), `let x = e; -` distributes through
// every former, exactly following the cases of single-variable substitution
// `subvar`. Together with `let-η` (the variable-hit case, let x = e; x ≈ e),
// these derive `let-β` (let x = e; b ≈ [e/x]b) by induction on b.

// Variable (miss): a binding the body does not use is dropped.
#let eqv-push-var = rule(
  label: msc("let-ne"),
  hastye($Γ$, $effpure$, $e$, $A$),
  hasty($Γ$, $y$, $B$),
  $x ≠ y$,
  eqat($Γ$, letx($x$, $e$, $y$), $y$, $B$),
)
#let eqv-push-op = rule(
  label: msc("let-op"),
  hastye($Γ$, $effpure$, $e$, $A$),
  instty($f$, $B$, $C$),
  hasty($Γ, x : A$, $a$, $B$),
  eqat($Γ$, letx($x$, $e$, $f med a$), $f med (#letx($x$, $e$, $a$))$, $C$),
)
#let eqv-push-nil = rule(
  label: msc("let-nil"),
  hastye($Γ$, $effpure$, $e$, $A$),
  eqat($Γ$, letx($x$, $e$, $()$), $()$, $tyunit$),
)
#let eqv-push-pair = rule(
  label: msc("let-pair"),
  hastye($Γ$, $effpure$, $e$, $A$),
  hasty($Γ, x : A$, $a$, $B$),
  hasty($Γ, x : A$, $b$, $C$),
  eqat($Γ$,
    letx($x$, $e$, $(a, b)$),
    $(#letx($x$, $e$, $a$), #letx($x$, $e$, $b$))$,
    $B tytensor C$),
)
#let eqv-push-inl = rule(
  label: msc("let-inl"),
  hastye($Γ$, $effpure$, $e$, $A$),
  hasty($Γ, x : A$, $a$, $B$),
  eqat($Γ$, letx($x$, $e$, linl($a$)), linl($(#letx($x$, $e$, $a$))$), $B tysum C$),
)
#let eqv-push-inr = rule(
  label: msc("let-inr"),
  hastye($Γ$, $effpure$, $e$, $A$),
  hasty($Γ, x : A$, $b$, $C$),
  eqat($Γ$, letx($x$, $e$, linr($b$)), linr($(#letx($x$, $e$, $b$))$), $B tysum C$),
)
#let eqv-push-let = rule(
  label: msc("let"),
  hastye($Γ$, $effpure$, $e$, $A$),
  hasty($Γ, x : A$, $a$, $B$),
  hasty($Γ, x : A, y : B$, $b$, $C$),
  eqat($Γ$,
    letx($x$, $e$, letx($y$, $a$, $b$)),
    letx($y$, $(#letx($x$, $e$, $a$))$, letx($x$, $e$, $b$)),
    $C$),
)
#let eqv-push-let-pair = rule(
  label: msc("let-pair"),
  hastye($Γ$, $effpure$, $e$, $A$),
  hasty($Γ, x : A$, $a$, $B tytensor C$),
  hasty($Γ, x : A, y : B, z : C$, $b$, $D$),
  eqat($Γ$,
    letx($x$, $e$, letx($(y, z)$, $a$, $b$)),
    letx($(y, z)$, $(#letx($x$, $e$, $a$))$, letx($x$, $e$, $b$)),
    $D$),
)
#let eqv-push-case = rule(
  label: msc("case"),
  hastye($Γ$, $effpure$, $e$, $A$),
  hasty($Γ, x : A$, $a$, $B tysum C$),
  hasty($Γ, x : A, y : B$, $b$, $D$),
  hasty($Γ, x : A, z : C$, $c$, $D$),
  eqat($Γ$,
    letx($x$, $e$, casex($a$, $y$, $b$, $z$, $c$)),
    casex($(#letx($x$, $e$, $a$))$, $y$, letx($x$, $e$, $b$), $z$, letx($x$, $e$, $c$)),
    $D$),
)
#let eqv-push-abort = rule(
  label: msc("abort"),
  hastye($Γ$, $effpure$, $e$, $A$),
  hasty($Γ, x : A$, $a$, $tyempty$),
  eqat($Γ$, letx($x$, $e$, labort($a$)), labort($(#letx($x$, $e$, $a$))$), $C$),
)
#let eqv-push-iter = rule(
  label: msc("iter"),
  hastye($Γ$, $effpure$, $e$, $A$),
  hasty($Γ, x : A$, $a$, $B$),
  hasty($Γ, x : A, y : B$, $b$, $C tysum B$),
  eqat($Γ$,
    letx($x$, $e$, iterx($a$, $y$, $b$)),
    iterx($(#letx($x$, $e$, $a$))$, $y$, letx($x$, $e$, $b$)),
    $C$),
)

// ===========================================================================
//  REFINEMENT THEORY  (directed; a preorder — no `symm`)
// ===========================================================================

// --- Congruence ------------------------------------------------------------

#let ref-base = rule(
  label: msc("base"),
  $(a ↠ b : A) ∈ cal(R)$,
  tref($Γ$, rwsys, $a$, $b$, $A$),
)
#let ref-refl = rule(
  label: msc("refl"),
  hastye($Γ$, $ε$, $a$, $A$),
  tref($Γ$, rwsys, $a$, $a$, $A$),
)
#let ref-trans = rule(
  label: msc("trans"),
  tref($Γ$, rwsys, $a$, $b$, $A$),
  tref($Γ$, rwsys, $b$, $c$, $A$),
  tref($Γ$, rwsys, $a$, $c$, $A$),
)
#let ref-op = rule(
  label: msc("op"),
  insttye($f$, $A$, $ε$, $B$),
  tref($Γ$, rwsys, $a$, $a'$, $A$),
  tref($Γ$, rwsys, $f med a$, $f med a'$, $B$),
)
#let ref-let = rule(
  label: msc("let"),
  tref($Γ$, rwsys, $a$, $a'$, $A$),
  tref($Γ, x : A$, rwsys, $b$, $b'$, $B$),
  tref($Γ$, rwsys, letx($x$, $a$, $b$), letx($x$, $a'$, $b'$), $B$),
)
#let ref-pair = rule(
  label: msc("pair"),
  tref($Γ$, rwsys, $a$, $a'$, $A$),
  tref($Γ$, rwsys, $b$, $b'$, $B$),
  tref($Γ$, rwsys, $(a, b)$, $(a', b')$, $A tytensor B$),
)
#let ref-let-pair = rule(
  label: msc("let-pair"),
  tref($Γ$, rwsys, $e$, $e'$, $A tytensor B$),
  tref($Γ, x : A, y : B$, rwsys, $c$, $c'$, $C$),
  tref($Γ$, rwsys, letx($(x, y)$, $e$, $c$), letx($(x, y)$, $e'$, $c'$), $C$),
)
#let ref-inl = rule(
  label: msc("inl"),
  tref($Γ$, rwsys, $a$, $a'$, $A$),
  tref($Γ$, rwsys, linl($a$), linl($a'$), $A tysum B$),
)
#let ref-inr = rule(
  label: msc("inr"),
  tref($Γ$, rwsys, $b$, $b'$, $B$),
  tref($Γ$, rwsys, linr($b$), linr($b'$), $A tysum B$),
)
#let ref-case = rule(
  label: msc("case"),
  tref($Γ$, rwsys, $e$, $e'$, $A tysum B$),
  tref($Γ, x : A$, rwsys, $a$, $a'$, $C$),
  tref($Γ, y : B$, rwsys, $b$, $b'$, $C$),
  tref($Γ$, rwsys, casex($e$, $x$, $a$, $y$, $b$), casex($e'$, $x$, $a'$, $y$, $b'$), $C$),
)
#let ref-abort = rule(
  label: msc("abort"),
  tref($Γ$, rwsys, $a$, $a'$, $tyempty$),
  tref($Γ$, rwsys, labort($a$), labort($a'$), $C$),
)
#let ref-iter = rule(
  label: msc("iter"),
  tref($Γ$, rwsys, $a$, $a'$, $A$),
  tref($Γ, x : A$, rwsys, $b$, $b'$, $B tysum A$),
  tref($Γ$, rwsys, iterx($a$, $x$, $b$), iterx($a'$, $x$, $b'$), $B$),
)

// --- Equivalence as mutual refinement --------------------------------------

// Two terms are R-equivalent when each refines the other: a ↠ b and b ↠ a.
#let ref-equiv = rule(
  label: msc("equiv"),
  tref($Γ$, rwsys, $a$, $b$, $A$),
  tref($Γ$, rwsys, $b$, $a$, $A$),
  treqr($Γ$, rwsys, $a$, $b$, $A$),
)
#let ref-equiv-rules = (ref-equiv,)

// --- Directed substitution -------------------------------------------------

// The headline directed law. Substitute a (possibly effectful) `a` for `x`,
// provided a's effect ε is a p-mover over the body's effect η (p = + pushes the
// binding inward, a ↠ [a/x]b; p = - is the reverse) AND ε has unrestricted
// quantity αl(ε) = ω, so it may be dropped or duplicated as x's occurrences in b
// demand. Tracking the *exact* multiplicity of x (affine to drop, relevant to
// duplicate) instead of demanding ω is the job of the substructural type system.
#let ref-let-beta = rule(
  label: msc("let-β"),
  hastye($Γ$, $ε$, $a$, $A$),
  hastye($Γ, x : A$, $η$, $b$, $B$),
  rmovep($ε$, $η$, $p$),
  $elin(ε) = topq$,
  trefp($Γ$, rwsys, letx($x$, $a$, $b$), subvar($a$, $x$, $b$), $B$, $p$),
)

// ===========================================================================
//  Figure groupings + helper
// ===========================================================================

#let subtyping-rules = (s-base, s-tensor, s-sum, s-initial, s-terminal)
#let weakening-rules = (w-nil, w-cons, w-drop)
#let typing-rules = (
  t-var, t-inst, t-op, t-let, t-unit, t-pair, t-let-pair,
  t-inl, t-inr, t-abort, t-case, t-iter,
)
#let typing-eff-rules = (
  te-var, te-inst, te-op, te-let, te-unit, te-pair, te-let-pair,
  te-inl, te-inr, te-abort, te-case, te-iter,
)
#let subst-typing-rules = (sub-nil, sub-cons)

#let eqv-congruence-rules = (
  eqv-refl, eqv-symm, eqv-trans,
  eqv-op, eqv-let, eqv-pair, eqv-let-pair,
  eqv-inl, eqv-inr, eqv-case, eqv-abort, eqv-iter,
)
// The equational axioms, split by former: let rules, case (+ empty/abort)
// rules, and the fixpoint (Conway iteration) rules.
#let eqv-let-rules = (eqv-let-beta, eqv-let-eta, eqv-unit, eqv-pair-beta)
#let eqv-case-rules = (eqv-case-betal, eqv-case-betar, eqv-case-eta, eqv-init)
#let eqv-fixpoint-rules = (
  eqv-iter-beta, eqv-iter-nat, eqv-iter-codiag, eqv-uniformity,
)

// The pure let-distribution rules (one per substitution case) that derive let-β.
#let eqv-push-rules = (
  eqv-push-var, eqv-push-op, eqv-push-nil, eqv-push-pair,
  eqv-push-inl, eqv-push-inr, eqv-push-let, eqv-push-let-pair,
  eqv-push-case, eqv-push-abort, eqv-push-iter,
)

// Commuting conversions / η / bind laws, kept available but not part of the
// core βη presentation above.
#let eqv-binding-rules = (
  eqv-let-op, eqv-let-let, eqv-let-let-pair,
  eqv-let-case, eqv-let-pair-bind, eqv-case-bind,
  eqv-pair-eta, eqv-iter-bind,
)

#let ref-congruence-rules = (
  ref-base, ref-refl, ref-trans,
  ref-op, ref-let, ref-pair, ref-let-pair,
  ref-inl, ref-inr, ref-case, ref-abort, ref-iter,
)
// Refinement adds a single directed rule -- directed substitution (let-β);
// every other rule of the theory is equational (a two-way refinement).
#let ref-directed-rules = (ref-let-beta,)

// Lay an array of rules out as a single `rule-set` of proof trees.
#let rules-block(rules) = rule-set(..rules.map(prooftree))
