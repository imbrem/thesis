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

// Equivalence judgement Γ ⊢_ε a ≈ b : A. The effect ε rides the turnstile's
// bottom-right corner, matching `hastye`.
#let tmeqv(g, e, a, b, ty) = $#g attach(⊢, br: #e) #a ≈ #b : #ty$

// Refinement judgement Γ ⊢_R a ↠ b : A ("a is refined by b"). The subscript is
// the rewrite system R (the base peephole rewrites); the effect lives on the
// typing premises, not the turnstile.
#let tref(g, r, a, b, ty) = $#g attach(⊢, br: #r) #a ↠ #b : #ty$

// Polarity-marked refinement Γ ⊢_R a ↠^p b : A, p ∈ {+, -}: p = + is a ↠ b,
// p = - is b ↠ a. Lets a directed rule and its dual be stated at once.
#let trefp(g, r, a, b, ty, p) = $#g attach(⊢, br: #r) #a attach(↠, tr: #p) #b : #ty$

// The rewrite-system metavariable.
#let rwsys = $cal(R)$

// Single-variable substitution [a/x]b: replace x by a in b.
#let substx(a, x, b) = $[#a slash #x] #b$

// --- Movers (directed commutativity) ---
// ε ⇀ η : ε is a right-mover over η (an ε-step may be pushed *after* an η-step).
#let rmove(e, n) = $#e ⇀ #n$
// ε ↽ η : ε is a left-mover over η (pushed *before*).
#let lmove(e, n) = $#e ↽ #n$
// ε ⇌ η : ε commutes with η (both a left- and a right-mover).
#let comm(e, n) = $#e ⇌ #n$
// Polarity-selected mover ⇀^p : ⇀^+ = ⇀, ⇀^- = ↽.
#let rmovep(e, n, p) = $#e attach(⇀, tr: #p) #n$

// --- Concrete effects for examples ---
// Undefined behaviour (UB).
#let lub = $↯$
// Partial coproduct projections ρ_l, ρ_r.
#let lprojl(a) = $rho_l med #a$
#let lprojr(a) = $rho_r med #a$

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
  $[a slash x] x = a$,
  $[a slash x] y = y "where" x ≠ y$,
  $[a slash x](f med b) = f med [a slash x] b$,
  $[a slash x](#letx($z$, $b$, $c$)) = #letx($z$, $[a slash x] b$, $[a slash x] c$)$,
  $[a slash x](#letx($(y, z)$, $b$, $c$))
    = #letx($(y, z)$, $[a slash x] b$, $[a slash x] c$)$,
  $[a slash x]() = ()$,
  $[a slash x](b, c) = ([a slash x] b, [a slash x] c)$,
  $[a slash x](linl(b)) = linl([a slash x] b)$,
  $[a slash x](linr(b)) = linr([a slash x] b)$,
  $[a slash x](#casex($e$, $y$, $b$, $z$, $c$))
    = #casex($[a slash x] e$, $y$, $[a slash x] b$, $z$, $[a slash x] c$)$,
  $[a slash x](#labort($b$)) = #labort($[a slash x] b$)$,
  $[a slash x](#iterx($b$, $y$, $c$)) = #iterx($[a slash x] b$, $y$, $[a slash x] c$)$,
)

// --- Parallel substitution action [σ]a -------------------------------------
// A substitution σ (typed by `sub-nil`/`sub-cons`) acts on a term, recursing
// through every former. Binders are handled by extending σ with the identity
// mapping (σ, x ↦ x), keeping it capture-avoiding under the variable convention.

#let subst-par-eqns = (
  $[(σ, x ↦ a)]x = a$,
  $[(σ, y ↦ a)]x = [σ]x "where" x ≠ y$,
  $[σ](f med a) = f med [σ]a$,
  $[σ](#letx($x$, $a$, $b$)) = #letx($x$, $[σ]a$, $[σ, x ↦ x]b$)$,
  $[σ](#letx($(x, y)$, $a$, $b$))
    = #letx($(x, y)$, $[σ]a$, $[σ, x ↦ x, y ↦ y]b$)$,
  $[σ]() = ()$,
  $[σ](a, b) = ([σ]a, [σ]b)$,
  $[σ](linl(a)) = linl([σ]a)$,
  $[σ](linr(b)) = linr([σ]b)$,
  $[σ](#casex($e$, $x$, $a$, $y$, $b$))
    = #casex($[σ]e$, $x$, $[σ, x ↦ x]a$, $y$, $[σ, y ↦ y]b$)$,
  $[σ](#labort($a$)) = #labort($[σ]a$)$,
  $[σ](#iterx($a$, $x$, $b$)) = #iterx($[σ]a$, $x$, $[σ, x ↦ x]b$)$,
)

// ===========================================================================
//  EQUIVALENCE THEORY
// ===========================================================================

// --- Congruence (reflexivity, symmetry, transitivity + one rule per former) --

#let eqv-refl = rule(
  label: msc("refl"),
  hastye($Γ$, $ε$, $a$, $A$),
  tmeqv($Γ$, $ε$, $a$, $a$, $A$),
)
#let eqv-symm = rule(
  label: msc("symm"),
  tmeqv($Γ$, $ε$, $a$, $b$, $A$),
  tmeqv($Γ$, $ε$, $b$, $a$, $A$),
)
#let eqv-trans = rule(
  label: msc("trans"),
  tmeqv($Γ$, $ε$, $a$, $b$, $A$),
  tmeqv($Γ$, $ε$, $b$, $c$, $A$),
  tmeqv($Γ$, $ε$, $a$, $c$, $A$),
)
#let eqv-op = rule(
  label: msc("op"),
  insttye($f$, $A$, $ε$, $B$),
  tmeqv($Γ$, $ε$, $a$, $a'$, $A$),
  tmeqv($Γ$, $ε$, $f med a$, $f med a'$, $B$),
)
#let eqv-let = rule(
  label: msc("let"),
  tmeqv($Γ$, $ε$, $a$, $a'$, $A$),
  tmeqv($Γ, x : A$, $ε$, $b$, $b'$, $B$),
  tmeqv($Γ$, $ε$, letx($x$, $a$, $b$), letx($x$, $a'$, $b'$), $B$),
)
#let eqv-pair = rule(
  label: msc("pair"),
  tmeqv($Γ$, $ε$, $a$, $a'$, $A$),
  tmeqv($Γ$, $ε$, $b$, $b'$, $B$),
  tmeqv($Γ$, $ε$, $(a, b)$, $(a', b')$, $A tytensor B$),
)
#let eqv-let-pair = rule(
  label: msc("let-pair"),
  tmeqv($Γ$, $ε$, $e$, $e'$, $A tytensor B$),
  tmeqv($Γ, x : A, y : B$, $ε$, $c$, $c'$, $C$),
  tmeqv($Γ$, $ε$, letx($(x, y)$, $e$, $c$), letx($(x, y)$, $e'$, $c'$), $C$),
)
#let eqv-inl = rule(
  label: msc("inl"),
  tmeqv($Γ$, $ε$, $a$, $a'$, $A$),
  tmeqv($Γ$, $ε$, linl($a$), linl($a'$), $A tysum B$),
)
#let eqv-inr = rule(
  label: msc("inr"),
  tmeqv($Γ$, $ε$, $b$, $b'$, $B$),
  tmeqv($Γ$, $ε$, linr($b$), linr($b'$), $A tysum B$),
)
#let eqv-case = rule(
  label: msc("case"),
  tmeqv($Γ$, $ε$, $e$, $e'$, $A tysum B$),
  tmeqv($Γ, x : A$, $ε$, $a$, $a'$, $C$),
  tmeqv($Γ, y : B$, $ε$, $b$, $b'$, $C$),
  tmeqv($Γ$, $ε$, casex($e$, $x$, $a$, $y$, $b$), casex($e'$, $x$, $a'$, $y$, $b'$), $C$),
)
#let eqv-abort = rule(
  label: msc("abort"),
  tmeqv($Γ$, $ε$, $a$, $a'$, $tyempty$),
  tmeqv($Γ$, $ε$, labort($a$), labort($a'$), $C$),
)
#let eqv-iter = rule(
  label: msc("iter"),
  tmeqv($Γ$, $ε$, $a$, $a'$, $A$),
  tmeqv($Γ, x : A$, $ε$, $b$, $b'$, $B tysum A$),
  tmeqv($Γ$, effiter($ε$), iterx($a$, $x$, $b$), iterx($a'$, $x$, $b'$), $B$),
)

// --- Binding / let-normalisation (commuting conversions) -------------------

#let eqv-let-eta = rule(
  label: msc("let-η"),
  hastye($Γ$, $ε$, $a$, $A$),
  tmeqv($Γ$, $ε$, letx($x$, $a$, $x$), $a$, $A$),
)
#let eqv-let-op = rule(
  label: msc("let-op"),
  insttye($f$, $A$, $ε$, $B$),
  hastye($Γ$, $ε$, $a$, $A$),
  hastye($Γ, y : B$, $ε$, $c$, $C$),
  tmeqv($Γ$, $ε$,
    letx($y$, $f med a$, $c$),
    letx($x$, $a$, letx($y$, $f med x$, $c$)),
    $C$),
)
#let eqv-let-let = rule(
  label: msc("let-let"),
  hastye($Γ$, $ε$, $a$, $A$),
  hastye($Γ, x : A$, $ε$, $b$, $B$),
  hastye($Γ, y : B$, $ε$, $c$, $C$),
  tmeqv($Γ$, $ε$,
    letx($y$, letx($x$, $a$, $b$), $c$),
    letx($x$, $a$, letx($y$, $b$, $c$)),
    $C$),
)
#let eqv-let-let-pair = rule(
  label: msc("let-let-pair"),
  hastye($Γ$, $ε$, $e$, $A tytensor B$),
  hastye($Γ, x : A, y : B$, $ε$, $c$, $C$),
  hastye($Γ, z : C$, $ε$, $d$, $D$),
  tmeqv($Γ$, $ε$,
    letx($z$, letx($(x, y)$, $e$, $c$), $d$),
    letx($(x, y)$, $e$, letx($z$, $c$, $d$)),
    $D$),
)
#let eqv-let-case = rule(
  label: msc("let-case"),
  hastye($Γ$, $ε$, $e$, $A tysum B$),
  hastye($Γ, x : A$, $ε$, $a$, $C$),
  hastye($Γ, y : B$, $ε$, $b$, $C$),
  hastye($Γ, z : C$, $ε$, $d$, $D$),
  tmeqv($Γ$, $ε$,
    letx($z$, casex($e$, $x$, $a$, $y$, $b$), $d$),
    casex($e$, $x$, letx($z$, $a$, $d$), $y$, letx($z$, $b$, $d$)),
    $D$),
)
#let eqv-let-pair-bind = rule(
  label: msc("let-pair-bind"),
  hastye($Γ$, $ε$, $a$, $A tytensor B$),
  hastye($Γ, x : A, y : B$, $ε$, $c$, $C$),
  tmeqv($Γ$, $ε$,
    letx($(x, y)$, $a$, $c$),
    letx($z$, $a$, letx($(x, y)$, $z$, $c$)),
    $C$),
)
#let eqv-case-bind = rule(
  label: msc("case-bind"),
  hastye($Γ$, $ε$, $e$, $A tysum B$),
  hastye($Γ, x : A$, $ε$, $a$, $C$),
  hastye($Γ, y : B$, $ε$, $b$, $C$),
  tmeqv($Γ$, $ε$,
    casex($e$, $x$, $a$, $y$, $b$),
    letx($z$, $e$, casex($z$, $x$, $a$, $y$, $b$)),
    $C$),
)

// --- β / η reductions ------------------------------------------------------

// β for let, restricted to a PURE bound expression (the directed, effectful
// version lives in the refinement theory as `ref-let-beta`).
#let eqv-let-beta = rule(
  label: msc("let-β"),
  hastye($Γ$, $effpure$, $a$, $A$),
  hastye($Γ, x : A$, $ε$, $b$, $B$),
  tmeqv($Γ$, $ε$, letx($x$, $a$, $b$), substx($a$, $x$, $b$), $B$),
)
// Unit η: a unit-typed result is its own sequencing.
#let eqv-unit = rule(
  label: msc("unit"),
  hastye($Γ$, $ε$, $a$, $tyunit$),
  tmeqv($Γ$, $ε$, letx($x$, $a$, $()$), $a$, $tyunit$),
)
// Empty type: everything after an aborting binding is equated (dead code).
#let eqv-init = rule(
  label: msc("init"),
  hastye($Γ$, $ε$, $a$, $tyempty$),
  hastye($Γ, x : A$, $ε$, $b$, $B$),
  hastye($Γ, x : A$, $ε$, $b'$, $B$),
  tmeqv($Γ$, $ε$, letx($x$, labort($a$), $b$), letx($x$, labort($a$), $b'$), $B$),
)
#let eqv-pair-beta = rule(
  label: msc("pair-β"),
  hastye($Γ$, $ε$, $a$, $A$),
  hastye($Γ$, $ε$, $b$, $B$),
  hastye($Γ, x : A, y : B$, $ε$, $c$, $C$),
  tmeqv($Γ$, $ε$,
    letx($(x, y)$, $(a, b)$, $c$),
    letx($x$, $a$, letx($y$, $b$, $c$)),
    $C$),
)
#let eqv-pair-eta = rule(
  label: msc("pair-η"),
  hastye($Γ$, $ε$, $a$, $A tytensor B$),
  tmeqv($Γ$, $ε$, letx($(x, y)$, $a$, $(x, y)$), $a$, $A tytensor B$),
)
#let eqv-case-betal = rule(
  label: msc("case-βl"),
  hastye($Γ$, $ε$, $e$, $A$),
  hastye($Γ, x : A$, $ε$, $a$, $C$),
  hastye($Γ, y : B$, $ε$, $b$, $C$),
  tmeqv($Γ$, $ε$, casex(linl($e$), $x$, $a$, $y$, $b$), letx($x$, $e$, $a$), $C$),
)
#let eqv-case-betar = rule(
  label: msc("case-βr"),
  hastye($Γ$, $ε$, $e$, $B$),
  hastye($Γ, x : A$, $ε$, $a$, $C$),
  hastye($Γ, y : B$, $ε$, $b$, $C$),
  tmeqv($Γ$, $ε$, casex(linr($e$), $x$, $a$, $y$, $b$), letx($y$, $e$, $b$), $C$),
)
#let eqv-case-eta = rule(
  label: msc("case-η"),
  hastye($Γ$, $ε$, $e$, $A tysum B$),
  tmeqv($Γ$, $ε$, casex($e$, $x$, linl($x$), $y$, linr($y$)), $e$, $A tysum B$),
)

// --- Iteration (Conway / Elgot axioms) -------------------------------------

// Fixpoint unfolding: one pass of the loop.
#let eqv-iter-beta = rule(
  label: msc("iter-β"),
  hastye($Γ$, $ε$, $a$, $A$),
  hastye($Γ, x : A$, $ε$, $b$, $B tysum A$),
  tmeqv($Γ$, effiter($ε$),
    iterx($a$, $x$, $b$),
    letx($x$, $a$, casex($b$, $y$, $y$, $z$, iterx($z$, $x$, $b$))),
    $B$),
)
// Naturality: a continuation after a loop moves into the loop's exit branch.
#let eqv-iter-nat = rule(
  label: msc("let-iter"),
  hastye($Γ$, $ε$, $a$, $A$),
  hastye($Γ, x : A$, $ε$, $b$, $B tysum A$),
  hastye($Γ, y : B$, $ε$, $c$, $C$),
  tmeqv($Γ$, effiter($ε$),
    letx($y$, iterx($a$, $x$, $b$), $c$),
    iterx($a$, $x$, casex($b$, $y$, linl($c$), $z$, linr($z$))),
    $C$),
)
// Codiagonal: a loop nested on the same parameter collapses to a single loop.
#let eqv-iter-codiag = rule(
  label: msc("codiag"),
  hastye($Γ$, $ε$, $a$, $A$),
  hastye($Γ, x : A$, $ε$, $b$, $(B tysum A) tysum A$),
  tmeqv($Γ$, effiter($ε$),
    iterx($a$, $x$, iterx($x$, $y$, $b$)),
    iterx($a$, $y$, casex($b$, $x$, $x$, $y$, linr($y$))),
    $B$),
)
// Binding: float the loop's initial value out into a let.
#let eqv-iter-bind = rule(
  label: msc("iter-bind"),
  hastye($Γ$, $ε$, $a$, $A$),
  hastye($Γ, x : A$, $ε$, $b$, $B tysum A$),
  tmeqv($Γ$, effiter($ε$),
    iterx($a$, $x$, $b$),
    letx($y$, $a$, iterx($y$, $x$, $b$)),
    $B$),
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

// --- Directed substitution -------------------------------------------------

// The headline directed law. Substitute a (possibly effectful) `a` for `x`,
// provided a's effect ε is a p-mover over the body's effect η (p = + pushes the
// binding inward, a ↠ [a/x]b; p = - is the reverse). The *multiplicity* side
// conditions on x (affine to drop, relevant to duplicate) belong to the
// substructural layer and are omitted here.
#let ref-let-beta = rule(
  label: msc("let-β"),
  hastye($Γ$, $ε$, $a$, $A$),
  hastye($Γ, x : A$, $η$, $b$, $B$),
  rmovep($ε$, $η$, $p$),
  trefp($Γ$, rwsys, letx($x$, $a$, $b$), substx($a$, $x$, $b$), $B$, $p$),
)

// --- Example rewrites: undefined behaviour ---------------------------------

// UB ⌁ is a right-mover over every effect, so it may always be pushed forward;
// these absorption laws seed R with the corresponding peephole rewrites.
#let ref-ub-seq = rule(
  label: msc("ub-seq"),
  hastye($Γ, x : A$, $ε$, $b$, $B$),
  tref($Γ$, rwsys, letx($x$, lub, $b$), lub, $B$),
)
#let ref-ub-inl = rule(
  label: msc("ub-inl"),
  hastye($Γ$, $ε$, $a$, $A tysum B$),
  hastye($Γ, x : A$, $ε$, $c$, $C$),
  tref($Γ$, rwsys, casex($a$, $x$, $c$, $y$, lub), letx($x$, lprojl($a$), $c$), $C$),
)
#let ref-ub-inr = rule(
  label: msc("ub-inr"),
  hastye($Γ$, $ε$, $a$, $A tysum B$),
  hastye($Γ, y : B$, $ε$, $c$, $C$),
  tref($Γ$, rwsys, casex($a$, $x$, lub, $y$, $c$), letx($y$, lprojr($a$), $c$), $C$),
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
#let eqv-binding-rules = (
  eqv-let-eta, eqv-let-op, eqv-let-let, eqv-let-let-pair,
  eqv-let-case, eqv-let-pair-bind, eqv-case-bind,
)
#let eqv-reduction-rules = (
  eqv-let-beta, eqv-unit, eqv-init,
  eqv-pair-beta, eqv-pair-eta,
  eqv-case-betal, eqv-case-betar, eqv-case-eta,
)
#let eqv-iteration-rules = (
  eqv-iter-beta, eqv-iter-nat, eqv-iter-codiag, eqv-iter-bind,
)

#let ref-congruence-rules = (
  ref-base, ref-refl, ref-trans,
  ref-op, ref-let, ref-pair, ref-let-pair,
  ref-inl, ref-inr, ref-case, ref-abort, ref-iter,
)
#let ref-directed-rules = (ref-let-beta,)
#let ref-ub-rules = (ref-ub-seq, ref-ub-inl, ref-ub-inr)

// Lay an array of rules out as a single `rule-set` of proof trees.
#let rules-block(rules) = rule-set(..rules.map(prooftree))
