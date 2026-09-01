// Shared notation for the SSA calculus and its judgements.

#import "/lib/todos.typ": old-syntax

/// The language name λ_SSA.
#let lssa = $lambda_(sans("SSA"))$

/// An effect annotation placed immediately to the lower-right of a turnstile.
/// Typst's ordinary attachment centers relation subscripts too far underneath;
/// this matches TeX's visual placement for `\vdash_{\epsilon}` more closely.
#let eff-turnstile(effect) = $⊢ #h(-0.08em) #move(dx: 0.03em, dy: 0.16em, $#effect$)$

/// Refinement-paper spelling of the current effectful turnstile. This alias is
/// intentionally family-specific: it lets the refinement imports migrate
/// independently of the older no-quantity SSA development.
#let refinement-eff-turnstile(effect) = {
  [#metadata((family: "refinement-effect-turnstile", state: "current")) <notation-migration>]
  eff-turnstile(effect)
}

/// Exact legacy attachment retained for unmigrated refinement displays.
/// Calling it emits migration metadata, so `make status` measures remaining
/// uses without changing the source judgement's mathematical content.
#let legacy-refinement-eff-turnstile(effect) = {
  [#metadata((family: "refinement-effect-turnstile", state: "legacy")) <notation-migration>]
  old-syntax(
    [],
    family: "refinement-effect-turnstile",
    note: "Centered Typst relation subscript; migrate to refinement-eff-turnstile.",
  )
  $attach(⊢, b: #effect)$
}

/// Effectful expression typing: Γ ⊢_ε a : A.
#let eff-typing(ctx, effect, term, ty) = $#ctx #eff-turnstile(effect) #term : #ty$

/// Region typing: Γ ⊢ r ▹ L.
#let region-typing(ctx, region, labels) = $#ctx ⊢ #region ▹ #labels$

/// A branch to label ℓ with argument a.
#let ssa-branch(label, arg) = $sans("br") med #label med #arg$

/// A mutually recursive region block.
#let ssa-where(region, branches) = $#region med sans("where") med #branches$

/// A labelled region clause ℓ(x) : { r }.
#let ssa-clause(label, binder, body) = $#label (#binder) : {#body}$
