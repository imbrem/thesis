// Shared notation for the SSA calculus and its judgements.

/// The language name λ_SSA.
#let lssa = $lambda_(sans("SSA"))$

/// An effect annotation placed immediately to the lower-right of a turnstile.
/// Typst's ordinary attachment centers relation subscripts too far underneath;
/// this matches TeX's visual placement for `\vdash_{\epsilon}` more closely.
#let eff-turnstile(effect) = $⊢ #h(-0.08em) #move(dx: 0.03em, dy: 0.16em, $#effect$)$

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
