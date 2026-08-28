import Isotope.LambdaIter.Named.Typing

/-! # Shadowing-safe structural rules -/

namespace Isotope.LambdaIter.Named

variable {ι τ : Type*} [DecidableEq ι] [TypeFormers τ] [Subtyping τ]
  {S : Signature τ}

theorem HasType.transport {Γ Δ : Ctx ι τ} {a : Tm ι S} {A : τ}
    (hΓ : Ctx.Preserves Γ Δ) (h : HasType S Γ a A) : HasType S Δ a A := by
  induction h generalizing Δ with
  | var h => exact .var (hΓ _ _ h)
  | op hf _ ih => exact .op hf (ih hΓ)
  | let₁ _ _ iha ihb => exact .let₁ (iha hΓ) (ihb (hΓ.cons _ _))
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair (iha hΓ) (ihb hΓ)
  | let₂ _ _ iha ihc => exact .let₂ (iha hΓ) (ihc ((hΓ.cons _ _).cons _ _))
  | inl _ ih => exact .inl (ih hΓ)
  | inr _ ih => exact .inr (ih hΓ)
  | case _ _ _ ihe iha ihb =>
      exact .case (ihe hΓ) (iha (hΓ.cons _ _)) (ihb (hΓ.cons _ _))
  | abort _ ih => exact .abort (ih hΓ)
  | iter _ _ iha ihb => exact .iter (iha hΓ) (ihb (hΓ.cons _ _))
  | sub _ hAB ih => exact .sub (ih hΓ) hAB

/-- Replay a derivation in a context whose visible variable types have been
strengthened to subtypes. -/
theorem HasType.transportWeakens {Γ Δ : Ctx ι τ} {a : Tm ι S} {A : τ}
    (hΓ : Ctx.Weakens Γ Δ) (h : HasType S Γ a A) : HasType S Δ a A := by
  induction h generalizing Δ with
  | var hx =>
      obtain ⟨B, hB, hBA⟩ := hΓ _ _ hx
      exact .sub (.var hB) hBA
  | op hf _ ih => exact .op hf (ih hΓ)
  | let₁ _ _ iha ihb => exact .let₁ (iha hΓ) (ihb (hΓ.cons _ _))
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair (iha hΓ) (ihb hΓ)
  | let₂ _ _ iha ihc => exact .let₂ (iha hΓ) (ihc ((hΓ.cons _ _).cons _ _))
  | inl _ ih => exact .inl (ih hΓ)
  | inr _ ih => exact .inr (ih hΓ)
  | case _ _ _ ihe iha ihb =>
      exact .case (ihe hΓ) (iha (hΓ.cons _ _)) (ihb (hΓ.cons _ _))
  | abort _ ih => exact .abort (ih hΓ)
  | iter _ _ iha ihb => exact .iter (iha hΓ) (ihb (hΓ.cons _ _))
  | sub _ hAB ih => exact .sub (ih hΓ) hAB

theorem HasType.weakenSubtypes {Γ Δ : Ctx ι τ} {a : Tm ι S} {A B : τ}
    (h : HasType S Γ a A) (hΓ : Ctx.Weakens Γ Δ) (hAB : Subty A B) :
    HasType S Δ a B := .sub (h.transportWeakens hΓ) hAB

/-- Anonymous weakening is always safe: it neither shadows nor becomes visible. -/
theorem HasType.weakenAnon {Γ : Ctx ι τ} {a : Tm ι S} {A : τ}
    (h : HasType S Γ a A) (B : τ) :
    HasType S ((none, B) :: Γ) a A :=
  h.transport (Ctx.preserves_anon Γ B)

/-- Named weakening is intentionally exposed only with the precise first-match
preservation premise. In particular it cannot insert a binder that shadows a
free occurrence. -/
theorem HasType.weaken {Γ Δ : Ctx ι τ} {a : Tm ι S} {A : τ}
    (h : HasType S Γ a A) (hΓ : Ctx.Preserves Γ Δ) :
    HasType S Δ a A := h.transport hΓ

/-- Strengthening is the same transport theorem in the erasing direction. -/
theorem HasType.strengthen {Γ : Ctx ι τ} {a : Tm ι S} {A : τ}
    {b : Option ι × τ} (h : HasType S (b :: Γ) a A)
    (hb : Ctx.CanErase Γ b) : HasType S Γ a A := h.transport hb

end Isotope.LambdaIter.Named
