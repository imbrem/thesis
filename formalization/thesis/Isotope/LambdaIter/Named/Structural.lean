import Isotope.LambdaIter.Named.Typing

/-! # Shadowing-safe structural rules -/

namespace Isotope.LambdaIter.Named

variable {ν τ : Type*} [DecidableEq ν] [TypeFormers τ] [Subtyping τ]
  {S : Signature τ}

/-- The lookup condition under which a shared `Wk Γ Δ` transports typing from
`Δ` to `Γ`. It is intentionally proof-relevant. Not every shared weakening has
this property: `NameEdit.introduce` can make a variable visible only in `Δ`. -/
structure LookupWk {Γ Δ : Ctx ν τ} (w : Ctx.Wk Γ Δ) : Type _ where
  lookup : ∀ x A, Δ.lookup x = some A → Γ.lookup x = some A

/-- Subtyping-aware lookup condition for `SubtypeWk`. -/
structure LookupSubtypeWk {Γ Δ : Ctx ν τ} (w : Ctx.SubtypeWk Γ Δ) : Type _ where
  lookup : ∀ x A, Δ.lookup x = some A →
    Σ B, (Γ.lookup x = some B) ×' Subty B A

namespace LookupWk

def snoc {Γ Δ : Ctx ν τ} {w : Ctx.Wk Γ Δ}
    (h : LookupWk w) (n : Option ν) (A : τ) :
    LookupWk (Ctx.Wk.keep (A := A) w (.keep n)) := ⟨by
  intro x B hx
  cases n with
  | none => exact h.lookup x B hx
  | some y =>
    by_cases e : x = y
    · subst e; simpa [Ctx.lookup] using hx
    · simpa [Ctx.lookup, e] using h.lookup x B (by simpa [Ctx.lookup, e] using hx)⟩

end LookupWk

namespace LookupSubtypeWk

def snoc {Γ Δ : Ctx ν τ} {w : Ctx.SubtypeWk Γ Δ}
    (h : LookupSubtypeWk w) (n : Option ν) (A : τ) :
    LookupSubtypeWk (Ctx.SubtypeWk.keep (A := A) (B := A) w (.keep n) (Subty.refl A)) := ⟨by
  intro x B hx
  cases n with
  | none => exact h.lookup x B hx
  | some y =>
    by_cases e : x = y
    · subst e
      have hAB : A = B := by simpa [Ctx.lookup] using hx
      subst B
      exact ⟨A, by simp [Ctx.lookup], Subty.refl A⟩
    · obtain ⟨C, hC, hCB⟩ := h.lookup x B (by simpa [Ctx.lookup, e] using hx)
      exact ⟨C, by simpa [Ctx.lookup, e] using hC, hCB⟩⟩

end LookupSubtypeWk

theorem HasType.wk {Γ Δ : Ctx ν τ} {a : Tm ν S} {A : τ}
    (w : Ctx.Wk Γ Δ) (hw : LookupWk w) (h : HasType S Δ a A) :
    HasType S Γ a A := by
  induction h generalizing Γ with
  | var hx => exact .var (hw.lookup _ _ hx)
  | op hf _ ih => exact .op hf (ih w hw)
  | let₁ _ _ iha ihb => exact .let₁ (iha w hw) (ihb _ (hw.snoc _ _))
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair (iha w hw) (ihb w hw)
  | let₂ _ _ iha ihc => exact .let₂ (iha w hw) (ihc _ ((hw.snoc _ _).snoc _ _))
  | inl _ ih => exact .inl (ih w hw)
  | inr _ ih => exact .inr (ih w hw)
  | case _ _ _ ihe iha ihb =>
      exact .case (ihe w hw) (iha _ (hw.snoc _ _)) (ihb _ (hw.snoc _ _))
  | abort _ ih => exact .abort (ih w hw)
  | iter _ _ iha ihb => exact .iter (iha w hw) (ihb _ (hw.snoc _ _))
  | sub _ hAB ih => exact .sub (ih w hw) hAB

theorem HasType.subtypeWk {Γ Δ : Ctx ν τ} {a : Tm ν S} {A : τ}
    (w : Ctx.SubtypeWk Γ Δ) (hw : LookupSubtypeWk w) (h : HasType S Δ a A) :
    HasType S Γ a A := by
  induction h generalizing Γ with
  | var hx =>
      obtain ⟨B, hB, hBA⟩ := hw.lookup _ _ hx
      exact .sub (.var hB) hBA
  | op hf _ ih => exact .op hf (ih w hw)
  | let₁ _ _ iha ihb => exact .let₁ (iha w hw) (ihb _ (hw.snoc _ _))
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair (iha w hw) (ihb w hw)
  | let₂ _ _ iha ihc => exact .let₂ (iha w hw) (ihc _ ((hw.snoc _ _).snoc _ _))
  | inl _ ih => exact .inl (ih w hw)
  | inr _ ih => exact .inr (ih w hw)
  | case _ _ _ ihe iha ihb =>
      exact .case (ihe w hw) (iha _ (hw.snoc _ _)) (ihb _ (hw.snoc _ _))
  | abort _ ih => exact .abort (ih w hw)
  | iter _ _ iha ihb => exact .iter (iha w hw) (ihb _ (hw.snoc _ _))
  | sub _ hAB ih => exact .sub (ih w hw) hAB

/-- Proposition-valued corollary, when derivation identity is irrelevant. -/
theorem HasType.wk_nonempty {Γ Δ : Ctx ν τ} {a : Tm ν S} {A : τ}
    (h : HasType S Δ a A) (p : Nonempty (Σ w : Ctx.Wk Γ Δ, LookupWk w)) :
    HasType S Γ a A := p.elim fun ⟨w, hw⟩ => h.wk w hw

end Isotope.LambdaIter.Named
