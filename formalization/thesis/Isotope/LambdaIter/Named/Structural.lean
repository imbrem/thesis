import Isotope.LambdaIter.Named.Typing

/-! # Shadowing-safe structural rules -/

namespace Isotope.LambdaIter.Named

variable {ν τ Φ : Type*} [DecidableEq ν] [TypeFormers τ] [Subtyping τ]
  [HasTy Φ τ]

/-- The lookup condition under which a shared `Wk Γ Δ` transports typing from
`Δ` to `Γ`. It is intentionally proof-relevant. Not every shared weakening has
this property: `NameEdit.introduce` can make a variable visible only in `Δ`. -/
structure LookupStrictWk {Γ Δ : Ctx ν τ} (w : Ctx.StrictWk Γ Δ) : Type _ where
  lookup : ∀ x A, Δ.lookup x = some A → Γ.lookup x = some A

/-- Subtyping-aware lookup condition for ordinary shared `Wk`. -/
structure LookupWk {Γ Δ : Ctx ν τ} (w : Ctx.Wk Γ Δ) : Type _ where
  lookup : ∀ x A, Δ.lookup x = some A →
    Σ B, (Γ.lookup x = some B) ×' Subty B A

namespace LookupStrictWk

def snoc {Γ Δ : Ctx ν τ} {w : Ctx.StrictWk Γ Δ}
    (h : LookupStrictWk w) (n : Option ν) (A : τ) :
    LookupStrictWk (Ctx.StrictWk.keep (A := A) w (.keep n)) := ⟨by
  intro x B hx
  cases n with
  | none => exact h.lookup x B hx
  | some y =>
    by_cases e : x = y
    · subst e; simpa [Ctx.lookup] using hx
    · simpa [Ctx.lookup, e] using h.lookup x B (by simpa [Ctx.lookup, e] using hx)⟩

end LookupStrictWk

namespace LookupWk

def snoc {Γ Δ : Ctx ν τ} {w : Ctx.Wk Γ Δ}
    (h : LookupWk w) (n : Option ν) (A : τ) :
    LookupWk (Ctx.Wk.keep (A := A) (B := A) w (.keep n) (Subty.refl A)) := ⟨by
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

end LookupWk

omit [TypeFormers τ] [Subtyping τ] in
theorem lookup_snoc_eq {Γ Δ : Ctx ν τ}
    (heq : ∀ x, Γ.lookup x = Δ.lookup x) (n : Option ν) (A : τ) :
    ∀ x, (Ctx.snoc Γ n A).lookup x = (Ctx.snoc Δ n A).lookup x := by
  intro x
  cases n with
  | none => exact heq x
  | some y => by_cases h : x = y <;> simp [Ctx.lookup, h, heq x]

theorem HasType.strictWk {Γ Δ : Ctx ν τ} {a : Tm ν Φ} {A : τ}
    (w : Ctx.StrictWk Γ Δ) (hw : LookupStrictWk w) (h : HasType Δ a A) :
    HasType Γ a A := by
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

theorem HasType.wk {Γ Δ : Ctx ν τ} {a : Tm ν Φ} {A : τ}
    (w : Ctx.Wk Γ Δ) (hw : LookupWk w) (h : HasType Δ a A) :
    HasType Γ a A := by
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
theorem HasType.strictWk_nonempty {Γ Δ : Ctx ν τ} {a : Tm ν Φ} {A : τ}
    (h : HasType Δ a A) (p : Nonempty (Σ w : Ctx.StrictWk Γ Δ, LookupStrictWk w)) :
    HasType Γ a A := p.elim fun ⟨w, hw⟩ => h.strictWk w hw

/-- Transport across an exact equality of visible lookups. This is the core
fact used for checked shadow-only context edits. -/
theorem HasType.lookupEq {Γ Δ : Ctx ν τ} {a : Tm ν Φ} {A : τ}
    (h : HasType Γ a A) (heq : ∀ x, Γ.lookup x = Δ.lookup x) :
    HasType Δ a A := by
  induction h generalizing Δ with
  | var hx => exact .var (heq _ ▸ hx)
  | op hf _ ih => exact .op hf (ih heq)
  | let₁ _ _ iha ihb =>
      exact .let₁ (iha heq) (ihb (lookup_snoc_eq heq _ _))
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair (iha heq) (ihb heq)
  | let₂ _ _ iha ihb =>
      exact .let₂ (iha heq)
        (ihb (lookup_snoc_eq (lookup_snoc_eq heq _ _) _ _))
  | inl _ ih => exact .inl (ih heq)
  | inr _ ih => exact .inr (ih heq)
  | case _ _ _ ihe iha ihb =>
      exact .case (ihe heq)
        (iha (lookup_snoc_eq heq _ _))
        (ihb (lookup_snoc_eq heq _ _))
  | abort _ ih => exact .abort (ih heq)
  | iter _ _ iha ihb =>
      exact .iter (iha heq) (ihb (lookup_snoc_eq heq _ _))
  | sub _ hAB ih => exact .sub (ih heq) hAB

theorem HasType.shadowEdit {Γ Δ : Ctx ν τ} {a : Tm ν Φ} {A : τ}
    (d : Ctx.ShadowEdit Γ Δ) (h : HasType Γ a A) : HasType Δ a A :=
  h.lookupEq (d.lookup_eq)

end Isotope.LambdaIter.Named
