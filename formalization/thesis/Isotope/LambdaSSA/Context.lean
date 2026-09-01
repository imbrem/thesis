import Isotope.LambdaSSA.Syntax

namespace Isotope.LambdaSSA

/-- Value contexts, with de Bruijn index zero at the list head. -/
abbrev VCtx (τ : Type u) := List τ

/-- Label contexts, with de Bruijn index zero at the list head. -/
abbrev LCtx (τ : Type u) := List τ

/-- Lookup evidence for a de Bruijn index. -/
abbrev At (Γ : List τ) (i : Nat) (A : τ) : Prop := Γ[i]? = some A

/-- A typed renaming from `Γ` into `Δ`. -/
def Ren (Γ Δ : List τ) (ρ : Nat → Nat) : Prop :=
  ∀ ⦃i A⦄, At Γ i A → At Δ (ρ i) A

namespace Ren

theorem id (Γ : List τ) : Ren Γ Γ id := by intro i A h; simpa using h

theorem comp {Γ Δ Θ : List τ} {ρ σ : Nat → Nat} (hρ : Ren Γ Δ ρ) (hσ : Ren Δ Θ σ) :
    Ren Γ Θ (σ ∘ ρ) := by intro i A h; exact hσ (hρ h)

theorem lift {Γ Δ : List τ} {ρ : Nat → Nat} (h : Ren Γ Δ ρ) (A : τ) :
    Ren (A :: Γ) (A :: Δ) (LambdaSSA.lift ρ) := by
  intro i B hi
  cases i with
  | zero => simpa [At, LambdaSSA.lift] using hi
  | succ i => simpa [At, LambdaSSA.lift] using h hi

theorem wk (Γ : List τ) (A : τ) : Ren Γ (A :: Γ) Nat.succ := by
  intro i B h
  simpa [At] using h

end Ren

end Isotope.LambdaSSA
