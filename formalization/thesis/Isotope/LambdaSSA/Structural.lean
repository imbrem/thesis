import Isotope.LambdaSSA.Typing

namespace Isotope.LambdaSSA

variable [LambdaIter.TypeFormers τ] [LambdaIter.HasTy Φ τ]

namespace Tm

@[simp] theorem lift_id : LambdaSSA.lift id = id := by funext i; cases i <;> rfl

@[simp] theorem liftN_id (n : Nat) : LambdaSSA.liftN n id = id := by
  induction n with
  | zero => rfl
  | succ n ih => simp [LambdaSSA.liftN, ih]

@[simp] theorem rename_id (a : Tm Φ) : a.rename id = a := by
  induction a <;> simp [rename, lift_id, liftN_id, *]

/-- The first proved structural theorem of the port: typing is stable under
any type-preserving renaming. -/
theorem HasType.rename {Γ Δ : VCtx τ} {a : Tm Φ} {A : τ} {ρ : Nat → Nat}
    (hρ : Ren Γ Δ ρ) (ha : HasType Γ a A) : HasType Δ (a.rename ρ) A := by
  induction ha generalizing Δ ρ with
  | var h => exact .var (hρ h)
  | op ha ih => exact .op (ih hρ)
  | let₁ ha hb iha ihb => exact .let₁ (iha hρ) (ihb (hρ.lift _))
  | pair ha hb iha ihb => exact .pair (iha hρ) (ihb hρ)
  | unit => exact .unit
  | let₂ ha hb iha ihb =>
      exact .let₂ (iha hρ) (ihb ((hρ.lift _).lift _))
  | inl ha ih => exact .inl (ih hρ)
  | inr hb ih => exact .inr (ih hρ)
  | case ha hl hr iha ihl ihr =>
      exact .case (iha hρ) (ihl (hρ.lift _)) (ihr (hρ.lift _))
  | abort ha ih => exact .abort (ih hρ)

theorem HasType.weaken {Γ : VCtx τ} {a : Tm Φ} {A : τ} (B : τ)
    (ha : HasType Γ a A) : HasType (B :: Γ) (a.rename Nat.succ) A :=
  ha.rename (Ren.wk Γ B)

/-- Typing criterion for simultaneous substitutions. -/
def Subst.HasType (Γ Δ : VCtx τ) (σ : Nat → Tm Φ) : Prop :=
  ∀ ⦃i A⦄, At Γ i A → Tm.HasType Δ (σ i) A

namespace Subst.HasType

theorem lift {Γ Δ : VCtx τ} {σ : Nat → Tm Φ} (hσ : Subst.HasType Γ Δ σ) (A : τ) :
    Subst.HasType (A :: Γ) (A :: Δ) (Tm.liftSubst σ) := by
  intro i B hi
  cases i with
  | zero => exact .var (by simpa [At] using hi)
  | succ i =>
      exact (hσ (by simpa [At] using hi)).weaken A

end Subst.HasType

/-- The first substitution theorem; it is stated for simultaneous
substitutions so the single-variable theorem is a direct specialization. -/
theorem HasType.subst {Γ Δ : VCtx τ} {a : Tm Φ} {A : τ} {σ : Nat → Tm Φ}
    (hσ : Subst.HasType Γ Δ σ) (ha : HasType Γ a A) : HasType Δ (a.subst σ) A := by
  induction ha generalizing Δ σ with
  | var h => exact hσ h
  | op ha ih => exact .op (ih hσ)
  | let₁ ha hb iha ihb => exact .let₁ (iha hσ) (ihb (hσ.lift _))
  | pair ha hb iha ihb => exact .pair (iha hσ) (ihb hσ)
  | unit => exact .unit
  | let₂ ha hb iha ihb => exact .let₂ (iha hσ) (ihb ((hσ.lift _).lift _))
  | inl ha ih => exact .inl (ih hσ)
  | inr hb ih => exact .inr (ih hσ)
  | case ha hl hr iha ihl ihr =>
      exact .case (iha hσ) (ihl (hσ.lift _)) (ihr (hσ.lift _))
  | abort ha ih => exact .abort (ih hσ)

end Tm

namespace Terminator

theorem HasType.renameVars {Γ Δ : VCtx τ} {t : Terminator Φ} {L : LCtx τ}
    {ρ : Nat → Nat} (hρ : Ren Γ Δ ρ) (ht : HasType Γ t L) :
    HasType Δ (t.renameVars ρ) L := by
  induction ht generalizing Δ ρ with
  | br hL ha => exact .br hL (ha.rename hρ)
  | case ha hl hr ihl ihr =>
      exact .case (ha.rename hρ) (ihl (hρ.lift _)) (ihr (hρ.lift _))

theorem HasType.renameLabels {Γ : VCtx τ} {t : Terminator Φ} {L K : LCtx τ}
    {ρ : Nat → Nat} (hρ : Ren L K ρ) (ht : HasType Γ t L) :
    HasType Γ (t.renameLabels ρ) K := by
  induction ht with
  | br hL ha => exact .br (hρ hL) ha
  | case ha hl hr ihl ihr => exact .case ha (ihl hρ) (ihr hρ)

end Terminator

end Isotope.LambdaSSA
