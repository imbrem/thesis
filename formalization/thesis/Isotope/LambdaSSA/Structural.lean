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

theorem liftN {Γ Δ : VCtx τ} {σ : Nat → Tm Φ} (hσ : Subst.HasType Γ Δ σ)
    (Ξ : List τ) : Subst.HasType (Ξ ++ Γ) (Ξ ++ Δ) (Tm.liftSubstN Ξ.length σ) := by
  induction Ξ with
  | nil => simpa [Tm.liftSubstN] using hσ
  | cons A Ξ ih => simpa [Tm.liftSubstN] using ih.lift A

end Subst.HasType

theorem Subst.HasType.subst0 {Γ : VCtx τ} {a : Tm Φ} {A : τ}
    (ha : Tm.HasType Γ a A) : Subst.HasType (A :: Γ) Γ (Tm.subst0 a) := by
  intro i B hi
  cases i with
  | zero =>
      have hAB : A = B := by simpa [At] using hi
      simpa [hAB, Tm.subst0] using ha
  | succ i => exact .var (by simpa [At, Tm.subst0] using hi)

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

namespace Body

theorem liftN_lift (n : Nat) (ρ : Nat → Nat) :
    LambdaSSA.liftN n (LambdaSSA.lift ρ) =
      LambdaSSA.lift (LambdaSSA.liftN n ρ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [LambdaSSA.liftN, ih]

theorem liftSubstN_liftSubst (n : Nat) (σ : Nat → Tm Φ) :
    Tm.liftSubstN n (Tm.liftSubst σ) =
      Tm.liftSubst (Tm.liftSubstN n σ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Tm.liftSubstN, ih]

theorem HasType.rename {Γ Δ Θ : VCtx τ} {b : Body Φ} {ρ : Nat → Nat}
    (hρ : Ren Γ Δ ρ) (hb : HasType Γ b Θ) :
    ∃ Θ', HasType Δ (b.rename ρ) Θ' ∧ Ren Θ Θ' (LambdaSSA.liftN b.bound ρ) := by
  induction hb generalizing Δ ρ with
  | nil => exact ⟨Δ, .nil, hρ⟩
  | @let₁ Γ a A b Θ ha hb ih =>
      obtain ⟨Θ', hb', hΘ⟩ := ih (hρ.lift A)
      rw [liftN_lift] at hΘ
      exact ⟨Θ', .let₁ (ha.rename hρ) hb', hΘ⟩
  | @let₂ Γ a A B b Θ ha hb ih =>
      obtain ⟨Θ', hb', hΘ⟩ := ih ((hρ.lift A).lift B)
      rw [liftN_lift, liftN_lift] at hΘ
      exact ⟨Θ', .let₂ (ha.rename hρ) hb', hΘ⟩

theorem HasType.subst {Γ Δ Θ : VCtx τ} {b : Body Φ} {σ : Nat → Tm Φ}
    (hσ : Tm.Subst.HasType Γ Δ σ) (hb : HasType Γ b Θ) :
    ∃ Θ', HasType Δ (b.subst σ) Θ' ∧
      Tm.Subst.HasType Θ Θ' (Tm.liftSubstN b.bound σ) := by
  induction hb generalizing Δ σ with
  | nil => exact ⟨Δ, .nil, hσ⟩
  | @let₁ Γ a A b Θ ha hb ih =>
      obtain ⟨Θ', hb', hΘ⟩ := ih (hσ.lift A)
      rw [liftSubstN_liftSubst] at hΘ
      exact ⟨Θ', .let₁ (ha.subst hσ) hb', hΘ⟩
  | @let₂ Γ a A B b Θ ha hb ih =>
      obtain ⟨Θ', hb', hΘ⟩ := ih ((hσ.lift A).lift B)
      rw [liftSubstN_liftSubst, liftSubstN_liftSubst] at hΘ
      exact ⟨Θ', .let₂ (ha.subst hσ) hb', hΘ⟩

end Body

namespace Terminator

theorem HasType.substVars {Γ Δ : VCtx τ} {t : Terminator Φ} {L : LCtx τ}
    {σ : Nat → Tm Φ} (hσ : Tm.Subst.HasType Γ Δ σ) (ht : HasType Γ t L) :
    HasType Δ (t.substVars σ) L := by
  induction ht generalizing Δ σ with
  | br hL ha => exact .br hL (ha.subst hσ)
  | case ha hl hr ihl ihr =>
      exact .case (ha.subst hσ) (ihl (hσ.lift _)) (ihr (hσ.lift _))

end Terminator

namespace Block

theorem HasType.renameVars {Γ Δ : VCtx τ} {b : Block Φ} {L : LCtx τ}
    {ρ : Nat → Nat} (hρ : Ren Γ Δ ρ) (hb : HasType Γ b L) :
    HasType Δ (b.renameVars ρ) L := by
  obtain ⟨Θ, hbody, hterm⟩ := hb
  obtain ⟨Θ', hbody', hΘ⟩ := hbody.rename hρ
  exact ⟨Θ', hbody', hterm.renameVars hΘ⟩

theorem HasType.renameLabels {Γ : VCtx τ} {b : Block Φ} {L K : LCtx τ}
    {ρ : Nat → Nat} (hρ : Ren L K ρ) (hb : HasType Γ b L) :
    HasType Γ (b.renameLabels ρ) K := by
  obtain ⟨Θ, hbody, hterm⟩ := hb
  exact ⟨Θ, hbody, hterm.renameLabels hρ⟩

theorem HasType.substVars {Γ Δ : VCtx τ} {b : Block Φ} {L : LCtx τ}
    {σ : Nat → Tm Φ} (hσ : Tm.Subst.HasType Γ Δ σ) (hb : HasType Γ b L) :
    HasType Δ (b.substVars σ) L := by
  obtain ⟨Θ, hbody, hterm⟩ := hb
  obtain ⟨Θ', hbody', hΘ⟩ := hbody.subst hσ
  exact ⟨Θ', hbody', hterm.substVars hΘ⟩

end Block

namespace Region

theorem HasType.renameVars {Γ Δ : VCtx τ} {r : Region Φ} {L : LCtx τ}
    {ρ : Nat → Nat} (hρ : Ren Γ Δ ρ) (hr : HasType Γ r L) :
    HasType Δ (r.renameVars ρ) L := by
  induction hr generalizing Δ ρ with
  | br hL ha => exact .br hL (ha.rename hρ)
  | case ha hl hr ihl ihr =>
      exact .case (ha.rename hρ) (ihl (hρ.lift _)) (ihr (hρ.lift _))
  | let₁ ha hr ih => exact .let₁ (ha.rename hρ) (ih (hρ.lift _))
  | let₂ ha hr ih => exact .let₂ (ha.rename hρ) (ih ((hρ.lift _).lift _))
  | cfg R he hb ihe ihb =>
      exact .cfg R (ihe hρ) (fun i => ihb i (hρ.lift (R i)))

theorem HasType.renameLabels {Γ : VCtx τ} {r : Region Φ} {L K : LCtx τ}
    {ρ : Nat → Nat} (hρ : Ren L K ρ) (hr : HasType Γ r L) :
    HasType Γ (r.renameLabels ρ) K := by
  induction hr generalizing K ρ with
  | br hL ha => exact .br (hρ hL) ha
  | case ha hl hr ihl ihr => exact .case ha (ihl hρ) (ihr hρ)
  | let₁ ha hr ih => exact .let₁ ha (ih hρ)
  | let₂ ha hr ih => exact .let₂ ha (ih hρ)
  | cfg R he hb ihe ihb =>
      have hρ' := hρ.liftN (List.ofFn R)
      exact .cfg R (ihe (by simpa using hρ')) (fun i => ihb i (by simpa using hρ'))

theorem HasType.substVars {Γ Δ : VCtx τ} {r : Region Φ} {L : LCtx τ}
    {σ : Nat → Tm Φ} (hσ : Tm.Subst.HasType Γ Δ σ) (hr : HasType Γ r L) :
    HasType Δ (r.substVars σ) L := by
  induction hr generalizing Δ σ with
  | br hL ha => exact .br hL (ha.subst hσ)
  | case ha hl hr ihl ihr =>
      exact .case (ha.subst hσ) (ihl (hσ.lift _)) (ihr (hσ.lift _))
  | let₁ ha hr ih => exact .let₁ (ha.subst hσ) (ih (hσ.lift _))
  | let₂ ha hr ih => exact .let₂ (ha.subst hσ) (ih ((hσ.lift _).lift _))
  | cfg R he hb ihe ihb =>
      exact .cfg R (ihe hσ) (fun i => ihb i (hσ.lift (R i)))

/-- A typed label substitution replaces a label of argument type `A` by a
region with one distinguished `A`-typed value variable. -/
def LabelSubst.HasType (Γ : VCtx τ) (L K : LCtx τ) (σ : LabelSubst Φ) : Prop :=
  ∀ ⦃ℓ A⦄, At L ℓ A → Region.HasType (A :: Γ) (σ ℓ) K

namespace LabelSubst.HasType

theorem liftVars {Γ : VCtx τ} {L K : LCtx τ} {σ : LabelSubst Φ}
    (hσ : LabelSubst.HasType Γ L K σ) (B : τ) :
    LabelSubst.HasType (B :: Γ) L K σ.liftVars := by
  intro ℓ A hℓ
  exact (hσ hℓ).renameVars ((Ren.wk Γ B).lift A)

theorem lift {Γ : VCtx τ} {L K : LCtx τ} {σ : LabelSubst Φ}
    (hσ : LabelSubst.HasType Γ L K σ) (B : τ) :
    LabelSubst.HasType Γ (B :: L) (B :: K) σ.lift := by
  intro ℓ A hℓ
  cases ℓ with
  | zero =>
      exact .br (by simpa [At] using hℓ) (.var (by simpa [At] using hℓ))
  | succ ℓ =>
      exact (hσ (by simpa [At] using hℓ)).renameLabels (Ren.wk K B)

theorem liftN {Γ : VCtx τ} {L K : LCtx τ} {σ : LabelSubst Φ}
    (hσ : LabelSubst.HasType Γ L K σ) (Ξ : List τ) :
    LabelSubst.HasType Γ (Ξ ++ L) (Ξ ++ K) (σ.liftN Ξ.length) := by
  induction Ξ with
  | nil => simpa [LabelSubst.liftN] using hσ
  | cons B Ξ ih => simpa [LabelSubst.liftN] using ih.lift B

end LabelSubst.HasType

theorem HasType.substLabels {Γ : VCtx τ} {r : Region Φ} {L K : LCtx τ}
    {σ : LabelSubst Φ} (hσ : LabelSubst.HasType Γ L K σ) (hr : HasType Γ r L) :
    HasType Γ (r.substLabels σ) K := by
  induction hr generalizing K σ with
  | br hL ha => exact (hσ hL).substVars (Tm.Subst.HasType.subst0 ha)
  | case ha hl hr ihl ihr =>
      exact .case ha (ihl (hσ.liftVars _)) (ihr (hσ.liftVars _))
  | let₁ ha hr ih => exact .let₁ ha (ih (hσ.liftVars _))
  | let₂ ha hr ih => exact .let₂ ha (ih ((hσ.liftVars _).liftVars _))
  | cfg R he hb ihe ihb =>
      have hσ' := hσ.liftN (List.ofFn R)
      exact .cfg R (ihe (by simpa using hσ'))
        (fun i => ihb i (by simpa using hσ'.liftVars (R i)))

end Region

end Isotope.LambdaSSA
