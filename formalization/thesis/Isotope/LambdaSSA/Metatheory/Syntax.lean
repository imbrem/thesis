import Isotope.LambdaSSA.Structural

/-! # Raw substitution algebra for lambda-SSA -/

namespace Isotope.LambdaSSA

namespace Tm

@[simp] theorem lift_comp (ρ σ : Nat → Nat) :
    LambdaSSA.lift (ρ ∘ σ) = LambdaSSA.lift ρ ∘ LambdaSSA.lift σ := by
  funext i
  cases i <;> rfl

@[simp] theorem liftN_comp (n : Nat) (ρ σ : Nat → Nat) :
    LambdaSSA.liftN n (ρ ∘ σ) = LambdaSSA.liftN n ρ ∘ LambdaSSA.liftN n σ := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [LambdaSSA.liftN, ih, lift_comp]

@[simp] theorem rename_comp (a : Tm Φ) (ρ σ : Nat → Nat) :
    (a.rename σ).rename ρ = a.rename (ρ ∘ σ) := by
  induction a generalizing ρ σ <;>
    simp [rename, lift_comp, liftN_comp, *]

@[simp] theorem liftSubst_id :
    liftSubst (fun i => .var i : Nat → Tm Φ) = fun i => .var i := by
  funext i
  cases i <;> rfl

@[simp] theorem liftSubstN_id (n : Nat) :
    liftSubstN n (fun i => .var i : Nat → Tm Φ) = fun i => .var i := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [liftSubstN, ih, liftSubst_id]

@[simp] theorem subst_id (a : Tm Φ) :
    a.subst (fun i => .var i) = a := by
  induction a <;> simp [subst, liftSubst_id, liftSubstN_id, *]

theorem liftSubst_renaming (ρ : Nat → Nat) :
    liftSubst (fun i => .var (ρ i) : Nat → Tm Φ) =
      fun i => .var (LambdaSSA.lift ρ i) := by
  funext i
  cases i <;> rfl

theorem liftSubstN_renaming (n : Nat) (ρ : Nat → Nat) :
    liftSubstN n (fun i => .var (ρ i) : Nat → Tm Φ) =
      fun i => .var (LambdaSSA.liftN n ρ i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [liftSubstN, ih, liftSubst_renaming]
      rfl

theorem rename_eq_subst (a : Tm Φ) (ρ : Nat → Nat) :
    a.rename ρ = a.subst (fun i => .var (ρ i)) := by
  induction a generalizing ρ <;>
    simp [rename, subst, liftSubst_renaming, liftSubstN_renaming, *]

theorem liftSubst_map_rename (σ : Nat → Tm Φ) (ρ : Nat → Nat) :
    liftSubst (fun i => (σ i).rename ρ) =
      fun i => (liftSubst σ i).rename (LambdaSSA.lift ρ) := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
      simp only [liftSubst, rename_comp]
      apply congrArg (fun f => (σ i).rename f)
      funext j
      cases j <;> rfl

theorem liftSubstN_map_rename (n : Nat) (σ : Nat → Tm Φ) (ρ : Nat → Nat) :
    liftSubstN n (fun i => (σ i).rename ρ) =
      fun i => (liftSubstN n σ i).rename (LambdaSSA.liftN n ρ) := by
  induction n generalizing σ ρ with
  | zero => rfl
  | succ n ih =>
      rw [liftSubstN, ih, liftSubst_map_rename]
      rfl

theorem subst_rename (a : Tm Φ) (σ : Nat → Tm Φ) (ρ : Nat → Nat) :
    (a.subst σ).rename ρ = a.subst (fun i => (σ i).rename ρ) := by
  induction a generalizing σ ρ <;>
    simp [subst, rename, liftSubst_map_rename, liftSubstN_map_rename, *]

end Tm

end Isotope.LambdaSSA
