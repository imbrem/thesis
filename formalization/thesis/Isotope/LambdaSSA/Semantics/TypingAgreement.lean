import Isotope.LambdaSSA.Semantics.Assumptions
import Isotope.LambdaSSA.Typing

/-! # Nondependent inversion for exact SSA typing

The typing judgment lives in `Prop`, so its hidden type parameters must be
exposed through propositions rather than dependent data.  These inversion
lemmas are the syntax-directed interface used by semantic coherence proofs.
-/

namespace Isotope.LambdaSSA.Semantics

variable {τ Φ : Type*} [LambdaIter.TypeFormers τ] [LambdaIter.HasTy Φ τ]

namespace Tm.HasType

theorem inv_var {Γ : VCtx τ} {i : Nat} {A : τ}
    (h : Tm.HasType Γ (Tm.var (Φ := Φ) i) A) : At Γ i A := by
  cases h with
  | var h => exact h

theorem inv_op {Γ : VCtx τ} {f : Φ} {a : Tm Φ} {A : τ}
    (h : Tm.HasType Γ (.op f a) A) :
    A = LambdaIter.instrTrg f ∧
      Tm.HasType Γ a (LambdaIter.instrSrc f) := by
  cases h with
  | op ha => exact ⟨rfl, ha⟩

theorem inv_unit {Γ : VCtx τ} {A : τ}
    (h : Tm.HasType Γ (Tm.unit (Φ := Φ)) A) : A = LambdaIter.unit := by
  cases h
  rfl

theorem inv_abort {Γ : VCtx τ} {a : Tm Φ} {A : τ}
    (h : Tm.HasType Γ (.abort a) A) :
    Tm.HasType Γ a LambdaIter.empty := by
  cases h with
  | abort ha => exact ha

theorem inv_let₁ {Γ : VCtx τ} {a b : Tm Φ} {B : τ}
    (h : Tm.HasType Γ (.let₁ a b) B) :
    ∃ A, Tm.HasType Γ a A ∧ Tm.HasType (A :: Γ) b B := by
  cases h with
  | let₁ ha hb => exact ⟨_, ha, hb⟩

theorem inv_pair {Γ : VCtx τ} {a b : Tm Φ} {T : τ}
    (h : Tm.HasType Γ (.pair a b) T) :
    ∃ A B, T = LambdaIter.tensor A B ∧
      Tm.HasType Γ a A ∧ Tm.HasType Γ b B := by
  cases h with
  | pair ha hb => exact ⟨_, _, rfl, ha, hb⟩

theorem inv_let₂ {Γ : VCtx τ} {a b : Tm Φ} {T : τ}
    (h : Tm.HasType Γ (.let₂ a b) T) :
    ∃ A B, Tm.HasType Γ a (LambdaIter.tensor A B) ∧
      Tm.HasType (B :: A :: Γ) b T := by
  cases h with
  | let₂ ha hb => exact ⟨_, _, ha, hb⟩

theorem inv_inl {Γ : VCtx τ} {a : Tm Φ} {T : τ}
    (h : Tm.HasType Γ (.inl a) T) :
    ∃ A B, T = LambdaIter.coprod A B ∧ Tm.HasType Γ a A := by
  cases h with
  | inl ha => exact ⟨_, _, rfl, ha⟩

theorem inv_inr {Γ : VCtx τ} {b : Tm Φ} {T : τ}
    (h : Tm.HasType Γ (.inr b) T) :
    ∃ A B, T = LambdaIter.coprod A B ∧ Tm.HasType Γ b B := by
  cases h with
  | inr hb => exact ⟨_, _, rfl, hb⟩

theorem inv_case {Γ : VCtx τ} {a l r : Tm Φ} {T : τ}
    (h : Tm.HasType Γ (.case a l r) T) :
    ∃ A B, Tm.HasType Γ a (LambdaIter.coprod A B) ∧
      Tm.HasType (A :: Γ) l T ∧ Tm.HasType (B :: Γ) r T := by
  cases h with
  | case ha hl hr => exact ⟨_, _, ha, hl, hr⟩

end Tm.HasType
end Isotope.LambdaSSA.Semantics
