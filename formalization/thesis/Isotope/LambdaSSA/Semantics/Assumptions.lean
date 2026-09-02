import Isotope.LambdaIter.Ty

/-! # Optional syntax-directedness assumptions for SSA semantics -/

namespace Isotope.LambdaSSA.Semantics

/-- The type constructors whose arguments are hidden by an extrinsic typing
derivation are injective.  This is deliberately optional: refinement models
need not collapse to a free type algebra. -/
class InjectiveTypeFormers (τ : Type*) [LambdaIter.TypeFormers τ] : Prop where
  tensor {A B A' B' : τ} :
    LambdaIter.tensor A B = LambdaIter.tensor A' B' → A = A' ∧ B = B'
  coprod {A B A' B' : τ} :
    LambdaIter.coprod A B = LambdaIter.coprod A' B' → A = A' ∧ B = B'

@[simp] theorem tensor_eq_iff [LambdaIter.TypeFormers τ]
    [InjectiveTypeFormers τ] {A B A' B' : τ} :
    LambdaIter.tensor A B = LambdaIter.tensor A' B' ↔ A = A' ∧ B = B' :=
  ⟨InjectiveTypeFormers.tensor, fun ⟨rfl, rfl⟩ => rfl⟩

@[simp] theorem coprod_eq_iff [LambdaIter.TypeFormers τ]
    [InjectiveTypeFormers τ] {A B A' B' : τ} :
    LambdaIter.coprod A B = LambdaIter.coprod A' B' ↔ A = A' ∧ B = B' :=
  ⟨InjectiveTypeFormers.coprod, fun ⟨rfl, rfl⟩ => rfl⟩

instance : InjectiveTypeFormers (LambdaIter.Ty α) where
  tensor h := by cases h; exact ⟨rfl, rfl⟩
  coprod h := by cases h; exact ⟨rfl, rfl⟩

end Isotope.LambdaSSA.Semantics
