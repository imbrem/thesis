import Isotope.LambdaSSA.Context

namespace Isotope.LambdaSSA

variable [LambdaIter.TypeFormers τ] [LambdaIter.HasTy Φ τ]

/-- Exact typing for pure expressions. This corrects the paper's right-case
branch to bind `B`, not `A`. -/
inductive Tm.HasType : VCtx τ → Tm Φ → τ → Prop where
  | var : At Γ i A → HasType Γ (.var i) A
  | op : HasType Γ a (LambdaIter.instrSrc f) → HasType Γ (.op f a) (LambdaIter.instrTrg f)
  | let₁ : HasType Γ a A → HasType (A :: Γ) b B → HasType Γ (.let₁ a b) B
  | pair : HasType Γ a A → HasType Γ b B → HasType Γ (.pair a b) (LambdaIter.tensor A B)
  | unit : HasType Γ .unit LambdaIter.unit
  | let₂ : HasType Γ a (LambdaIter.tensor A B) →
      HasType (B :: A :: Γ) b C → HasType Γ (.let₂ a b) C
  | inl : HasType Γ a A → HasType Γ (.inl a) (LambdaIter.coprod A B)
  | inr : HasType Γ b B → HasType Γ (.inr b) (LambdaIter.coprod A B)
  | case : HasType Γ a (LambdaIter.coprod A B) →
      HasType (A :: Γ) l C → HasType (B :: Γ) r C → HasType Γ (.case a l r) C
  | abort : HasType Γ a LambdaIter.empty → HasType Γ (.abort a) A

/-- Typing for terminators: the branch argument matches the target label. -/
inductive Terminator.HasType : VCtx τ → Terminator Φ → LCtx τ → Prop where
  | br : At L ℓ A → Tm.HasType Γ a A → HasType Γ (.br ℓ a) L
  | case : Tm.HasType Γ a (LambdaIter.coprod A B) →
      HasType (A :: Γ) l L → HasType (B :: Γ) r L → HasType Γ (.case a l r) L

/-- Typing for straight-line block bodies, exposing their final value context. -/
inductive Body.HasType : VCtx τ → Body Φ → VCtx τ → Prop where
  | nil : HasType Γ .nil Γ
  | let₁ : Tm.HasType Γ a A → HasType (A :: Γ) b Δ → HasType Γ (.let₁ a b) Δ
  | let₂ : Tm.HasType Γ a (LambdaIter.tensor A B) →
      HasType (B :: A :: Γ) b Δ → HasType Γ (.let₂ a b) Δ

/-- A block types by threading the context produced by its body into its terminator. -/
def Block.HasType (Γ : VCtx τ) (b : Block Φ) (L : LCtx τ) : Prop :=
  ∃ Δ, Body.HasType Γ b.body Δ ∧ Terminator.HasType Δ b.terminator L

/-- Exact typing skeleton for regions. `cfg` binds all internal labels in the
entry and block bodies and one block parameter in each body. -/
inductive Region.HasType : VCtx τ → Region Φ → LCtx τ → Prop where
  | br : At L ℓ A → Tm.HasType Γ a A → HasType Γ (.br ℓ a) L
  | case : Tm.HasType Γ a (LambdaIter.coprod A B) →
      HasType (A :: Γ) l L → HasType (B :: Γ) r L → HasType Γ (.case a l r) L
  | let₁ : Tm.HasType Γ a A → HasType (A :: Γ) r L → HasType Γ (.let₁ a r) L
  | let₂ : Tm.HasType Γ a (LambdaIter.tensor A B) →
      HasType (B :: A :: Γ) r L → HasType Γ (.let₂ a r) L
  | cfg {entry : Region Φ} {n : Nat} {blocks : Fin n → Region Φ} (R : Fin n → τ) :
      HasType Γ entry (List.ofFn R ++ L) →
      (∀ i, HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) →
      HasType Γ (.cfg entry n blocks) L

end Isotope.LambdaSSA
