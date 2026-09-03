import Isotope.LambdaSSA.Typing
import Isotope.LambdaIter.Subtyping

/-!
# Proof-relevant subtyping for lambda-SSA

This development deliberately reuses the raw inductive SSA syntax while
keeping subtype derivations in `Type`.  It is parallel to, and does not change,
the proposition-valued exact typing API.
-/

namespace Isotope.LambdaSSA.Subtyping

open Isotope.LambdaIter

variable [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ] [LambdaIter.HasTy Φ τ]

inductive Tm.HasType : VCtx τ → LambdaSSA.Tm Φ → τ → Type _ where
  | var : At Γ i A → HasType Γ (.var i) A
  | op : HasType Γ a (instrSrc f) → HasType Γ (.op f a) (instrTrg f)
  | let₁ : HasType Γ a A → HasType (A :: Γ) b B → HasType Γ (.let₁ a b) B
  | pair : HasType Γ a A → HasType Γ b B → HasType Γ (.pair a b) (tensor A B)
  | unit : HasType Γ .unit unit
  | let₂ : HasType Γ a (tensor A B) →
      HasType (B :: A :: Γ) b C → HasType Γ (.let₂ a b) C
  | inl : HasType Γ a A → HasType Γ (.inl a) (coprod A B)
  | inr : HasType Γ b B → HasType Γ (.inr b) (coprod A B)
  | case : HasType Γ a (coprod A B) →
      HasType (A :: Γ) l C → HasType (B :: Γ) r C → HasType Γ (.case a l r) C
  | abort : HasType Γ a empty → HasType Γ (.abort a) A
  | sub : HasType Γ a A → LambdaIter.Subty A B → HasType Γ a B

inductive Terminator.HasType : VCtx τ → LambdaSSA.Terminator Φ → LCtx τ → Type _ where
  | br : At L ℓ A → Tm.HasType Γ a A → HasType Γ (.br ℓ a) L
  | case : Tm.HasType Γ a (coprod A B) →
      HasType (A :: Γ) l L → HasType (B :: Γ) r L → HasType Γ (.case a l r) L

inductive Body.HasType : VCtx τ → LambdaSSA.Body Φ → VCtx τ → Type _ where
  | nil : HasType Γ .nil Γ
  | let₁ : Tm.HasType Γ a A → HasType (A :: Γ) b Δ → HasType Γ (.let₁ a b) Δ
  | let₂ : Tm.HasType Γ a (tensor A B) →
      HasType (B :: A :: Γ) b Δ → HasType Γ (.let₂ a b) Δ

structure Block.HasType (Γ : VCtx τ) (b : LambdaSSA.Block Φ) (L : LCtx τ) : Type _ where
  Δ : VCtx τ
  body : Body.HasType Γ b.body Δ
  terminator : Terminator.HasType Δ b.terminator L

inductive Region.HasType : VCtx τ → LambdaSSA.Region Φ → LCtx τ → Type _ where
  | br : At L ℓ A → Tm.HasType Γ a A → HasType Γ (.br ℓ a) L
  | case : Tm.HasType Γ a (coprod A B) →
      HasType (A :: Γ) l L → HasType (B :: Γ) r L → HasType Γ (.case a l r) L
  | let₁ : Tm.HasType Γ a A → HasType (A :: Γ) r L → HasType Γ (.let₁ a r) L
  | let₂ : Tm.HasType Γ a (tensor A B) →
      HasType (B :: A :: Γ) r L → HasType Γ (.let₂ a r) L
  | cfg {entry : LambdaSSA.Region Φ} {n : Nat}
      {blocks : Fin n → LambdaSSA.Region Φ} (R : Fin n → τ) :
      HasType Γ entry (List.ofFn R ++ L) →
      (∀ i, HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) →
      HasType Γ (.cfg entry n blocks) L

namespace Exact

/-- Exact SSA typings inject into the proof-relevant system using no coercion.
Because exact typings live in `Prop`, the resulting witness is propositionally
truncated rather than extracted into data. -/
theorem tm {Γ : VCtx τ} {t : LambdaSSA.Tm Φ} {A : τ}
    (h : LambdaSSA.Tm.HasType Γ t A) : Nonempty (Tm.HasType Γ t A) := by
  induction h with
  | var h => exact ⟨.var h⟩
  | op _ ih => exact ih.elim fun h => ⟨.op h⟩
  | let₁ _ _ iha ihb => exact iha.elim fun ha => ihb.elim fun hb => ⟨.let₁ ha hb⟩
  | pair _ _ iha ihb => exact iha.elim fun ha => ihb.elim fun hb => ⟨.pair ha hb⟩
  | unit => exact ⟨.unit⟩
  | let₂ _ _ iha ihb => exact iha.elim fun ha => ihb.elim fun hb => ⟨.let₂ ha hb⟩
  | inl _ ih => exact ih.elim fun h => ⟨.inl h⟩
  | inr _ ih => exact ih.elim fun h => ⟨.inr h⟩
  | case _ _ _ ihe ihl ihr =>
      exact ihe.elim fun he => ihl.elim fun hl => ihr.elim fun hr => ⟨.case he hl hr⟩
  | abort _ ih => exact ih.elim fun h => ⟨.abort h⟩

theorem region {Γ : VCtx τ} {r : LambdaSSA.Region Φ} {L : LCtx τ}
    (h : LambdaSSA.Region.HasType Γ r L) :
    Nonempty (Region.HasType Γ r L) := by
  induction h with
  | br h ha => exact (tm ha).elim fun ha => ⟨.br h ha⟩
  | case ha _ _ ihl ihr =>
      exact (tm ha).elim fun ha => ihl.elim fun hl => ihr.elim fun hr => ⟨.case ha hl hr⟩
  | let₁ ha _ ihr => exact (tm ha).elim fun ha => ihr.elim fun hr => ⟨.let₁ ha hr⟩
  | let₂ ha _ ihr => exact (tm ha).elim fun ha => ihr.elim fun hr => ⟨.let₂ ha hr⟩
  | cfg R _ _ ihe ihb =>
      exact ihe.elim fun he =>
        ⟨.cfg R he (fun i => Classical.choice (ihb i))⟩

end Exact

end Isotope.LambdaSSA.Subtyping
