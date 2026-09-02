import Isotope.LambdaSSA.Typing
import Isotope.LambdaIter.Subtyping.Semantics.Categorical

/-! # Categorical models of lambda-SSA value contexts

This is the term-level part of the denotational semantics.  SSA value contexts
are newest-first lists, so their categorical interpretation places the head in
the right tensor factor.  The model of types and instructions is shared with
lambda-iter.
-/

universe v u₁ u₃

namespace Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped MonoidalCategory
open Isotope.LambdaIter.Subtyping.Semantics.Categorical

variable {V : Type u₁} [Category.{v} V]
  [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {τ : Type u₃} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]

/-- Interpretation of a newest-first SSA value context.  The newest value is
the right tensor factor, matching the context convention of lambda-iter. -/
def ctxObj (M : TypeModel τ V) : VCtx τ → V
  | [] => 𝟙_ V
  | A :: Γ => ctxObj M Γ ⊗ M.obj A

/-- A typed de Bruijn lookup interpreted as a Cartesian projection. -/
noncomputable def lookup (M : TypeModel τ V) : {Γ : VCtx τ} →
    (i : Nat) → {A : τ} → At Γ i A → (ctxObj M Γ ⟶ M.obj A)
  | [], _, _, h => by simp [At] at h
  | _ :: _, 0, _, h => by
      simp [At] at h
      subst_vars
      exact CartesianMonoidalCategory.snd _ _
  | _ :: _, i + 1, _, h =>
      CartesianMonoidalCategory.fst _ _ ≫ lookup M i h

@[simp]
theorem lookup_zero (M : TypeModel τ V) (Γ : VCtx τ) (A : τ) :
    lookup M 0 (Γ := A :: Γ) (A := A) (by simp [At]) =
      CartesianMonoidalCategory.snd (ctxObj M Γ) (M.obj A) := rfl

@[simp]
theorem lookup_succ (M : TypeModel τ V) {Γ : VCtx τ} {A B : τ}
    (i : Nat) (h : At Γ i A) :
    lookup M (i + 1) (Γ := B :: Γ) h =
      CartesianMonoidalCategory.fst (ctxObj M Γ) (M.obj B) ≫ lookup M i h := rfl

/-- Reassociate an environment extended by a pair into the two newest SSA
slots.  Since contexts are newest-first, `B` is the head after destructuring. -/
def ctxPairIso (M : TypeModel τ V) (Γ : VCtx τ) (A B : τ) :
    ctxObj M Γ ⊗ (M.obj A ⊗ M.obj B) ≅ ctxObj M (B :: A :: Γ) :=
  (α_ (ctxObj M Γ) (M.obj A) (M.obj B)).symm

end Isotope.LambdaSSA.Semantics.Categorical
