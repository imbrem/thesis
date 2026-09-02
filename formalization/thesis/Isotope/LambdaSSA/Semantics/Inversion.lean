import Isotope.LambdaSSA.Semantics.Term
import Isotope.LambdaSSA.Semantics.Empty
import Mathlib.Tactic.CasesM

/-! # Coherence and inversion for SSA term denotations -/

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Isotope.LambdaSSA.Semantics.Categorical

set_option autoImplicit true
set_option relaxedAutoImplicit true

open CategoryTheory CategoryTheory.Limits
open Isotope.LambdaIter.Subtyping.Semantics.Categorical

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : Functor V C) [DistributiveFreydCategory J]
  {τ : Type u₃} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
  (M : TypeModel τ V)
  {Φ : Type u₄} [LambdaIter.HasTy Φ τ]
  [InstructionModel J M Φ]

theorem Denotes.proof_irrel
    {Γ : VCtx τ} {t : Tm Φ} {A : τ}
    {h h' : Tm.HasType Γ t A}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
    (d : Denotes J M h f) : Denotes J M h' f := by
  rw [Subsingleton.elim h' h]
  exact d

/-- Optional coherence of the relational denotation.  As for lambda-iter,
this is not automatic for arbitrary extrinsic typing derivations. -/
class TypingCoherent : Prop where
  denotes_eq {Γ : VCtx τ} {t : Tm Φ} {A : τ}
      {h : Tm.HasType Γ t A}
      {f g : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)} :
      Denotes J M h f → Denotes J M h g → f = g

theorem denote_eq [TypingCoherent (Φ := Φ) J M]
    {Γ : VCtx τ} {t : Tm Φ} {A : τ} {h : Tm.HasType Γ t A}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
    (hf : Denotes J M h f) : denote J M h = f :=
  TypingCoherent.denotes_eq (denote_spec J M h) hf

/-- The result type hidden by `abort` cannot introduce semantic ambiguity:
all continuations from the interpreted empty object agree after the empty
computation. -/
theorem abort_continuation_eq {Γ : VCtx τ} {A B : τ} {X : V}
    (f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj (LambdaIter.empty : τ)))
    (kA : J.obj (M.obj A) ⟶ J.obj X)
    (kB : J.obj (M.obj B) ⟶ J.obj X) :
    abort J M (A := A) f ≫ kA = abort J M (A := B) f ≫ kB := by
  unfold abort
  simp only [Category.assoc]
  apply empty_continuation_unique J M

end Isotope.LambdaSSA.Semantics.Categorical
