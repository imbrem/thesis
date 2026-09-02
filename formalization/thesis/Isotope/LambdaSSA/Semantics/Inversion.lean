import Isotope.LambdaSSA.Semantics.Term
import Mathlib.Tactic.CasesM

/-! # Inversion for the free SSA type algebra

For the free `LambdaIter.Ty` instance, constructor no-confusion supplies the
dependent transports needed to show that the term denotation graph is
single-valued.  The corresponding abstract assumption is
`Semantics.InjectiveTypeFormers`.
-/

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Isotope.LambdaIter.Subtyping.Semantics.Categorical

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : Functor V C) [DistributiveFreydCategory J]
  {α : Type u₃} (M : TypeModel (LambdaIter.Ty α) V)
  {Φ : Type u₄} [LambdaIter.HasTy Φ (LambdaIter.Ty α)]
  [InstructionModel J M Φ]

theorem Denotes.proof_irrel
    {Γ : VCtx (LambdaIter.Ty α)} {t : Tm Φ} {A : LambdaIter.Ty α}
    {h h' : Tm.HasType Γ t A}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
    (d : Denotes J M h f) : Denotes J M h' f := by
  rw [Subsingleton.elim h' h]
  exact d

end Isotope.LambdaSSA.Semantics.Categorical
