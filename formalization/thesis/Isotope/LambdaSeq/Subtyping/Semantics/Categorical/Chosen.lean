import Isotope.LambdaSeq.Categorical

/-! # Lambda-iter-induced categorical semantics of lambda-seq -/

namespace Isotope.LambdaSeq.Subtyping.Semantics.Categorical.Chosen

open CategoryTheory CategoryTheory.Limits
open Isotope.LambdaIter.Subtyping.Semantics.Categorical

universe v₁ v₂ u₁ u₂ u₃ u₄

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
  (M : TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type*} [LambdaIter.HasTy Φ τ] [InstructionModel J M Φ]

noncomputable def denote {Γ : LambdaIter.Ctx ν τ} {n : Nat}
    {β : LambdaSeq.LocallyNameless.BoundCtx τ n}
    {t : LambdaSeq.LocallyNameless.Tm ν Φ n} {A : τ}
    (h : LambdaSeq.Subtyping.LocallyNameless.HasType Φ Γ β t A) :=
  Isotope.LambdaIter.Subtyping.Semantics.Categorical.denote J M h.embedIter

theorem denote_embedIter {Γ : LambdaIter.Ctx ν τ} {n : Nat}
    {β : LambdaSeq.LocallyNameless.BoundCtx τ n}
    {t : LambdaSeq.LocallyNameless.Tm ν Φ n} {A : τ}
    (h : LambdaSeq.Subtyping.LocallyNameless.HasType Φ Γ β t A) :
    Isotope.LambdaIter.Subtyping.Semantics.Categorical.denote J M h.embedIter =
      denote J M h := rfl

end Isotope.LambdaSeq.Subtyping.Semantics.Categorical.Chosen
