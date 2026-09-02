import Isotope.LambdaIter.Semantics.Categorical
import Isotope.LambdaIter.Subtyping.Semantics.Effects

/-!
# Effect soundness for coercion-free lambda-iter

The coercion-free denotation is the generic one composed with `HasType.toGeneric`, so effect
soundness transports along that embedding with no further work.
-/

universe v₁ v₂ u₁ u₂ u₃ u₄ u₅

namespace Isotope.LambdaIter.LocallyNameless.Categorical

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.PremonoidalCategory
open Isotope.LambdaIter.Subtyping.Semantics.Categorical
open Isotope.LambdaIter.Subtyping.Semantics.Categorical.EffectModel
open scoped MonoidalCategory

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  {E : Type u₅} [Preorder E] [OrderBot E]
  (J : Functor V C) [StrongElgotFreydCategory J]
  {eff : E → MorphismProperty C} [CategoryTheory.EffectLattice E eff]
  [EffectModel E J eff] [DistributiveEffectModel E J eff]
  {τ : Type u₃} [TypeFormers τ] [Subtyping τ] (M : TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type u₄} [HasTy Φ τ] [HasEff Φ E] [InstructionModel J M Φ]
  [EffectfulInstructionModel E J eff M Φ]
  {iterative : E → Prop} [CategoryTheory.IterativeEffects E eff iterative]

/-- **Effect soundness for coercion-free λ-iter.** -/
theorem denote_mem_eff {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} {e : E}
    (h : HasType Φ Γ β t A)
    (he : Subtyping.LocallyNameless.HasEffect iterative e t) :
    eff e (denote J M h) :=
  Subtyping.Semantics.Categorical.denote_mem_eff J M h.toGeneric he

end Isotope.LambdaIter.LocallyNameless.Categorical
