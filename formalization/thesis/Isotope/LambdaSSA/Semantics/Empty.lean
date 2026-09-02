import Isotope.LambdaSSA.Semantics.Model

/-! # Strictness of the interpreted empty type -/

universe v₁ v₂ u₁ u₂ u₃

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
  {τ : Type u₃} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
  (M : TypeModel τ V)

/-- A distributive Freyd functor carries the model's initial empty-type
object to an initial computation object. -/
noncomputable def computationEmptyIsInitial :
    IsInitial (J.obj (M.obj (LambdaIter.empty : τ))) :=
  M.emptyIsInitial.isInitialObj J

/-- Once an empty-typed computation has run, its continuation is irrelevant.
This is the categorical left-zero law used by polymorphic `abort`. -/
theorem empty_continuation_unique {R X : V}
    (z : J.obj R ⟶ J.obj (M.obj (LambdaIter.empty : τ)))
    (f g : J.obj (M.obj (LambdaIter.empty : τ)) ⟶ J.obj X) :
    z ≫ f = z ≫ g := by
  congr 1
  exact (computationEmptyIsInitial J M).hom_ext f g

end Isotope.LambdaSSA.Semantics.Categorical
