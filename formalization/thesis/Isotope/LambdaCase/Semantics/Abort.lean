import Isotope.LambdaCase.Semantics.Categorical

/-! # Uniqueness of categorical empty elimination -/

universe v₁ v₂ u₁ u₂ u₃

namespace Isotope.LambdaCase.Semantics.Categorical

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
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

/-- The interpreted empty type remains initial after applying the Freyd
functor.  This uses preservation of initial objects by `J`; no strictness law
for tensoring with empty is required. -/
noncomputable def computationEmptyIsInitial :
    IsInitial (J.obj (M.obj (LambdaIter.empty : τ))) :=
  M.emptyIsInitial.isInitialObj J

/-- The arrow used by categorical `abort` is the unique computation arrow
out of the interpreted empty type. -/
theorem map_empty_to_eq_unique (A : τ) :
    J.map (M.emptyIsInitial.to (M.obj A)) =
      (computationEmptyIsInitial J M).to (J.obj (M.obj A)) := by
  exact (computationEmptyIsInitial J M).hom_ext _ _

/-- All continuations from an empty-typed computation are equal. -/
theorem empty_continuation_unique {R X : V}
    (z : J.obj R ⟶ J.obj (M.obj (LambdaIter.empty : τ)))
    (f g : J.obj (M.obj (LambdaIter.empty : τ)) ⟶ J.obj X) :
    z ≫ f = z ≫ g := by
  congr 1
  exact (computationEmptyIsInitial J M).hom_ext f g

/-- `abort` can equivalently be written using the unique computation arrow. -/
theorem abort_eq_unique {R : V} {A : τ}
    (z : J.obj R ⟶ J.obj (M.obj (LambdaIter.empty : τ))) :
    abort J M (A := A) z =
      z ≫ (computationEmptyIsInitial J M).to (J.obj (M.obj A)) := by
  unfold abort
  rw [map_empty_to_eq_unique]
  rfl

end Isotope.LambdaCase.Semantics.Categorical
