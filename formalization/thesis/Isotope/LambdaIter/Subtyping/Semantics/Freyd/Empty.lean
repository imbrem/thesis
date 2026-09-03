import Isotope.LambdaIter.Subtyping.Semantics.Freyd.Combinators

/-!
# Strictness of the interpreted empty type

`DistributiveTensor` asks only that `X ⊗ -` preserve *binary* coproducts.  That
does not imply `R ⊗ 0 ≅ 0`, so the nullary half of distributivity has to be
requested separately.  It is exactly what validates the `emptyInitial` axiom
scheme — once an empty-typed computation has run, its continuation is
irrelevant — and it is what removes the `abort` slack from typing coherence.

This is the lambda-iter home of the law.  Two earlier, local copies of the same
statement already exist further downstream — `TensorEmptyStrict` and its
companions in `Isotope/LambdaSSA/Semantics/Empty.lean`, and the initiality
helpers in `Isotope/LambdaCase/Semantics/Abort.lean`.  Neither is changed here:
unifying the three (by `export`ing this one) is a mechanical integration step,
deliberately left out of this file so that no downstream module is disturbed.
-/

universe v₁ v₂ u₁ u₂ u₃

namespace Isotope.LambdaIter.Subtyping.Semantics.Categorical

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : Functor V C) [DistributiveFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] [Subtyping τ] (M : TypeModel τ V)

/-- The nullary part of distributivity omitted by `DistributiveTensor`:
tensoring the interpreted empty type with an environment stays initial.  It is
optional because binary distributivity alone does not imply it. -/
class TensorEmptyStrict : Prop where
  leftInitial (R : V) :
    Nonempty (IsInitial (R ⊗ (M.obj (TypeFormers.empty : τ))))
  rightInitial (R : V) :
    Nonempty (IsInitial ((M.obj (TypeFormers.empty : τ)) ⊗ R))

/-- A distributive Freyd inclusion carries the interpreted empty type to an
initial computation object. -/
noncomputable def computationEmptyIsInitial :
    IsInitial (J.obj (M.obj (TypeFormers.empty : τ))) :=
  M.emptyIsInitial.isInitialObj J

/-- Under `TensorEmptyStrict`, an environment paired with the interpreted empty
type is carried to an initial computation object.  Consequently any two
continuations of an empty-typed computation agree. -/
theorem computationTensorEmptyIsInitial [TensorEmptyStrict M] (R : V) {X : C}
    (f g : J.obj (R ⊗ (M.obj (TypeFormers.empty : τ))) ⟶ X) : f = g := by
  obtain ⟨h⟩ := TensorEmptyStrict.leftInitial (M := M) R
  exact (h.isInitialObj J).hom_ext f g

/-- Symmetric companion of `computationTensorEmptyIsInitial`. -/
theorem computationEmptyTensorIsInitial [TensorEmptyStrict M] (R : V) {X : C}
    (f g : J.obj ((M.obj (TypeFormers.empty : τ)) ⊗ R) ⟶ X) : f = g := by
  obtain ⟨h⟩ := TensorEmptyStrict.rightInitial (M := M) R
  exact (h.isInitialObj J).hom_ext f g

/-- Empty elimination followed by any continuation depends only on the
empty-producing prefix. -/
theorem abort_comp_eq {R : V} {A : τ} {X : C}
    (z : J.obj R ⟶ J.obj (M.obj (TypeFormers.empty : τ)))
    (f g : J.obj (M.obj (A : τ)) ⟶ X) :
    abort J M (A := A) z ≫ f = abort J M (A := A) z ≫ g := by
  rw [abort, Category.assoc, Category.assoc]
  congr 1
  exact (computationEmptyIsInitial J M).hom_ext _ _

end Isotope.LambdaIter.Subtyping.Semantics.Categorical
