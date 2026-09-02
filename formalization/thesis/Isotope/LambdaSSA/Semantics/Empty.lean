import Isotope.LambdaSSA.Semantics.Model

/-! # Strictness of the interpreted empty type -/

universe v₁ v₂ u₁ u₂ u₃

namespace Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open Isotope.LambdaIter.Subtyping.Semantics.Categorical
open scoped MonoidalCategory

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : Functor V C) [DistributiveFreydCategory J]
  {τ : Type u₃} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
  (M : TypeModel τ V)

/-- The nullary part of distributivity omitted by `DistributiveTensor`:
tensoring the interpreted initial type with an environment remains initial.
It is optional because binary distributivity alone does not imply this law. -/
class TensorEmptyStrict where
  leftInitial (R : V) : IsInitial (R ⊗ (M.obj (LambdaIter.empty : τ)))
  rightInitial (R : V) : IsInitial ((M.obj (LambdaIter.empty : τ)) ⊗ R)

/-- The chosen Freyd functor carries the strict left tensor with empty to an
initial computation object. -/
noncomputable def computationTensorEmptyIsInitial [TensorEmptyStrict M] (R : V) :
    IsInitial (J.obj (R ⊗ (M.obj (LambdaIter.empty : τ)))) :=
  (TensorEmptyStrict.leftInitial (M := M) R).isInitialObj J

/-- Symmetric companion of `computationTensorEmptyIsInitial`. -/
noncomputable def computationEmptyTensorIsInitial [TensorEmptyStrict M] (R : V) :
    IsInitial (J.obj ((M.obj (LambdaIter.empty : τ)) ⊗ R)) :=
  (TensorEmptyStrict.rightInitial (M := M) R).isInitialObj J

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

/-- A computation factors through the interpreted empty type.  The prefix is
kept as data: arrows *into* an initial object need not be unique. -/
structure FactorsThroughEmpty {R X : V} (f : J.obj R ⟶ J.obj X) where
  emptyPrefix : J.obj R ⟶ J.obj (M.obj (LambdaIter.empty : τ))
  suffix : J.obj (M.obj (LambdaIter.empty : τ)) ⟶ J.obj X
  factor : emptyPrefix ≫ suffix = f

/-- Postcomposition preserves empty factorization and its empty-producing
prefix. -/
def FactorsThroughEmpty.comp {R X Y : V} {f : J.obj R ⟶ J.obj X}
    (hf : FactorsThroughEmpty J M f) (k : J.obj X ⟶ J.obj Y) :
    FactorsThroughEmpty J M (f ≫ k) := by
  refine ⟨hf.emptyPrefix, hf.suffix ≫ k, ?_⟩
  rw [← Category.assoc, hf.factor]

/-- Two empty factorizations with the same prefix denote the same
computation, independently of their continuations. -/
theorem FactorsThroughEmpty.eq_of_prefix {R X : V} {f g : J.obj R ⟶ J.obj X}
    (hf : FactorsThroughEmpty J M f) (hg : FactorsThroughEmpty J M g)
    (hp : hf.emptyPrefix = hg.emptyPrefix) : f = g := by
  rw [← hf.factor, ← hg.factor, hp]
  apply empty_continuation_unique J M

/-- Empty elimination is the canonical empty factorization. -/
def abort_factors {R : V} {A : τ}
    (z : J.obj R ⟶ J.obj (M.obj (LambdaIter.empty : τ))) :
    FactorsThroughEmpty J M
      (LambdaIter.Subtyping.Semantics.Categorical.abort J M (A := A) z) := by
  exact ⟨z, J.map (M.emptyIsInitial.to (M.obj A)), rfl⟩

end Isotope.LambdaSSA.Semantics.Categorical
