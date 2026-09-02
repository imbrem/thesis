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

/-- The nullary part of distributivity omitted by `DistributiveTensor`:
tensoring the interpreted initial type with an environment remains initial.
It is optional because binary distributivity alone does not imply this law. -/
class TensorEmptyStrict : Prop where
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
structure FactorsThroughEmpty {R X : V} (f : J.obj R ⟶ J.obj X) : Prop where
  prefix : J.obj R ⟶ J.obj (M.obj (LambdaIter.empty : τ))
  continuation : J.obj (M.obj (LambdaIter.empty : τ)) ⟶ J.obj X
  factor : prefix ≫ continuation = f

/-- Postcomposition preserves empty factorization and its empty-producing
prefix. -/
theorem FactorsThroughEmpty.comp {R X Y : V} {f : J.obj R ⟶ J.obj X}
    (hf : FactorsThroughEmpty J M f) (k : J.obj X ⟶ J.obj Y) :
    FactorsThroughEmpty J M (f ≫ k) := by
  refine ⟨hf.prefix, hf.continuation ≫ k, ?_⟩
  rw [← Category.assoc, hf.factor]

/-- Two empty factorizations with the same prefix denote the same
computation, independently of their continuations. -/
theorem FactorsThroughEmpty.eq_of_prefix {R X : V} {f g : J.obj R ⟶ J.obj X}
    (hf : FactorsThroughEmpty J M f) (hg : FactorsThroughEmpty J M g)
    (hp : hf.prefix = hg.prefix) : f = g := by
  rw [← hf.factor, ← hg.factor, hp]
  apply empty_continuation_unique J M

/-- Empty elimination is the canonical empty factorization. -/
theorem abort_factors {R : V} {A : τ}
    (z : J.obj R ⟶ J.obj (M.obj (LambdaIter.empty : τ))) :
    FactorsThroughEmpty J M
      (LambdaIter.Subtyping.Semantics.Categorical.abort J M (A := A) z) := by
  exact ⟨z, J.map (M.emptyIsInitial.to (M.obj A)), rfl⟩

theorem extend_comp_map {R X Y : V} (f : J.obj R ⟶ J.obj X) (k : X ⟶ Y) :
    extend J (f ≫ J.map k) =
      extend J f ≫ J.map ((𝟙 R) ⊗ₘ k) := by
  simp [extend, PremonoidalCategory.leftTensor, Category.assoc,
    Functor.map_comp]

theorem FactorsThroughEmpty.extend [TensorEmptyStrict M]
    {R X : V} {f : J.obj R ⟶ J.obj X}
    (hf : FactorsThroughEmpty J M f) :
    FactorsThroughEmpty J M (extend J f) := by
  let E := M.obj (LambdaIter.empty : τ)
  let p : J.obj R ⟶ J.obj (R ⊗ E) := extend J hf.prefix
  let q : J.obj (R ⊗ E) ⟶ J.obj E :=
    (computationTensorEmptyIsInitial J M R).to _
  let k : J.obj E ⟶ J.obj (R ⊗ X) :=
    (computationEmptyIsInitial J M).to _
  refine ⟨p ≫ q, k, ?_⟩
  have hc : hf.continuation = J.map (M.emptyIsInitial.to X) :=
    (computationEmptyIsInitial J M).hom_ext _ _
  rw [← hf.factor, hc, extend_comp_map]
  change p ≫ q ≫ k = p ≫ J.map ((𝟙 R) ⊗ₘ M.emptyIsInitial.to X)
  rw [← Category.assoc]
  congr 1
  exact (computationTensorEmptyIsInitial J M R).hom_ext _ _

theorem FactorsThroughEmpty.bind [TensorEmptyStrict M]
    {R X Y : V} {f : J.obj R ⟶ J.obj X}
    (hf : FactorsThroughEmpty J M f)
    (g : J.obj (R ⊗ X) ⟶ J.obj Y) :
    FactorsThroughEmpty J M (bind J f g) := by
  exact (hf.extend (J := J) (M := M)).comp g

end Isotope.LambdaSSA.Semantics.Categorical
