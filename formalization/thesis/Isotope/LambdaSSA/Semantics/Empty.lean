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

end Isotope.LambdaSSA.Semantics.Categorical
