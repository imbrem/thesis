import Isotope.LambdaIter.Semantics.Categorical

/-!
# Derived iteration diagrams

These lemmas isolate the equations supplied by the abstract Elgot interfaces
from the additional work needed to relate contextual `lambda_iter` denotations
to bare categorical iteration.  In particular, none of the results in this
file is a model axiom for the syntax.
-/

namespace Isotope.LambdaIter.Semantics.Categorical

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] [HasFiniteCoproducts C]
  [Iteration C] [ElgotCategory C]

/-- The semantic loop unfolds by one iteration step. -/
theorem loop_fixpoint {X Y : C} (f : X ⟶ Y ⨿ X) :
    loop f = f ≫ coprod.desc (𝟙 Y) (loop f) :=
  ElgotCategory.fixpoint f

/-- Postcomposition of a loop is absorbed into its return branch. -/
theorem loop_naturality {X Y Z : C} (f : X ⟶ Y ⨿ X) (g : Y ⟶ Z) :
    loop f ≫ g = loop (f ≫ coprod.map g (𝟙 X)) :=
  ElgotCategory.naturality f g

/-- Nested loops satisfy the codiagonal equation. -/
theorem loop_codiagonal {X Y : C} (f : X ⟶ (Y ⨿ X) ⨿ X) :
    loop (loop f) =
      loop (f ≫ coprod.desc (𝟙 (Y ⨿ X))
        (coprod.inr : X ⟶ Y ⨿ X)) :=
  ElgotCategory.codiagonal f

section Freyd

variable {V : Type u₂} [Category.{v₂} V]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : Functor V C) [ElgotFreydCategory J]

/-- Uniformity is derivable when the change of loop state is a pure value
morphism.  This is the categorical theorem targeted by the syntactic
uniformity rule after purity and environment-threading have been discharged. -/
theorem loop_pure_uniformity {A D : V} {B : C}
    (f : J.obj A ⟶ B ⨿ J.obj A) (g : J.obj D ⟶ B ⨿ J.obj D)
    (h : A ⟶ D)
    (comm : f ≫ coprod.map (𝟙 B) (J.map h) = J.map h ≫ g) :
    loop f = J.map h ≫ loop g :=
  ElgotFreydCategory.pure_uniformity J f g h comm

end Freyd

section Strong

variable {V : Type u₂} [Category.{v₂} V]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]

/-- Threading a fixed context through a bare loop is supplied by strong Elgot
iteration, rather than being an additional language-model law. -/
theorem loop_strength (R : C) {X Y : C} (f : X ⟶ Y ⨿ X) :
    threadLoop R f = R ◁ loop f :=
  threadLoop_eq J R f

end Strong

end Isotope.LambdaIter.Semantics.Categorical
