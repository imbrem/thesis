import Isotope.CategoryTheory.Freyd.Distributive

/-!
# Elgot and strong Elgot Freyd categories

The convention agrees with `Isotope.Elgot.LawfulElgotMonad`: the left coproduct summand returns
a result and the right summand requests another iteration.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits
open scoped MonoidalCategory

/-- An iteration operator for computation morphisms. -/
class Iteration (C : Type u₁) [Category.{v₁} C] [HasBinaryCoproducts C] where
  iterate {X Y : C} : (X ⟶ Y ⨿ X) → (X ⟶ Y)

export Iteration (iterate)

/-- The categorical complete-Elgot equations.  These are oriented to match
`Isotope.Elgot.LawfulElgotMonad`. -/
class ElgotCategory (C : Type u₁) [Category.{v₁} C] [HasFiniteCoproducts C]
    [Iteration C] : Prop where
  fixpoint {X Y : C} (f : X ⟶ Y ⨿ X) :
    iterate f = f ≫ coprod.desc (𝟙 Y) (iterate f) := by cat_disch
  naturality {X Y Z : C} (f : X ⟶ Y ⨿ X) (g : Y ⟶ Z) :
    iterate f ≫ g = iterate (f ≫ coprod.map g (𝟙 X)) := by cat_disch
  codiagonal {X Y : C} (f : X ⟶ (Y ⨿ X) ⨿ X) :
    iterate (iterate f) =
      iterate (f ≫ coprod.desc (𝟙 (Y ⨿ X))
        (coprod.inr : X ⟶ Y ⨿ X)) := by cat_disch

attribute [reassoc] ElgotCategory.fixpoint ElgotCategory.naturality

namespace ElgotCategory

variable {C : Type u₁} [Category.{v₁} C] [HasFiniteCoproducts C]
  [Iteration C] [ElgotCategory C]

/-- Unfold one iteration step. -/
theorem unfold {X Y : C} (f : X ⟶ Y ⨿ X) :
    f ≫ coprod.desc (𝟙 Y) (iterate f) = iterate f :=
  (ElgotCategory.fixpoint f).symm

end ElgotCategory

/-- A distributive Freyd category whose iteration is uniform under changes of state made by
pure value morphisms.  No uniformity for arbitrary effectful computation morphisms is claimed. -/
class ElgotFreydCategory {V : Type u₁} {C : Type u₂}
    [Category.{v₁} V] [Category.{v₂} C]
    [CartesianMonoidalCategory V] [SymmetricCategory V]
    [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
    [HasFiniteCoproducts V] [HasFiniteCoproducts C]
    [DistributiveTensor V] [DistributivePremonoidalCategory C]
    [Iteration C] [ElgotCategory C]
    (J : Functor V C) extends DistributiveFreydCategory J where
  uniformity {A D : V} {B : C}
      (f : J.obj A ⟶ B ⨿ J.obj A) (g : J.obj D ⟶ B ⨿ J.obj D) (h : A ⟶ D)
      (comm : f ≫ coprod.map (𝟙 B) (J.map h) = J.map h ≫ g) :
    iterate f = J.map h ≫ iterate g := by cat_disch

namespace ElgotFreydCategory

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [ElgotFreydCategory J]

theorem pure_uniformity {A D : V} {B : C}
    (f : J.obj A ⟶ B ⨿ J.obj A) (g : J.obj D ⟶ B ⨿ J.obj D) (h : A ⟶ D)
    (comm : f ≫ coprod.map (𝟙 B) (J.map h) = J.map h ≫ g) :
    iterate f = J.map h ≫ iterate g :=
  ElgotFreydCategory.uniformity f g h comm

end ElgotFreydCategory

/-- Strength of iteration: an unchanged context may be threaded through every loop iteration.
The right-handed form follows from this equation and symmetry, so only the paper's left-handed
law is stored. -/
class StrongElgotFreydCategory {V : Type u₁} {C : Type u₂}
    [Category.{v₁} V] [Category.{v₂} C]
    [CartesianMonoidalCategory V] [SymmetricCategory V]
    [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
    [HasFiniteCoproducts V] [HasFiniteCoproducts C]
    [DistributiveTensor V] [DistributivePremonoidalCategory C]
    [Iteration C] [ElgotCategory C]
    (J : Functor V C) extends ElgotFreydCategory J where
  iterate_whiskerLeft {X Y : C} (Z : C) (f : X ⟶ Y ⨿ X) :
    iterate ((Z ◁ f) ≫ DistributivePremonoidalCategory.leftInv Z Y X) =
      Z ◁ iterate f := by cat_disch

namespace StrongElgotFreydCategory

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]

theorem strength (J : Functor V C) [StrongElgotFreydCategory J]
    {X Y : C} (Z : C) (f : X ⟶ Y ⨿ X) :
    iterate ((Z ◁ f) ≫ DistributivePremonoidalCategory.leftInv Z Y X) =
      Z ◁ iterate f :=
  StrongElgotFreydCategory.iterate_whiskerLeft (J := J) Z f

end StrongElgotFreydCategory

end CategoryTheory
