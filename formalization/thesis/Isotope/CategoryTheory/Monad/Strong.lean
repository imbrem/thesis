import Mathlib.CategoryTheory.Monad.Kleisli
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Strong monads on symmetric monoidal categories

This is the categorical interface needed to construct the premonoidal structure on a Kleisli
category. The strength is natural in both arguments, coherent with the monoidal structure, and
compatible with the monad unit and multiplication.
-/

universe v u

namespace CategoryTheory

open Category
open scoped MonoidalCategory

/-- A tensorial strength for a categorical monad. -/
class Monad.Strong {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (T : Monad C) where
  strength (X Y : C) : X ⊗ T.obj Y ⟶ T.obj (X ⊗ Y)
  naturality_left {X X' : C} (f : X ⟶ X') (Y : C) :
      (f ▷ T.obj Y) ≫ strength X' Y = strength X Y ≫ T.map (f ▷ Y) := by cat_disch
  naturality_right (X : C) {Y Y' : C} (f : Y ⟶ Y') :
      (X ◁ T.map f) ≫ strength X Y' = strength X Y ≫ T.map (X ◁ f) := by cat_disch
  associativity (X Y Z : C) :
      (α_ X Y (T.obj Z)).hom ≫ X ◁ strength Y Z ≫ strength X (Y ⊗ Z) =
        strength (X ⊗ Y) Z ≫ T.map (α_ X Y Z).hom := by cat_disch
  left_unitality (X : C) :
      strength (𝟙_ C) X ≫ T.map (λ_ X).hom = (λ_ (T.obj X)).hom := by cat_disch
  unit (X Y : C) :
      X ◁ T.η.app Y ≫ strength X Y = T.η.app (X ⊗ Y) := by cat_disch
  multiplication (X Y : C) :
      X ◁ T.μ.app Y ≫ strength X Y =
        strength X (T.obj Y) ≫ T.map (strength X Y) ≫ T.μ.app (X ⊗ Y) := by cat_disch

namespace Monad.Strong

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (T : Monad C) [T.Strong]

attribute [reassoc] naturality_left naturality_right associativity left_unitality unit
  multiplication

/-- The costrength induced by a strength and a symmetry. -/
def costrength [BraidedCategory C] (X Y : C) : T.obj X ⊗ Y ⟶ T.obj (X ⊗ Y) :=
  (BraidedCategory.braiding (T.obj X) Y).hom ≫ strength Y X ≫
    T.map (BraidedCategory.braiding Y X).hom

theorem costrength_def [BraidedCategory C] (X Y : C) :
    costrength T X Y = (BraidedCategory.braiding (T.obj X) Y).hom ≫ strength Y X ≫
      T.map (BraidedCategory.braiding Y X).hom := rfl

end Monad.Strong

end CategoryTheory
