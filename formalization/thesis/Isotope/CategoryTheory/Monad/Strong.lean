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

theorem costrength_unit [SymmetricCategory C] (X Y : C) :
    T.η.app X ▷ Y ≫ costrength T X Y = T.η.app (X ⊗ Y) := by
  rw [costrength_def, BraidedCategory.braiding_naturality_left_assoc]
  have hunit := Monad.Strong.unit (T := T) Y X
  slice_lhs 2 3 => exact hunit
  slice_lhs 2 3 => exact (T.η.naturality (BraidedCategory.braiding Y X).hom).symm
  simp

theorem costrength_naturality_left [SymmetricCategory C] {X X' : C}
    (f : X ⟶ X') (Y : C) :
    (T.map f ▷ Y) ≫ costrength T X' Y = costrength T X Y ≫ T.map (f ▷ Y) := by
  rw [costrength_def, costrength_def,
    BraidedCategory.braiding_naturality_left_assoc]
  rw [Monad.Strong.naturality_right_assoc]
  simp only [Category.assoc]
  rw [← Functor.map_comp, BraidedCategory.braiding_naturality_right]
  simp only [Functor.map_comp]

theorem costrength_naturality_right [SymmetricCategory C] (X : C) {Y Y' : C}
    (f : Y ⟶ Y') :
    (T.obj X ◁ f) ≫ costrength T X Y' = costrength T X Y ≫ T.map (X ◁ f) := by
  rw [costrength_def, costrength_def,
    BraidedCategory.braiding_naturality_right_assoc]
  rw [Monad.Strong.naturality_left_assoc]
  simp only [Category.assoc]
  rw [← Functor.map_comp, BraidedCategory.braiding_naturality_left]
  simp only [Functor.map_comp]

theorem costrength_multiplication [SymmetricCategory C] (X Y : C) :
    (T.μ.app X ▷ Y) ≫ costrength T X Y =
      costrength T (T.obj X) Y ≫ T.map (costrength T X Y) ≫ T.μ.app (X ⊗ Y) := by
  rw [costrength_def, costrength_def,
    BraidedCategory.braiding_naturality_left_assoc]
  have hmul := Monad.Strong.multiplication_assoc (T := T) Y X
    (T.map (BraidedCategory.braiding Y X).hom)
  slice_lhs 2 4 => exact hmul
  have hnat := (T.μ.naturality (BraidedCategory.braiding Y X).hom).symm
  slice_lhs 4 5 => exact hnat
  rw [Functor.map_comp]
  simp only [Category.assoc]
  simp only [Functor.comp_obj, Functor.comp_map]
  have hcancel :
      T.map (BraidedCategory.braiding Y (T.obj X)).hom ≫
        T.map (BraidedCategory.braiding (T.obj X) Y).hom = 𝟙 _ := by
    rw [← Functor.map_comp, SymmetricCategory.symmetry, Functor.map_id]
  slice_rhs 3 4 => exact hcancel
  simp only [Category.id_comp]
  rw [Functor.map_comp]
  simp only [Category.assoc]

attribute [reassoc] costrength_unit costrength_naturality_left
  costrength_naturality_right costrength_multiplication

end Monad.Strong

end CategoryTheory
