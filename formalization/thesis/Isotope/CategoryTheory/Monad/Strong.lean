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

theorem costrength_right_unitality [SymmetricCategory C] (X : C) :
    costrength T X (𝟙_ C) ≫ T.map (ρ_ X).hom = (ρ_ (T.obj X)).hom := by
  rw [costrength_def]
  simp only [Category.assoc, ← Functor.map_comp]
  simp only [braiding_tensorUnit_right, braiding_tensorUnit_left, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [Monad.Strong.left_unitality]
  simp

theorem costrength_associativity [SymmetricCategory C] (X Y Z : C) :
    costrength T X Y ▷ Z ≫ costrength T (X ⊗ Y) Z ≫ T.map (α_ X Y Z).hom =
      (α_ (T.obj X) Y Z).hom ≫ costrength T X (Y ⊗ Z) := by
  simp only [costrength_def, MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [BraidedCategory.braiding_naturality_left_assoc]
  rw [Monad.Strong.naturality_right_assoc]
  rw [BraidedCategory.braiding_naturality_left_assoc]
  have hprefix :
      (BraidedCategory.braiding (T.obj X) Y).hom ▷ Z ≫
          (BraidedCategory.braiding (Y ⊗ T.obj X) Z).hom =
        (α_ (T.obj X) Y Z).hom ≫
          (BraidedCategory.braiding (T.obj X) (Y ⊗ Z)).hom ≫
          (BraidedCategory.braiding Y Z).hom ▷ T.obj X ≫
          (α_ Z Y (T.obj X)).hom := by
    rw [BraidedCategory.braiding_tensor_left_hom,
      BraidedCategory.braiding_tensor_right_hom]
    monoidal
  slice_lhs 1 2 => exact hprefix
  have hassoc := Monad.Strong.associativity (T := T) Z Y X
  slice_lhs 4 6 => exact hassoc
  have hnat := Monad.Strong.naturality_left (T := T)
    (BraidedCategory.braiding Y Z).hom X
  slice_lhs 3 4 => exact hnat
  have htail :
      (BraidedCategory.braiding Y Z).hom ▷ X ≫ (α_ Z Y X).hom ≫
          Z ◁ (BraidedCategory.braiding Y X).hom ≫
          (BraidedCategory.braiding Z (X ⊗ Y)).hom ≫ (α_ X Y Z).hom =
        (BraidedCategory.braiding (Y ⊗ Z) X).hom := by
    rw [BraidedCategory.braiding_tensor_right_hom,
      BraidedCategory.braiding_tensor_left_hom]
    apply (cancel_epi (α_ Y Z X).inv).1
    simp only [Category.assoc]
    rw [BraidedCategory.yang_baxter_assoc]
    have hcancel :
        X ◁ (BraidedCategory.braiding Y Z).hom ≫
          X ◁ (BraidedCategory.braiding Z Y).hom = 𝟙 _ := by
      rw [← MonoidalCategory.whiskerLeft_comp, SymmetricCategory.symmetry]
      simp
    slice_lhs 5 6 => exact hcancel
    simp
  simp only [← Functor.map_comp, Category.assoc]
  rw [htail]

theorem strength_costrength_associativity [SymmetricCategory C] (X Y Z : C) :
    strength X Y ▷ Z ≫ costrength T (X ⊗ Y) Z ≫ T.map (α_ X Y Z).hom =
      (α_ X (T.obj Y) Z).hom ≫ X ◁ costrength T Y Z ≫ strength X (Y ⊗ Z) := by
  simp only [costrength_def, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [BraidedCategory.braiding_naturality_left_assoc]
  rw [BraidedCategory.braiding_tensor_left_hom_assoc]
  have hassoc := Monad.Strong.associativity (T := T) Z X Y
  slice_lhs 5 7 => exact hassoc
  have hnatl := Monad.Strong.naturality_left (T := T)
    (BraidedCategory.braiding X Z).hom Y
  slice_lhs 4 5 => exact hnatl
  have hnatr := Monad.Strong.naturality_right (T := T) X
    (BraidedCategory.braiding Z Y).hom
  slice_rhs 4 5 => exact hnatr
  have hassoc_inv :
      X ◁ strength Z Y ≫ strength X (Z ⊗ Y) =
        (α_ X Z (T.obj Y)).inv ≫ strength (X ⊗ Z) Y ≫
          T.map (α_ X Z Y).hom := by
    apply (cancel_epi (α_ X Z (T.obj Y)).hom).1
    slice_rhs 1 2 => rw [Iso.hom_inv_id]
    simp only [Category.id_comp]
    exact Monad.Strong.associativity (T := T) X Z Y
  slice_rhs 3 4 => exact hassoc_inv
  simp only [← Functor.map_comp, Category.assoc]
  have htail :
      (BraidedCategory.braiding X Z).hom ▷ Y ≫ (α_ Z X Y).hom ≫
          (BraidedCategory.braiding Z (X ⊗ Y)).hom ≫ (α_ X Y Z).hom =
        (α_ X Z Y).hom ≫ X ◁ (BraidedCategory.braiding Z Y).hom := by
    rw [BraidedCategory.braiding_tensor_right_hom]
    simp only [Category.assoc]
    have hcancel :
        (BraidedCategory.braiding X Z).hom ▷ Y ≫
          (BraidedCategory.braiding Z X).hom ▷ Y = 𝟙 _ := by
      rw [← MonoidalCategory.comp_whiskerRight, SymmetricCategory.symmetry]
      simp
    slice_lhs 2 3 => rw [Iso.hom_inv_id]
    simp only [Category.id_comp]
    slice_lhs 1 2 => exact hcancel
    simp
  rw [htail]

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
  costrength_naturality_right costrength_right_unitality costrength_associativity
  strength_costrength_associativity costrength_multiplication

end Monad.Strong

end CategoryTheory
