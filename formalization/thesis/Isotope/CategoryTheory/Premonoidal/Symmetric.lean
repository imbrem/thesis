import Isotope.CategoryTheory.Premonoidal.Basic

/-! # Symmetric premonoidal categories -/

universe v u

namespace CategoryTheory

open Category
open scoped MonoidalCategory

/-- A premonoidal-compatible braiding: it is separately natural, central, and satisfies both
hexagons. Unlike Mathlib's `BraidedCategory`, this does not require bifunctorial tensor. -/
class BraidedPremonoidalCategory (C : Type u) [Category.{v} C] [PremonoidalCategory C] where
  braiding : ∀ X Y : C, X ⊗ Y ≅ Y ⊗ X
  naturality_left {X Y : C} (f : X ⟶ Y) (Z : C) :
      f ▷ Z ≫ (braiding Y Z).hom = (braiding X Z).hom ≫ Z ◁ f := by cat_disch
  naturality_right (X : C) {Y Z : C} (f : Y ⟶ Z) :
      X ◁ f ≫ (braiding X Z).hom = (braiding X Y).hom ≫ f ▷ X := by cat_disch
  hexagon_forward (X Y Z : C) :
      (α_ X Y Z).hom ≫ (braiding X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
        (braiding X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (braiding X Z).hom := by
    cat_disch
  hexagon_reverse (X Y Z : C) :
      (α_ X Y Z).inv ≫ (braiding (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
        X ◁ (braiding Y Z).hom ≫ (α_ X Z Y).inv ≫ (braiding X Z).hom ▷ Y := by
    cat_disch
  braiding_central (X Y : C) : PremonoidalCategory.IsCentral (braiding X Y).hom := by
    cat_disch

namespace BraidedPremonoidalCategory

notation "β_" => BraidedPremonoidalCategory.braiding

end BraidedPremonoidalCategory

/-- A symmetric premonoidal category is braided and its braiding is self-inverse. -/
class SymmetricPremonoidalCategory (C : Type u) [Category.{v} C] [PremonoidalCategory C]
    extends BraidedPremonoidalCategory C where
  symmetry (X Y : C) : (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y) := by cat_disch

attribute [reassoc] BraidedPremonoidalCategory.naturality_left
  BraidedPremonoidalCategory.naturality_right
  BraidedPremonoidalCategory.hexagon_forward BraidedPremonoidalCategory.hexagon_reverse
attribute [reassoc (attr := simp)] SymmetricPremonoidalCategory.symmetry

end CategoryTheory
