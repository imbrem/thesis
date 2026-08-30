import Isotope.CategoryTheory.Monad.Strong
import Isotope.CategoryTheory.Premonoidal.Basic

/-! # Premonoidal Kleisli categories of strong monads -/

universe v u

namespace CategoryTheory

open Category
open scoped MonoidalCategory

namespace Kleisli

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  (T : Monad C) [T.Strong] [SymmetricCategory C]

def whiskerLeft (X : Kleisli T) {Y Z : Kleisli T} (f : Y ⟶ Z) :
    Kleisli.Hom (.mk T (X.of ⊗ Y.of)) (.mk T (X.of ⊗ Z.of)) :=
  .mk (X.of ◁ f.of ≫ Monad.Strong.strength X.of Z.of)

def whiskerRight {X Y : Kleisli T} (f : X ⟶ Y) (Z : Kleisli T) :
    Kleisli.Hom (.mk T (X.of ⊗ Z.of)) (.mk T (Y.of ⊗ Z.of)) :=
  .mk (f.of ▷ Z.of ≫ Monad.Strong.costrength T Y.of Z.of)

instance monoidalCategoryStruct : MonoidalCategoryStruct (Kleisli T) where
  tensorObj X Y := .mk T (X.of ⊗ Y.of)
  whiskerLeft := whiskerLeft T
  whiskerRight := fun f Z ↦ whiskerRight T f Z
  tensorUnit := .mk T (𝟙_ C)
  associator X Y Z := (Kleisli.Adjunction.toKleisli T).mapIso (α_ X.of Y.of Z.of)
  leftUnitor X := (Kleisli.Adjunction.toKleisli T).mapIso (λ_ X.of)
  rightUnitor X := (Kleisli.Adjunction.toKleisli T).mapIso (ρ_ X.of)

@[simp] theorem tensorObj_of (X Y : Kleisli T) : (X ⊗ Y).of = X.of ⊗ Y.of := rfl
@[simp] theorem tensorUnit_of : (𝟙_ (Kleisli T)).of = 𝟙_ C := rfl

@[simp] theorem whiskerLeft_of (X : Kleisli T) {Y Z : Kleisli T} (f : Y ⟶ Z) :
    (X ◁ f).of = X.of ◁ f.of ≫ Monad.Strong.strength X.of Z.of := rfl

@[simp] theorem whiskerRight_of {X Y : Kleisli T} (f : X ⟶ Y) (Z : Kleisli T) :
    (f ▷ Z).of = f.of ▷ Z.of ≫ Monad.Strong.costrength T Y.of Z.of := rfl

theorem whiskerLeft_id (X Y : Kleisli T) : X ◁ 𝟙 Y = 𝟙 (X ⊗ Y) := by
  apply Kleisli.hom_ext
  dsimp [whiskerLeft]
  exact Monad.Strong.unit X.of Y.of

theorem whiskerLeft_comp (X : Kleisli T) {Y Z W : Kleisli T}
    (f : Y ⟶ Z) (g : Z ⟶ W) : X ◁ (f ≫ g) = X ◁ f ≫ X ◁ g := by
  apply Kleisli.hom_ext
  dsimp [whiskerLeft]
  rw [MonoidalCategory.whiskerLeft_comp X.of f.of (T.map g.of ≫ T.μ.app W.of)]
  rw [MonoidalCategory.whiskerLeft_comp X.of (T.map g.of) (T.μ.app W.of)]
  simp only [Category.assoc]
  have hmul := Monad.Strong.multiplication (T := T) X.of W.of
  slice_lhs 3 4 => exact hmul
  rw [Monad.Strong.naturality_right_assoc]
  simp only [Functor.map_comp, Category.assoc]

theorem id_whiskerRight (X Y : Kleisli T) : 𝟙 X ▷ Y = 𝟙 (X ⊗ Y) := by
  apply Kleisli.hom_ext
  dsimp [whiskerRight]
  exact Monad.Strong.costrength_unit T X.of Y.of

theorem comp_whiskerRight {X Y Z : Kleisli T} (f : X ⟶ Y) (g : Y ⟶ Z)
    (W : Kleisli T) : (f ≫ g) ▷ W = f ▷ W ≫ g ▷ W := by
  apply Kleisli.hom_ext
  dsimp [whiskerRight]
  rw [MonoidalCategory.comp_whiskerRight f.of (T.map g.of ≫ T.μ.app Z.of) W.of]
  rw [MonoidalCategory.comp_whiskerRight (T.map g.of) (T.μ.app Z.of) W.of]
  simp only [Category.assoc]
  have hmul := Monad.Strong.costrength_multiplication (T := T) Z.of W.of
  slice_lhs 3 4 => exact hmul
  rw [Monad.Strong.costrength_naturality_left_assoc]
  simp only [Functor.map_comp, Category.assoc]

theorem toKleisli_map_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) :
    (Kleisli.Adjunction.toKleisli T).map f ▷ (.mk T Z) =
      (Kleisli.Adjunction.toKleisli T).map (f ▷ Z) := by
  apply Kleisli.hom_ext
  dsimp [whiskerRight, Kleisli.Adjunction.toKleisli]
  rw [MonoidalCategory.comp_whiskerRight_assoc]
  have hunit := Monad.Strong.costrength_unit T Y Z
  slice_lhs 2 3 => exact hunit

theorem whiskerLeft_toKleisli_map (X : C) {Y Z : C} (f : Y ⟶ Z) :
    (.mk T X) ◁ (Kleisli.Adjunction.toKleisli T).map f =
      (Kleisli.Adjunction.toKleisli T).map (X ◁ f) := by
  apply Kleisli.hom_ext
  dsimp [whiskerLeft, Kleisli.Adjunction.toKleisli]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]
  have hunit := Monad.Strong.unit (T := T) X Z
  slice_lhs 2 3 => exact hunit

end Kleisli

end CategoryTheory
