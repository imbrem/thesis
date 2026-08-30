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

theorem toKleisli_map_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : Kleisli T) :
    (Kleisli.Adjunction.toKleisli T).map f ▷ Z =
      (Kleisli.Adjunction.toKleisli T).map (f ▷ Z.of) := by
  apply Kleisli.hom_ext
  dsimp [whiskerRight, Kleisli.Adjunction.toKleisli]
  rw [MonoidalCategory.comp_whiskerRight_assoc]
  have hunit := Monad.Strong.costrength_unit T Y Z.of
  slice_lhs 2 3 => exact hunit

theorem whiskerLeft_toKleisli_map (X : Kleisli T) {Y Z : C} (f : Y ⟶ Z) :
    X ◁ (Kleisli.Adjunction.toKleisli T).map f =
      (Kleisli.Adjunction.toKleisli T).map (X.of ◁ f) := by
  apply Kleisli.hom_ext
  dsimp [whiskerLeft, Kleisli.Adjunction.toKleisli]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]
  have hunit := Monad.Strong.unit (T := T) X.of Z
  slice_lhs 2 3 => exact hunit

omit [MonoidalCategory C] [T.Strong] [SymmetricCategory C] in
theorem toKleisli_map_comp {X Y : C} (f : X ⟶ Y) {Z : Kleisli T}
    (g : (Kleisli.Adjunction.toKleisli T).obj Y ⟶ Z) :
    ((Kleisli.Adjunction.toKleisli T).map f ≫ g).of = f ≫ g.of := by
  dsimp [Kleisli.Adjunction.toKleisli]
  have hunit : T.η.app Y ≫ T.map g.of ≫ T.μ.app Z.of = g.of := by
    rw [← T.η.naturality_assoc, T.left_unit]
    simp
  slice_lhs 2 4 => exact hunit

omit [MonoidalCategory C] [T.Strong] [SymmetricCategory C] in
theorem comp_toKleisli_map {X Y : Kleisli T} (f : X ⟶ Y) {Z : C}
    (g : Y.of ⟶ Z) :
    (f ≫ (Kleisli.Adjunction.toKleisli T).map g).of = f.of ≫ T.map g := by
  dsimp [Kleisli.Adjunction.toKleisli]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  have hunit := T.right_unit Z
  slice_lhs 3 4 => exact hunit
  simp

/-- Every morphism from the base category becomes central in the Kleisli category. -/
theorem toKleisli_map_isCentral {X Y : C} (f : X ⟶ Y) :
    PremonoidalCategory.IsCentral ((Kleisli.Adjunction.toKleisli T).map f) := by
  constructor
  · intro X' Y' g
    apply Kleisli.hom_ext
    simp only [PremonoidalCategory.leftTensor, PremonoidalCategory.rightTensor]
    rw [toKleisli_map_whiskerRight, toKleisli_map_whiskerRight]
    have hmiddle :
        (f ▷ X'.of) ≫ ((Kleisli.Adjunction.toKleisli T).obj Y ◁ g).of =
          ((Kleisli.Adjunction.toKleisli T).obj X ◁ g).of ≫ T.map (f ▷ Y'.of) := by
      dsimp [whiskerLeft]
      rw [← MonoidalCategory.whisker_exchange_assoc]
      rw [Monad.Strong.naturality_left]
      simp only [Category.assoc]
    exact (toKleisli_map_comp T (f ▷ X'.of) _).trans
      (hmiddle.trans (comp_toKleisli_map T _ (f ▷ Y'.of)).symm)
  · intro X' Y' g
    apply Kleisli.hom_ext
    simp only [PremonoidalCategory.leftTensor, PremonoidalCategory.rightTensor]
    rw [whiskerLeft_toKleisli_map, whiskerLeft_toKleisli_map]
    have hmiddle :
        (g ▷ (Kleisli.Adjunction.toKleisli T).obj X).of ≫ T.map (Y'.of ◁ f) =
          (X'.of ◁ f) ≫ (g ▷ (Kleisli.Adjunction.toKleisli T).obj Y).of := by
      dsimp [whiskerRight]
      simp only [Category.assoc]
      have hcostr := (Monad.Strong.costrength_naturality_right (T := T) Y'.of f).symm
      slice_lhs 2 3 => exact hcostr
      rw [MonoidalCategory.whisker_exchange_assoc]
    exact (comp_toKleisli_map T _ (Y'.of ◁ f)).trans
      (hmiddle.trans (toKleisli_map_comp T (X'.of ◁ f) _).symm)

theorem associator_hom_isCentral (X Y Z : Kleisli T) :
    PremonoidalCategory.IsCentral (α_ X Y Z).hom := by
  exact toKleisli_map_isCentral T (α_ X.of Y.of Z.of).hom

theorem leftUnitor_hom_isCentral (X : Kleisli T) :
    PremonoidalCategory.IsCentral (λ_ X).hom := by
  exact toKleisli_map_isCentral T (λ_ X.of).hom

theorem rightUnitor_hom_isCentral (X : Kleisli T) :
    PremonoidalCategory.IsCentral (ρ_ X).hom := by
  exact toKleisli_map_isCentral T (ρ_ X.of).hom

theorem associator_naturality_right (X Y : Kleisli T) {Z W : Kleisli T}
    (f : Z ⟶ W) :
    ((X ⊗ Y) ◁ f) ≫ (α_ X Y W).hom =
      (α_ X Y Z).hom ≫ X ◁ (Y ◁ f) := by
  apply Kleisli.hom_ext
  change (((X ⊗ Y) ◁ f) ≫
      (Kleisli.Adjunction.toKleisli T).map (α_ X.of Y.of W.of).hom).of = _
  rw [comp_toKleisli_map]
  change _ = (((Kleisli.Adjunction.toKleisli T).map (α_ X.of Y.of Z.of).hom ≫
      X ◁ (Y ◁ f)).of)
  rw [toKleisli_map_comp]
  dsimp [whiskerLeft]
  rw [MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [← Monad.Strong.associativity]
  rw [MonoidalCategory.associator_naturality_right_assoc]

end Kleisli

end CategoryTheory
