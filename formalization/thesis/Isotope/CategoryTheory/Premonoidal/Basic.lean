import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Premonoidal categories

The object-level data deliberately reuses `MonoidalCategoryStruct`, but this file does **not**
assume Mathlib's `MonoidalCategory`: its tensor product of morphisms is bifunctorial, whereas a
premonoidal tensor is functorial in only one variable at a time.
-/

universe v u

namespace CategoryTheory

open Category
open scoped MonoidalCategory

namespace PremonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategoryStruct C]

/-- First run `f`, then `g`: the left sequential tensor of two morphisms. -/
def leftTensor {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') : X ⊗ X' ⟶ Y ⊗ Y' :=
  f ▷ X' ≫ Y ◁ g

/-- First run `g`, then `f`: the right sequential tensor of two morphisms. -/
def rightTensor {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') : X ⊗ X' ⟶ Y ⊗ Y' :=
  X ◁ g ≫ f ▷ Y'

scoped infixr:70 " ⋉ " => leftTensor
scoped infixr:70 " ⋊ " => rightTensor

/-- A morphism is central when it exchanges with every morphism in either tensor position. -/
def IsCentral {X Y : C} (f : X ⟶ Y) : Prop :=
  (∀ {X' Y' : C} (g : X' ⟶ Y'), f ⋉ g = f ⋊ g) ∧
  (∀ {X' Y' : C} (g : X' ⟶ Y'), g ⋉ f = g ⋊ f)

end PremonoidalCategory

open PremonoidalCategory

/-- A premonoidal category has functorial tensoring by each fixed object, with central coherent
associators and unitors. No interchange law for two arbitrary morphisms is assumed. -/
class PremonoidalCategory (C : Type u) [Category.{v} C] extends MonoidalCategoryStruct C where
  tensorHom_def {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') : f ⊗ₘ g = f ⋉ g := by
    cat_disch
  whiskerLeft_id (X Y : C) : X ◁ 𝟙 Y = 𝟙 (X ⊗ Y) := by cat_disch
  whiskerLeft_comp (X : C) {Y Z W : C} (f : Y ⟶ Z) (g : Z ⟶ W) :
      X ◁ (f ≫ g) = X ◁ f ≫ X ◁ g := by cat_disch
  id_whiskerRight (X Y : C) : 𝟙 X ▷ Y = 𝟙 (X ⊗ Y) := by cat_disch
  comp_whiskerRight {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (W : C) :
      (f ≫ g) ▷ W = f ▷ W ≫ g ▷ W := by cat_disch
  associator_central (X Y Z : C) : IsCentral (α_ X Y Z).hom := by cat_disch
  leftUnitor_central (X : C) : IsCentral (λ_ X).hom := by cat_disch
  rightUnitor_central (X : C) : IsCentral (ρ_ X).hom := by cat_disch
  associator_naturality_left {X Y : C} (f : X ⟶ Y) (Z W : C) :
      ((f ▷ Z) ▷ W) ≫ (α_ Y Z W).hom =
        (α_ X Z W).hom ≫ f ▷ (Z ⊗ W) := by cat_disch
  associator_naturality_middle (X : C) {Y Z : C} (f : Y ⟶ Z) (W : C) :
      ((X ◁ f) ▷ W) ≫ (α_ X Z W).hom =
        (α_ X Y W).hom ≫ X ◁ (f ▷ W) := by cat_disch
  associator_naturality_right (X Y : C) {Z W : C} (f : Z ⟶ W) :
      ((X ⊗ Y) ◁ f) ≫ (α_ X Y W).hom =
        (α_ X Y Z).hom ≫ X ◁ (Y ◁ f) := by cat_disch
  leftUnitor_naturality {X Y : C} (f : X ⟶ Y) :
      𝟙_ C ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by cat_disch
  rightUnitor_naturality {X Y : C} (f : X ⟶ Y) :
      f ▷ 𝟙_ C ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by cat_disch
  pentagon (W X Y Z : C) : MonoidalCategory.Pentagon W X Y Z := by cat_disch
  triangle (X Y : C) :
      (α_ X (𝟙_ C) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y := by cat_disch

attribute [reassoc] PremonoidalCategory.tensorHom_def
attribute [simp] PremonoidalCategory.whiskerLeft_id PremonoidalCategory.id_whiskerRight
attribute [reassoc] PremonoidalCategory.whiskerLeft_comp PremonoidalCategory.comp_whiskerRight
attribute [reassoc] PremonoidalCategory.associator_naturality_left
  PremonoidalCategory.associator_naturality_middle
  PremonoidalCategory.associator_naturality_right
  PremonoidalCategory.leftUnitor_naturality PremonoidalCategory.rightUnitor_naturality
attribute [reassoc (attr := simp)] PremonoidalCategory.pentagon PremonoidalCategory.triangle

namespace PremonoidalCategory

variable {C : Type u} [Category.{v} C] [PremonoidalCategory C]

@[simp] theorem leftTensor_id (X Y : C) : (𝟙 X) ⋉ (𝟙 Y) = 𝟙 (X ⊗ Y) := by
  simp [leftTensor]

@[simp] theorem rightTensor_id (X Y : C) : (𝟙 X) ⋊ (𝟙 Y) = 𝟙 (X ⊗ Y) := by
  simp [rightTensor]

theorem isCentral_id (X : C) : IsCentral (𝟙 X) := by
  constructor <;> intro X' Y' g <;> simp [leftTensor, rightTensor]

theorem IsCentral.comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsCentral f) (hg : IsCentral g) : IsCentral (f ≫ g) := by
  constructor
  · intro X' Y' h
    have hf' : f ▷ X' ≫ Y ◁ h = X ◁ h ≫ f ▷ Y' := by
      simpa only [leftTensor, rightTensor] using hf.1 h
    have hg' : g ▷ X' ≫ Z ◁ h = Y ◁ h ≫ g ▷ Y' := by
      simpa only [leftTensor, rightTensor] using hg.1 h
    simp only [leftTensor, rightTensor, PremonoidalCategory.comp_whiskerRight,
      Category.assoc]
    rw [hg', ← Category.assoc, hf', Category.assoc]
  · intro X' Y' h
    have hf' : h ▷ X ≫ Y' ◁ f = X' ◁ f ≫ h ▷ Y := by
      simpa only [leftTensor, rightTensor] using hf.2 h
    have hg' : h ▷ Y ≫ Y' ◁ g = X' ◁ g ≫ h ▷ Z := by
      simpa only [leftTensor, rightTensor] using hg.2 h
    simp only [leftTensor, rightTensor, PremonoidalCategory.whiskerLeft_comp,
      Category.assoc]
    rw [← Category.assoc, hf', Category.assoc, hg']

end PremonoidalCategory

end CategoryTheory
