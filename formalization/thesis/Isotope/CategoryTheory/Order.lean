import Mathlib.CategoryTheory.Monoidal.Category
import Isotope.CategoryTheory.AddMonoidal.Cocartesian

/-! # Categories locally enriched in orders -/

universe v u

namespace CategoryTheory

open scoped MonoidalCategory AddMonoidalCategory

/-- A category enriched in preorders: every hom-set is preordered and
composition is monotone in both arguments. -/
class LocallyPreorderedCategory (C : Type u) [Category.{v} C] where
  homPreorder (X Y : C) : Preorder (X ⟶ Y)
  comp_mono {W X Y : C} {f f' : W ⟶ X} {g g' : X ⟶ Y} :
    f ≤ f' → g ≤ g' → f ≫ g ≤ f' ≫ g'

@[reducible] instance locallyPreorderedHom
    {C : Type u} [Category.{v} C] [LocallyPreorderedCategory C] (X Y : C) :
    Preorder (X ⟶ Y) := LocallyPreorderedCategory.homPreorder X Y

namespace LocallyPreorderedCategory

variable {C : Type u} [Category.{v} C] [LocallyPreorderedCategory C]

theorem comp_mono_left {X Y Z : C} {f f' : X ⟶ Y} (h : f ≤ f') (g : Y ⟶ Z) :
    f ≫ g ≤ f' ≫ g := comp_mono h le_rfl

theorem comp_mono_right {X Y Z : C} (f : X ⟶ Y) {g g' : Y ⟶ Z} (h : g ≤ g') :
    f ≫ g ≤ f ≫ g' := comp_mono le_rfl h

end LocallyPreorderedCategory

/-- A locally preordered category whose hom preorders are antisymmetric. -/
class LocallyOrderedCategory (C : Type u) [Category.{v} C]
    extends LocallyPreorderedCategory C where
  hom_antisymm {X Y : C} {f g : X ⟶ Y} : f ≤ g → g ≤ f → f = g

instance {C : Type u} [Category.{v} C] [LocallyOrderedCategory C] (X Y : C) :
    PartialOrder (X ⟶ Y) where
  le := (LocallyPreorderedCategory.homPreorder X Y).le
  lt := fun f g =>
    (LocallyPreorderedCategory.homPreorder X Y).le f g ∧
      ¬ (LocallyPreorderedCategory.homPreorder X Y).le g f
  le_refl := (LocallyPreorderedCategory.homPreorder X Y).le_refl
  le_trans := (LocallyPreorderedCategory.homPreorder X Y).le_trans
  le_antisymm := fun _ _ => LocallyOrderedCategory.hom_antisymm
  lt_iff_le_not_ge := fun _ _ => Iff.rfl

/-- Ordinary monoidal tensoring is locally monotone. -/
class OrderedMonoidalCategory (C : Type u) [Category.{v} C]
    [LocallyPreorderedCategory C] [MonoidalCategoryStruct C] : Prop where
  whiskerLeft_mono (X : C) {Y Z : C} {f g : Y ⟶ Z} : f ≤ g → X ◁ f ≤ X ◁ g
  whiskerRight_mono {X Y : C} {f g : X ⟶ Y} (Z : C) : f ≤ g → f ▷ Z ≤ g ▷ Z
  tensorHom_mono {X Y X' Y' : C} {f f' : X ⟶ Y} {g g' : X' ⟶ Y'} :
    f ≤ f' → g ≤ g' → f ⊗ₘ g ≤ f' ⊗ₘ g'

namespace OrderedMonoidalCategory

open scoped MonoidalCategory
variable {C : Type u} [Category.{v} C] [LocallyPreorderedCategory C]
  [MonoidalCategoryStruct C] [OrderedMonoidalCategory C]

end OrderedMonoidalCategory

/-- Additively written monoidal tensoring is locally monotone. -/
class OrderedAddMonoidalCategory (C : Type u) [Category.{v} C]
    [LocallyPreorderedCategory C] [AddMonoidalCategoryStruct C] : Prop where
  addWhiskerLeft_mono (X : C) {Y Z : C} {f g : Y ⟶ Z} :
    f ≤ g → X ◁⁺ f ≤ X ◁⁺ g
  addWhiskerRight_mono {X Y : C} {f g : X ⟶ Y} (Z : C) :
    f ≤ g → f ▷⁺ Z ≤ g ▷⁺ Z
  addHom_mono {X Y X' Y' : C} {f f' : X ⟶ Y} {g g' : X' ⟶ Y'} :
    f ≤ f' → g ≤ g' → f ⊕ₕ g ≤ f' ⊕ₕ g'

namespace OrderedAddMonoidalCategory

open scoped AddMonoidalCategory
variable {C : Type u} [Category.{v} C] [LocallyPreorderedCategory C]
  [AddMonoidalCategoryStruct C] [OrderedAddMonoidalCategory C]

end OrderedAddMonoidalCategory

/-- Compatibility of the chosen coproduct copairing with local order. -/
class OrderedCocartesianMonoidalCategory (C : Type u) [Category.{v} C]
    [LocallyPreorderedCategory C] [AddMonoidalCategory C]
    [CocartesianMonoidalCategory C] : Prop extends OrderedAddMonoidalCategory C where
  desc_mono {T X Y : C} {f f' : X ⟶ T} {g g' : Y ⟶ T} :
    f ≤ f' → g ≤ g' → CocartesianMonoidalCategory.desc f g ≤
      CocartesianMonoidalCategory.desc f' g'

end CategoryTheory
