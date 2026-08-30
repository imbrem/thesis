import Isotope.CategoryTheory.Premonoidal.Center
import Isotope.CategoryTheory.Premonoidal.Symmetric
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Freyd categories

We package the traditional presentation as an identity-on-objects (up to a specified object
bijection) strong symmetric premonoidal functor from a cartesian value category to a symmetric
premonoidal computation category.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category
open scoped MonoidalCategory

/-- Structure maps and laws for a strong premonoidal functor from a monoidal category into a
premonoidal category. Naturality is stated separately in each argument. -/
class Functor.StrongPremonoidal {V : Type u₁} {C : Type u₂}
    [Category.{v₁} V] [Category.{v₂} C] [MonoidalCategory V] [PremonoidalCategory C]
    (J : Functor V C) where
  unitIso : 𝟙_ C ≅ J.obj (𝟙_ V)
  tensorIso (X Y : V) : J.obj X ⊗ J.obj Y ≅ J.obj (X ⊗ Y)
  tensor_naturality_left {X Y : V} (f : X ⟶ Y) (Z : V) :
      J.map f ▷ J.obj Z ≫ (tensorIso Y Z).hom =
        (tensorIso X Z).hom ≫ J.map (f ▷ Z) := by cat_disch
  tensor_naturality_right (X : V) {Y Z : V} (f : Y ⟶ Z) :
      J.obj X ◁ J.map f ≫ (tensorIso X Z).hom =
        (tensorIso X Y).hom ≫ J.map (X ◁ f) := by cat_disch
  associativity (X Y Z : V) :
      (α_ (J.obj X) (J.obj Y) (J.obj Z)).hom ≫
          J.obj X ◁ (tensorIso Y Z).hom ≫ (tensorIso X (Y ⊗ Z)).hom =
        (tensorIso X Y).hom ▷ J.obj Z ≫ (tensorIso (X ⊗ Y) Z).hom ≫
          J.map (α_ X Y Z).hom := by cat_disch
  left_unitality (X : V) :
      unitIso.hom ▷ J.obj X ≫ (tensorIso (𝟙_ V) X).hom ≫ J.map (λ_ X).hom =
        (λ_ (J.obj X)).hom := by cat_disch
  right_unitality (X : V) :
      J.obj X ◁ unitIso.hom ≫ (tensorIso X (𝟙_ V)).hom ≫ J.map (ρ_ X).hom =
        (ρ_ (J.obj X)).hom := by cat_disch
  map_central {X Y : V} (f : X ⟶ Y) : PremonoidalCategory.IsCentral (J.map f) := by
    cat_disch

/-- A strong symmetric premonoidal functor also preserves the braiding. -/
class Functor.StrongSymmetricPremonoidal {V : Type u₁} {C : Type u₂}
    [Category.{v₁} V] [Category.{v₂} C] [MonoidalCategory V] [SymmetricCategory V]
    [PremonoidalCategory C] [SymmetricPremonoidalCategory C] (J : Functor V C)
    extends Functor.StrongPremonoidal J where
  braiding (X Y : V) :
      (tensorIso X Y).hom ≫ J.map (BraidedCategory.braiding X Y).hom =
        (BraidedPremonoidalCategory.braiding (J.obj X) (J.obj Y)).hom ≫
          (tensorIso Y X).hom := by cat_disch

/-- A Freyd category: cartesian values, symmetric premonoidal computations, and a strong
symmetric premonoidal embedding that is bijective on objects. -/
class FreydCategory {V : Type u₁} {C : Type u₂}
    [Category.{v₁} V] [Category.{v₂} C] [CartesianMonoidalCategory V] [SymmetricCategory V]
    [PremonoidalCategory C] [SymmetricPremonoidalCategory C] (J : Functor V C)
    extends Functor.StrongSymmetricPremonoidal J where
  obj_bijective : Function.Bijective J.obj

namespace FreydCategory

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  (J : Functor V C) [FreydCategory J]

theorem image_central {X Y : V} (f : X ⟶ Y) : PremonoidalCategory.IsCentral (J.map f) :=
  Functor.StrongPremonoidal.map_central f

/-- Value morphisms factor through the center of the computation category. -/
def toCenter : Functor V (PremonoidalCategory.Center C) where
  obj X := ⟨J.obj X⟩
  map f := ⟨J.map f, image_central J f⟩
  map_id X := by apply Subtype.ext; simp
  map_comp f g := by apply Subtype.ext; simp

@[simp] theorem toCenter_obj (X : V) : (toCenter J).obj X = ⟨J.obj X⟩ := rfl
@[simp] theorem toCenter_map {X Y : V} (f : X ⟶ Y) : ((toCenter J).map f).1 = J.map f := rfl

end FreydCategory

end CategoryTheory
