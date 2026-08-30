import Isotope.CategoryTheory.Freyd.Basic
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Distributive Freyd categories

This file keeps the two roles of coproducts explicit:

* the value category has finite coproducts and its cartesian tensor distributes over them;
* the computation category has finite coproducts of arbitrary computation morphisms, with
  central injections, and its premonoidal tensor distributes over them;
* the value-to-computation functor preserves finite coproducts.

Crucially, distributivity uses only one-variable whiskering.  It does not assert an interchange
law for two arbitrary computation morphisms.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits
open scoped MonoidalCategory

namespace DistributiveTensor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategoryStruct C]
  [HasBinaryCoproducts C]

/-- The canonical left distributor.  Its two branches only whisker a coproduct injection by a
fixed object, so this definition makes sense without a bifunctorial tensor on morphisms. -/
noncomputable def leftHom (X Y Z : C) :
    (X ⊗ Y) ⨿ (X ⊗ Z) ⟶ X ⊗ (Y ⨿ Z) :=
  coprod.desc (X ◁ (coprod.inl : Y ⟶ Y ⨿ Z)) (X ◁ (coprod.inr : Z ⟶ Y ⨿ Z))

/-- The canonical right distributor. -/
noncomputable def rightHom (X Y Z : C) :
    (X ⊗ Z) ⨿ (Y ⊗ Z) ⟶ (X ⨿ Y) ⊗ Z :=
  coprod.desc ((coprod.inl : X ⟶ X ⨿ Y) ▷ Z) ((coprod.inr : Y ⟶ X ⨿ Y) ▷ Z)

@[reassoc (attr := simp)] theorem inl_leftHom (X Y Z : C) :
    (coprod.inl : X ⊗ Y ⟶ (X ⊗ Y) ⨿ (X ⊗ Z)) ≫ leftHom X Y Z =
      X ◁ (coprod.inl : Y ⟶ Y ⨿ Z) := by
  exact coprod.inl_desc _ _

@[reassoc (attr := simp)] theorem inr_leftHom (X Y Z : C) :
    (coprod.inr : X ⊗ Z ⟶ (X ⊗ Y) ⨿ (X ⊗ Z)) ≫ leftHom X Y Z =
      X ◁ (coprod.inr : Z ⟶ Y ⨿ Z) := by
  exact coprod.inr_desc _ _

@[reassoc (attr := simp)] theorem inl_rightHom (X Y Z : C) :
    (coprod.inl : X ⊗ Z ⟶ (X ⊗ Z) ⨿ (Y ⊗ Z)) ≫ rightHom X Y Z =
      (coprod.inl : X ⟶ X ⨿ Y) ▷ Z := by
  exact coprod.inl_desc _ _

@[reassoc (attr := simp)] theorem inr_rightHom (X Y Z : C) :
    (coprod.inr : Y ⊗ Z ⟶ (X ⊗ Z) ⨿ (Y ⊗ Z)) ≫ rightHom X Y Z =
      (coprod.inr : Y ⟶ X ⨿ Y) ▷ Z := by
  exact coprod.inr_desc _ _

end DistributiveTensor

/-- A tensor distributes over binary coproducts on the left.  This is the distributor used to
thread an unchanged environment into the branches of a `case` or `iter`.  In the symmetric
setting the right distributor follows by conjugating with the braiding, so it is deliberately
not an additional field.  The class only talks about objects, one-variable whiskering, and the
universal property of coproducts. -/
class DistributiveTensor (C : Type u₁) [Category.{v₁} C] [MonoidalCategoryStruct C]
    [HasBinaryCoproducts C] : Prop where
  left_isIso (X Y Z : C) : IsIso (DistributiveTensor.leftHom X Y Z) := by infer_instance

namespace DistributiveTensor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategoryStruct C]
  [HasBinaryCoproducts C] [DistributiveTensor C]

attribute [instance] DistributiveTensor.left_isIso

/-- The chosen left distributor isomorphism. -/
noncomputable def leftIso (X Y Z : C) :
    (X ⊗ Y) ⨿ (X ⊗ Z) ≅ X ⊗ (Y ⨿ Z) :=
  asIso (leftHom X Y Z)

/-- Conventional notation for the left distributor isomorphism. -/
scoped notation "∂L" => DistributiveTensor.leftIso

end DistributiveTensor

/-- Distributive premonoidal computations additionally require the coproduct injections to be
central.  This is exactly what lets case distinctions count as pure structural control flow. -/
class DistributivePremonoidalCategory (C : Type u₁) [Category.{v₁} C]
    [PremonoidalCategory C] [HasFiniteCoproducts C] : Prop extends DistributiveTensor C where
  inl_central {X Y : C} :
    PremonoidalCategory.IsCentral (coprod.inl : X ⟶ X ⨿ Y) := by cat_disch
  inr_central {X Y : C} :
    PremonoidalCategory.IsCentral (coprod.inr : Y ⟶ X ⨿ Y) := by cat_disch

namespace DistributivePremonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [PremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributivePremonoidalCategory C]

theorem central_inl {X Y : C} :
    PremonoidalCategory.IsCentral (coprod.inl : X ⟶ X ⨿ Y) :=
  DistributivePremonoidalCategory.inl_central

theorem central_inr {X Y : C} :
    PremonoidalCategory.IsCentral (coprod.inr : Y ⟶ X ⨿ Y) :=
  DistributivePremonoidalCategory.inr_central

section Symmetric

variable [SymmetricPremonoidalCategory C]

/-- In a symmetric premonoidal category, right distributivity is obtained from left
distributivity by conjugating with the braiding. -/
noncomputable def rightIsoViaBraiding (X Y Z : C) :
    (X ⊗ Z) ⨿ (Y ⊗ Z) ≅ (X ⨿ Y) ⊗ Z :=
  (coprod.mapIso (BraidedPremonoidalCategory.braiding X Z)
      (BraidedPremonoidalCategory.braiding Y Z)).trans
    ((DistributiveTensor.leftIso Z X Y).trans
      (BraidedPremonoidalCategory.braiding Z (X ⨿ Y)))

@[reassoc] theorem rightIsoViaBraiding_hom (X Y Z : C) :
    (rightIsoViaBraiding X Y Z).hom = DistributiveTensor.rightHom X Y Z := by
  apply coprod.hom_ext
  · calc
      coprod.inl ≫ (rightIsoViaBraiding X Y Z).hom =
          (BraidedPremonoidalCategory.braiding X Z).hom ≫
            Z ◁ (coprod.inl : X ⟶ X ⨿ Y) ≫
              (BraidedPremonoidalCategory.braiding Z (X ⨿ Y)).hom := by
                simp [rightIsoViaBraiding, coprod.mapIso, DistributiveTensor.leftIso]
      _ = (BraidedPremonoidalCategory.braiding X Z).hom ≫
            (BraidedPremonoidalCategory.braiding Z X).hom ≫
              (coprod.inl : X ⟶ X ⨿ Y) ▷ Z := by
                rw [BraidedPremonoidalCategory.naturality_right]
      _ = (coprod.inl : X ⟶ X ⨿ Y) ▷ Z := by simp
      _ = coprod.inl ≫ DistributiveTensor.rightHom X Y Z :=
        (DistributiveTensor.inl_rightHom X Y Z).symm
  · calc
      coprod.inr ≫ (rightIsoViaBraiding X Y Z).hom =
          (BraidedPremonoidalCategory.braiding Y Z).hom ≫
            Z ◁ (coprod.inr : Y ⟶ X ⨿ Y) ≫
              (BraidedPremonoidalCategory.braiding Z (X ⨿ Y)).hom := by
                simp [rightIsoViaBraiding, coprod.mapIso, DistributiveTensor.leftIso]
      _ = (BraidedPremonoidalCategory.braiding Y Z).hom ≫
            (BraidedPremonoidalCategory.braiding Z Y).hom ≫
              (coprod.inr : Y ⟶ X ⨿ Y) ▷ Z := by
                rw [BraidedPremonoidalCategory.naturality_right]
      _ = (coprod.inr : Y ⟶ X ⨿ Y) ▷ Z := by simp
      _ = coprod.inr ≫ DistributiveTensor.rightHom X Y Z :=
        (DistributiveTensor.inr_rightHom X Y Z).symm

instance rightHom_isIso (X Y Z : C) :
    IsIso (DistributiveTensor.rightHom X Y Z) := by
  rw [← rightIsoViaBraiding_hom]
  infer_instance

/-- The right distributor, derived rather than required as an independent law. -/
noncomputable def rightIso (X Y Z : C) :
    (X ⊗ Z) ⨿ (Y ⊗ Z) ≅ (X ⨿ Y) ⊗ Z :=
  asIso (DistributiveTensor.rightHom X Y Z)

/-- Conventional notation for the symmetry-derived right distributor isomorphism. -/
scoped notation "∂R" => DistributivePremonoidalCategory.rightIso

/-- Inverse of the left distributor, used to thread an environment into coproduct branches. -/
noncomputable abbrev leftInv (X Y Z : C) :
    X ⊗ (Y ⨿ Z) ⟶ (X ⊗ Y) ⨿ (X ⊗ Z) :=
  (DistributiveTensor.leftIso X Y Z).inv

/-- Inverse of the symmetry-derived right distributor. -/
noncomputable abbrev rightInv (X Y Z : C) :
    (X ⨿ Y) ⊗ Z ⟶ (X ⊗ Z) ⨿ (Y ⊗ Z) :=
  (rightIso X Y Z).inv

end Symmetric

end DistributivePremonoidalCategory

/-- A distributive Freyd category has distributive finite coproducts both for values and for
computations, and the inclusion of values preserves them. -/
class DistributiveFreydCategory {V : Type u₁} {C : Type u₂}
    [Category.{v₁} V] [Category.{v₂} C]
    [CartesianMonoidalCategory V] [SymmetricCategory V]
    [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
    [HasFiniteCoproducts V] [HasFiniteCoproducts C]
    [DistributiveTensor V] [DistributivePremonoidalCategory C]
    (J : Functor V C) extends FreydCategory J where
  preservesFiniteCoproducts : PreservesFiniteCoproducts J := by infer_instance

namespace DistributiveFreydCategory

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : Functor V C) [DistributiveFreydCategory J]

instance : PreservesFiniteCoproducts J :=
  DistributiveFreydCategory.preservesFiniteCoproducts

end DistributiveFreydCategory

end CategoryTheory
