import Isotope.CategoryTheory.Monad.Strong
import Isotope.CategoryTheory.Premonoidal.Basic
import Isotope.CategoryTheory.Premonoidal.Symmetric

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

theorem associator_naturality_left {X Y : Kleisli T} (f : X ⟶ Y)
    (Z W : Kleisli T) :
    ((f ▷ Z) ▷ W) ≫ (α_ Y Z W).hom =
      (α_ X Z W).hom ≫ f ▷ (Z ⊗ W) := by
  apply Kleisli.hom_ext
  change (((f ▷ Z) ▷ W) ≫
      (Kleisli.Adjunction.toKleisli T).map (α_ Y.of Z.of W.of).hom).of = _
  rw [comp_toKleisli_map]
  change _ = ((Kleisli.Adjunction.toKleisli T).map
      (α_ X.of Z.of W.of).hom ≫ f ▷ (Z ⊗ W)).of
  rw [toKleisli_map_comp]
  dsimp [whiskerRight]
  rw [MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc]
  rw [Monad.Strong.costrength_associativity]
  rw [MonoidalCategory.associator_naturality_left_assoc]

theorem associator_naturality_middle (X : Kleisli T) {Y Z : Kleisli T}
    (f : Y ⟶ Z) (W : Kleisli T) :
    ((X ◁ f) ▷ W) ≫ (α_ X Z W).hom =
      (α_ X Y W).hom ≫ X ◁ (f ▷ W) := by
  apply Kleisli.hom_ext
  change (((X ◁ f) ▷ W) ≫
      (Kleisli.Adjunction.toKleisli T).map (α_ X.of Z.of W.of).hom).of = _
  rw [comp_toKleisli_map]
  change _ = ((Kleisli.Adjunction.toKleisli T).map
      (α_ X.of Y.of W.of).hom ≫ X ◁ (f ▷ W)).of
  rw [toKleisli_map_comp]
  dsimp [whiskerLeft, whiskerRight]
  rw [MonoidalCategory.comp_whiskerRight]
  rw [MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [Monad.Strong.strength_costrength_associativity]
  rw [MonoidalCategory.associator_naturality_middle_assoc]

theorem leftUnitor_naturality {X Y : Kleisli T} (f : X ⟶ Y) :
    𝟙_ (Kleisli T) ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by
  apply Kleisli.hom_ext
  change ((𝟙_ (Kleisli T) ◁ f) ≫
      (Kleisli.Adjunction.toKleisli T).map (λ_ Y.of).hom).of = _
  rw [comp_toKleisli_map]
  change _ = ((Kleisli.Adjunction.toKleisli T).map (λ_ X.of).hom ≫ f).of
  rw [toKleisli_map_comp]
  dsimp [whiskerLeft]
  have hunit := Monad.Strong.left_unitality (T := T) Y.of
  slice_lhs 2 3 => exact hunit
  rw [MonoidalCategory.leftUnitor_naturality]

theorem rightUnitor_naturality {X Y : Kleisli T} (f : X ⟶ Y) :
    f ▷ 𝟙_ (Kleisli T) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
  apply Kleisli.hom_ext
  change ((f ▷ 𝟙_ (Kleisli T)) ≫
      (Kleisli.Adjunction.toKleisli T).map (ρ_ Y.of).hom).of = _
  rw [comp_toKleisli_map]
  change _ = ((Kleisli.Adjunction.toKleisli T).map (ρ_ X.of).hom ≫ f).of
  rw [toKleisli_map_comp]
  dsimp [whiskerRight]
  have hunit := Monad.Strong.costrength_right_unitality (T := T) Y.of
  slice_lhs 2 3 => exact hunit
  rw [MonoidalCategory.rightUnitor_naturality]

theorem pentagon (W X Y Z : Kleisli T) : MonoidalCategory.Pentagon W X Y Z := by
  dsimp [MonoidalCategory.Pentagon]
  change ((Kleisli.Adjunction.toKleisli T).map (α_ W.of X.of Y.of).hom ▷ Z) ≫
      (Kleisli.Adjunction.toKleisli T).map (α_ W.of (X.of ⊗ Y.of) Z.of).hom ≫
      W ◁ (Kleisli.Adjunction.toKleisli T).map (α_ X.of Y.of Z.of).hom =
    (Kleisli.Adjunction.toKleisli T).map (α_ (W.of ⊗ X.of) Y.of Z.of).hom ≫
      (Kleisli.Adjunction.toKleisli T).map (α_ W.of X.of (Y.of ⊗ Z.of)).hom
  rw [toKleisli_map_whiskerRight]
  have hw := whiskerLeft_toKleisli_map T W (α_ X.of Y.of Z.of).hom
  calc
    _ = (Kleisli.Adjunction.toKleisli T).map ((α_ W.of X.of Y.of).hom ▷ Z.of) ≫
        (Kleisli.Adjunction.toKleisli T).map (α_ W.of (X.of ⊗ Y.of) Z.of).hom ≫
        (Kleisli.Adjunction.toKleisli T).map (W.of ◁ (α_ X.of Y.of Z.of).hom) := by
      exact congrArg
        (fun q ↦ (Kleisli.Adjunction.toKleisli T).map
          ((α_ W.of X.of Y.of).hom ▷ Z.of) ≫
          (Kleisli.Adjunction.toKleisli T).map
            (α_ W.of (X.of ⊗ Y.of) Z.of).hom ≫ q) hw
    _ = _ := by
      simpa only [Functor.map_comp] using congrArg
        (fun h ↦ (Kleisli.Adjunction.toKleisli T).map h)
        (MonoidalCategory.pentagon W.of X.of Y.of Z.of)

theorem triangle (X Y : Kleisli T) :
    (α_ X (𝟙_ (Kleisli T)) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y := by
  change (Kleisli.Adjunction.toKleisli T).map (α_ X.of (𝟙_ C) Y.of).hom ≫
      X ◁ (Kleisli.Adjunction.toKleisli T).map (λ_ Y.of).hom =
    (Kleisli.Adjunction.toKleisli T).map (ρ_ X.of).hom ▷ Y
  have hx := whiskerLeft_toKleisli_map T X (λ_ Y.of).hom
  have hr := toKleisli_map_whiskerRight T (ρ_ X.of).hom Y
  calc
    _ = (Kleisli.Adjunction.toKleisli T).map (α_ X.of (𝟙_ C) Y.of).hom ≫
        (Kleisli.Adjunction.toKleisli T).map (X.of ◁ (λ_ Y.of).hom) :=
      congrArg ((Kleisli.Adjunction.toKleisli T).map
        (α_ X.of (𝟙_ C) Y.of).hom ≫ ·) hx
    _ = (Kleisli.Adjunction.toKleisli T).map ((ρ_ X.of).hom ▷ Y.of) := by
      simpa only [Functor.map_comp] using congrArg
        (fun h ↦ (Kleisli.Adjunction.toKleisli T).map h)
        (MonoidalCategory.triangle X.of Y.of)
    _ = _ := hr.symm

instance premonoidalCategory : PremonoidalCategory (Kleisli T) where
  tensorHom_def _ _ := rfl
  whiskerLeft_id := whiskerLeft_id T
  whiskerLeft_comp := whiskerLeft_comp T
  id_whiskerRight := id_whiskerRight T
  comp_whiskerRight := comp_whiskerRight T
  associator_central := associator_hom_isCentral T
  leftUnitor_central := leftUnitor_hom_isCentral T
  rightUnitor_central := rightUnitor_hom_isCentral T
  associator_naturality_left := associator_naturality_left T
  associator_naturality_middle := associator_naturality_middle T
  associator_naturality_right := associator_naturality_right T
  leftUnitor_naturality := leftUnitor_naturality T
  rightUnitor_naturality := rightUnitor_naturality T
  pentagon := pentagon T
  triangle := triangle T

def braidingIso (X Y : Kleisli T) : X ⊗ Y ≅ Y ⊗ X :=
  (Kleisli.Adjunction.toKleisli T).mapIso
    (BraidedCategory.braiding X.of Y.of)

theorem braiding_naturality_left {X Y : Kleisli T} (f : X ⟶ Y) (Z : Kleisli T) :
    f ▷ Z ≫ (braidingIso T Y Z).hom =
      (braidingIso T X Z).hom ≫ Z ◁ f := by
  apply Kleisli.hom_ext
  change ((f ▷ Z) ≫ (Kleisli.Adjunction.toKleisli T).map
      (BraidedCategory.braiding Y.of Z.of).hom).of = _
  rw [comp_toKleisli_map]
  change _ = ((Kleisli.Adjunction.toKleisli T).map
      (BraidedCategory.braiding X.of Z.of).hom ≫ Z ◁ f).of
  rw [toKleisli_map_comp]
  dsimp [whiskerRight, whiskerLeft, Monad.Strong.costrength]
  simp only [Category.assoc]
  have hcancel :
      T.map (BraidedCategory.braiding Z.of Y.of).hom ≫
        T.map (BraidedCategory.braiding Y.of Z.of).hom = 𝟙 _ := by
    rw [← Functor.map_comp, SymmetricCategory.symmetry, Functor.map_id]
  slice_lhs 4 5 => exact hcancel
  rw [BraidedCategory.braiding_naturality_left_assoc]
  simp only [Category.comp_id]

theorem braiding_naturality_right (X : Kleisli T) {Y Z : Kleisli T} (f : Y ⟶ Z) :
    X ◁ f ≫ (braidingIso T X Z).hom =
      (braidingIso T X Y).hom ≫ f ▷ X := by
  apply Kleisli.hom_ext
  change ((X ◁ f) ≫ (Kleisli.Adjunction.toKleisli T).map
      (BraidedCategory.braiding X.of Z.of).hom).of = _
  rw [comp_toKleisli_map]
  change _ = ((Kleisli.Adjunction.toKleisli T).map
      (BraidedCategory.braiding X.of Y.of).hom ≫ f ▷ X).of
  rw [toKleisli_map_comp]
  dsimp [whiskerRight, whiskerLeft, Monad.Strong.costrength]
  simp only [Category.assoc]
  have hbraid := (BraidedCategory.braiding_naturality_right X.of f.of).symm
  slice_rhs 1 2 => exact hbraid
  have hcancel :
      (BraidedCategory.braiding X.of (T.obj Z.of)).hom ≫
        (BraidedCategory.braiding (T.obj Z.of) X.of).hom = 𝟙 _ :=
    SymmetricCategory.symmetry X.of (T.obj Z.of)
  slice_rhs 2 3 => exact hcancel
  simp only [Category.id_comp]

theorem braiding_hexagon_forward (X Y Z : Kleisli T) :
    (α_ X Y Z).hom ≫ (braidingIso T X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
      (braidingIso T X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫
        Y ◁ (braidingIso T X Z).hom := by
  change (Kleisli.Adjunction.toKleisli T).map (α_ X.of Y.of Z.of).hom ≫
      (Kleisli.Adjunction.toKleisli T).map
        (BraidedCategory.braiding X.of (Y.of ⊗ Z.of)).hom ≫
      (Kleisli.Adjunction.toKleisli T).map (α_ Y.of Z.of X.of).hom =
    ((Kleisli.Adjunction.toKleisli T).map
        (BraidedCategory.braiding X.of Y.of).hom ▷ Z) ≫
      (Kleisli.Adjunction.toKleisli T).map (α_ Y.of X.of Z.of).hom ≫
      Y ◁ (Kleisli.Adjunction.toKleisli T).map
        (BraidedCategory.braiding X.of Z.of).hom
  have hr := toKleisli_map_whiskerRight T
    (BraidedCategory.braiding X.of Y.of).hom Z
  have hl := whiskerLeft_toKleisli_map T Y
    (BraidedCategory.braiding X.of Z.of).hom
  calc
    _ = (Kleisli.Adjunction.toKleisli T).map
          ((BraidedCategory.braiding X.of Y.of).hom ▷ Z.of) ≫
        (Kleisli.Adjunction.toKleisli T).map (α_ Y.of X.of Z.of).hom ≫
        (Kleisli.Adjunction.toKleisli T).map
          (Y.of ◁ (BraidedCategory.braiding X.of Z.of).hom) := by
      simpa only [Functor.map_comp] using congrArg
        (fun h ↦ (Kleisli.Adjunction.toKleisli T).map h)
        (BraidedCategory.hexagon_forward X.of Y.of Z.of)
    _ = ((Kleisli.Adjunction.toKleisli T).map
          (BraidedCategory.braiding X.of Y.of).hom ▷ Z) ≫
        (Kleisli.Adjunction.toKleisli T).map (α_ Y.of X.of Z.of).hom ≫
        (Kleisli.Adjunction.toKleisli T).map
          (Y.of ◁ (BraidedCategory.braiding X.of Z.of).hom) :=
      congrArg (· ≫ (Kleisli.Adjunction.toKleisli T).map
        (α_ Y.of X.of Z.of).hom ≫ (Kleisli.Adjunction.toKleisli T).map
          (Y.of ◁ (BraidedCategory.braiding X.of Z.of).hom)) hr.symm
    _ = _ := congrArg
      (((Kleisli.Adjunction.toKleisli T).map
          (BraidedCategory.braiding X.of Y.of).hom ▷ Z) ≫
        (Kleisli.Adjunction.toKleisli T).map (α_ Y.of X.of Z.of).hom ≫ ·) hl.symm

theorem braiding_hexagon_reverse (X Y Z : Kleisli T) :
    (α_ X Y Z).inv ≫ (braidingIso T (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
      X ◁ (braidingIso T Y Z).hom ≫ (α_ X Z Y).inv ≫
        (braidingIso T X Z).hom ▷ Y := by
  change (Kleisli.Adjunction.toKleisli T).map (α_ X.of Y.of Z.of).inv ≫
      (Kleisli.Adjunction.toKleisli T).map
        (BraidedCategory.braiding (X.of ⊗ Y.of) Z.of).hom ≫
      (Kleisli.Adjunction.toKleisli T).map (α_ Z.of X.of Y.of).inv =
    X ◁ (Kleisli.Adjunction.toKleisli T).map
        (BraidedCategory.braiding Y.of Z.of).hom ≫
      (Kleisli.Adjunction.toKleisli T).map (α_ X.of Z.of Y.of).inv ≫
      ((Kleisli.Adjunction.toKleisli T).map
        (BraidedCategory.braiding X.of Z.of).hom ▷ Y)
  have hl := whiskerLeft_toKleisli_map T X
    (BraidedCategory.braiding Y.of Z.of).hom
  have hr := toKleisli_map_whiskerRight T
    (BraidedCategory.braiding X.of Z.of).hom Y
  calc
    _ = (Kleisli.Adjunction.toKleisli T).map
          (X.of ◁ (BraidedCategory.braiding Y.of Z.of).hom) ≫
        (Kleisli.Adjunction.toKleisli T).map (α_ X.of Z.of Y.of).inv ≫
        (Kleisli.Adjunction.toKleisli T).map
          ((BraidedCategory.braiding X.of Z.of).hom ▷ Y.of) := by
      simpa only [Functor.map_comp] using congrArg
        (fun h ↦ (Kleisli.Adjunction.toKleisli T).map h)
        (BraidedCategory.hexagon_reverse X.of Y.of Z.of)
    _ = (X ◁ (Kleisli.Adjunction.toKleisli T).map
          (BraidedCategory.braiding Y.of Z.of).hom) ≫
        (Kleisli.Adjunction.toKleisli T).map (α_ X.of Z.of Y.of).inv ≫
        (Kleisli.Adjunction.toKleisli T).map
          ((BraidedCategory.braiding X.of Z.of).hom ▷ Y.of) :=
      congrArg (· ≫ (Kleisli.Adjunction.toKleisli T).map
        (α_ X.of Z.of Y.of).inv ≫ (Kleisli.Adjunction.toKleisli T).map
          ((BraidedCategory.braiding X.of Z.of).hom ▷ Y.of)) hl.symm
    _ = _ := congrArg
      ((X ◁ (Kleisli.Adjunction.toKleisli T).map
          (BraidedCategory.braiding Y.of Z.of).hom) ≫
        (Kleisli.Adjunction.toKleisli T).map (α_ X.of Z.of Y.of).inv ≫ ·) hr.symm

theorem braiding_symmetry (X Y : Kleisli T) :
    (braidingIso T X Y).hom ≫ (braidingIso T Y X).hom = 𝟙 (X ⊗ Y) := by
  dsimp [braidingIso]
  calc
    _ = (Kleisli.Adjunction.toKleisli T).map
        ((BraidedCategory.braiding X.of Y.of).hom ≫
          (BraidedCategory.braiding Y.of X.of).hom) :=
      ((Kleisli.Adjunction.toKleisli T).map_comp _ _).symm
    _ = (Kleisli.Adjunction.toKleisli T).map (𝟙 (X.of ⊗ Y.of)) := congrArg
      (fun h ↦ (Kleisli.Adjunction.toKleisli T).map h)
      (SymmetricCategory.symmetry X.of Y.of)
    _ = _ := (Kleisli.Adjunction.toKleisli T).map_id (X.of ⊗ Y.of)

instance symmetricPremonoidalCategory : SymmetricPremonoidalCategory (Kleisli T) where
  braiding := braidingIso T
  naturality_left := braiding_naturality_left T
  naturality_right := braiding_naturality_right T
  hexagon_forward := braiding_hexagon_forward T
  hexagon_reverse := braiding_hexagon_reverse T
  braiding_central X Y := toKleisli_map_isCentral T
    (BraidedCategory.braiding X.of Y.of).hom
  symmetry := braiding_symmetry T

end Kleisli

end CategoryTheory
