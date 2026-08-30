import Isotope.CategoryTheory.Monad.Strong
import Isotope.CategoryTheory.Premonoidal.Basic

/-! # Premonoidal Kleisli categories of strong monads -/

universe v u

namespace CategoryTheory

open Category
open scoped MonoidalCategory

namespace Kleisli

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  (T : Monad C) [T.Strong] [BraidedCategory C]

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

end Kleisli

end CategoryTheory
