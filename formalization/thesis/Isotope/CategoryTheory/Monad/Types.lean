import Isotope.CategoryTheory.Monad.Kleisli
import Mathlib.CategoryTheory.Monad.Types
import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-! # Every lawful monad on `Type` is strong -/

universe u

namespace CategoryTheory

open Category
open scoped MonoidalCategory

variable (m : Type u → Type u) [_root_.Monad m] [LawfulMonad m]

/-- The canonical tensorial strength of a monad on types. -/
def typeMonadStrength (X Y : Type u) : X × m Y → m (X × Y) :=
  fun p ↦ (fun y ↦ (p.1, y)) <$> p.2

instance ofTypeMonadStrong : (ofTypeMonad m).Strong where
  strength := typeMonadStrength m
  naturality_left f Y := by
    funext p
    simp [typeMonadStrength]
  naturality_right := fun X {_ _} f ↦ by
    funext p
    simp [typeMonadStrength]
  associativity X Y Z := by
    funext p
    simp [typeMonadStrength]
    congr 1
  left_unitality X := by
    funext p
    rcases p with ⟨u, my⟩
    cases u
    simp [typeMonadStrength]
  unit X Y := by
    funext p
    simp [typeMonadStrength]
  multiplication X Y := by
    funext p
    simp [typeMonadStrength, joinM]

@[simp] theorem ofTypeMonad_strength_apply (X Y : Type u) (p : X × m Y) :
    Monad.Strong.strength (T := ofTypeMonad m) X Y p = typeMonadStrength m X Y p := rfl

/-- Kleisli arrows of every lawful monad on `Type` form a premonoidal category. -/
@[reducible] def typeMonadKleisliPremonoidal :
    PremonoidalCategory (Kleisli (ofTypeMonad m)) := inferInstance

/-- Kleisli arrows of every lawful monad on `Type`, together with pure functions, form a Freyd
category. -/
@[reducible] def typeMonadKleisliFreyd :
    FreydCategory (Kleisli.Adjunction.toKleisli (ofTypeMonad m)) := inferInstance

end CategoryTheory
