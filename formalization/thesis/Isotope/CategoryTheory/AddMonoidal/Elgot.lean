import Isotope.CategoryTheory.AddMonoidal.Kleisli
import Isotope.CategoryTheory.Freyd.Elgot

/-!
# Elgot structure over a chosen coproduct

`AddIteration` and `AddElgotCategory` are the iteration operator and the Conway/Elgot equations
stated over the *chosen* coproduct `⊕ₘ`, rather than over `Limits.coprod`.  For the Kleisli
category of an Elgot monad the operator is then literally the monad's `iter`, with no comparison
isomorphism in sight — compare `CategoryTheory.Kleisli.Type.iterate`, which has to conjugate by
`coprodIsoSum`.

The two presentations are related in both directions by `AddIteration.ofIteration` and
`Iteration.ofAddIteration`, and pointwise for the Kleisli category by `iterate_eq_addIterate`.
-/

universe v u

namespace CategoryTheory

open Category Limits
open scoped AddMonoidalCategory

/-- An iteration operator for the chosen coproduct: `f : X ⟶ Y ⊕ₘ X` either returns or loops. -/
class AddIteration (C : Type u) [Category.{v} C] [AddMonoidalCategoryStruct C] where
  addIterate {X Y : C} : (X ⟶ Y ⊕ₘ X) → (X ⟶ Y)

export AddIteration (addIterate)

namespace CocartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CocartesianMonoidalCategory C]

/-- The functorial action of the chosen coproduct on morphisms, via the injections. -/
def addMap {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') : X ⊕ₘ X' ⟶ Y ⊕ₘ Y' :=
  desc (f ≫ inl Y Y') (g ≫ inr Y Y')

@[reassoc (attr := simp)] lemma inl_addMap {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    inl X X' ≫ addMap f g = f ≫ inl Y Y' := by simp [addMap]

@[reassoc (attr := simp)] lemma inr_addMap {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    inr X X' ≫ addMap f g = g ≫ inr Y Y' := by simp [addMap]

end CocartesianMonoidalCategory

open CocartesianMonoidalCategory

/-- The Conway/complete-Elgot equations over the chosen coproduct. -/
class AddElgotCategory (C : Type u) [Category.{v} C] [CocartesianMonoidalCategory C]
    [AddIteration C] : Prop where
  addIterate_fixpoint {X Y : C} (f : X ⟶ Y ⊕ₘ X) :
    addIterate f = f ≫ desc (𝟙 Y) (addIterate f)
  addIterate_naturality {X Y Z : C} (f : X ⟶ Y ⊕ₘ X) (g : Y ⟶ Z) :
    addIterate f ≫ g = addIterate (f ≫ addMap g (𝟙 X))
  addIterate_codiagonal {X Y : C} (f : X ⟶ (Y ⊕ₘ X) ⊕ₘ X) :
    addIterate (addIterate f) = addIterate (f ≫ desc (𝟙 (Y ⊕ₘ X)) (inr Y X))

/-! ### Transporting between the two coproducts -/

section Transport

variable (C : Type u) [Category.{v} C] [CocartesianMonoidalCategory C]

/-- An iteration operator for Mathlib's coproduct induces one for the chosen coproduct. -/
noncomputable def AddIteration.ofIteration [Iteration C] : AddIteration C where
  addIterate f := iterate (f ≫ (addObjIsoCoprod _ _).hom)

/-- Conversely, a chosen-coproduct iteration operator induces one for Mathlib's. -/
noncomputable def Iteration.ofAddIteration [AddIteration C] : Iteration C where
  iterate f := addIterate (f ≫ (addObjIsoCoprod _ _).inv)

end Transport

/-! ### Kleisli categories of Elgot monads -/

namespace Kleisli.Type

variable (m : Type u → Type u) [_root_.Monad m] [LawfulMonad m]

open Isotope.Elgot

/-- **The Kleisli category of an Elgot monad iterates over the chosen coproduct**, and the
operator is the monad's own `iter`: no comparison isomorphism appears. -/
instance addIteration [Iterate m] : AddIteration (Kleisli (TM m)) where
  addIterate := fun {X Y} f =>
    Kleisli.Hom.mk (Isotope.Elgot.iter (m := m) (f.of : X.of → m (Y.of ⊕ X.of)))

@[simp] theorem addIterate_of [Iterate m] {X Y : Kleisli (TM m)} (f : X ⟶ Y ⊕ₘ X) :
    (addIterate f).of =
      ((Isotope.Elgot.iter (m := m) (f.of : X.of → m (Y.of ⊕ X.of))) : X.of → m Y.of) := rfl

/-- **Every complete Elgot monad gives an Elgot category over the chosen coproduct.** -/
instance addElgotCategory [Iterate m] [LawfulElgotMonad m] :
    AddElgotCategory (Kleisli (TM m)) where
  addIterate_fixpoint f := by
    apply Kleisli.hom_ext
    funext x
    simp only [addIterate_of, comp_of' m, desc_of, id_of']
    exact congrFun (LawfulElgotMonad.fixpoint (m := m) (f.of : _ → m _)) x
  addIterate_naturality f g := by
    apply Kleisli.hom_ext
    have hbody : ((f ≫ addMap g (𝟙 _)).of : _ → m _) =
        mapReturn (m := m) (f.of : _ → m _) (g.of : _ → m _) := by
      funext x
      simp only [addMap, comp_of', desc_of, id_of', inl_of, inr_of, mapReturn,
        Function.comp_def]
      congr 1
      funext s
      cases s with
      | inl y => simp
      | inr x' => simp
    simp only [comp_of', addIterate_of, hbody]
    exact LawfulElgotMonad.naturality (m := m) (f.of : _ → m _) (g.of : _ → m _)
  addIterate_codiagonal f := by
    have hbody : ((f ≫ CocartesianMonoidalCategory.desc (𝟙 _)
          (CocartesianMonoidalCategory.inr _ _)).of : _ → m _) =
        Isotope.Elgot.flattenBody (m := m) (f.of : _ → m _) := by
      rw [comp_of']
      funext a
      simp only [desc_of, id_of', inr_of, Isotope.Elgot.flattenBody, Isotope.Elgot.kcomp,
        Isotope.Elgot.liftPure, Isotope.Elgot.flatten, Function.comp_def]
      congr 1
      funext s
      cases s <;> rfl
    apply Kleisli.hom_ext
    rw [addIterate_of, addIterate_of, addIterate_of, hbody]
    exact Isotope.Elgot.LawfulElgotMonad.codiagonal (m := m) (f.of : _ → m _)

/-! ### Relating the two iteration operators -/

/-- The `⨿`-based iteration operator of `Isotope.CategoryTheory.Monad.Elgot` is the chosen one,
transported along the comparison isomorphism. -/
theorem iterate_eq_addIterate [Iterate m] {X Y : Kleisli (TM m)} (f : X ⟶ Y ⨿ X) :
    iterate f = addIterate (f ≫ (addObjIsoCoprod Y X).inv) := by
  apply Kleisli.hom_ext
  rw [addObjIsoCoprod_eq]
  rfl

/-- …and conversely. -/
theorem addIterate_eq_iterate [Iterate m] {X Y : Kleisli (TM m)} (f : X ⟶ Y ⊕ₘ X) :
    addIterate f = iterate (f ≫ (addObjIsoCoprod Y X).hom) := by
  rw [iterate_eq_addIterate, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Kleisli.Type

end CategoryTheory
