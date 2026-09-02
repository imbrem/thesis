import Isotope.CategoryTheory.AddMonoidal.Types
import Isotope.CategoryTheory.Monad.Elgot
import Isotope.CategoryTheory.Monad.Effectful

/-!
# Kleisli categories are cocartesian monoidal

A monad on `Type u` preserves coproducts — its Kleisli inclusion is a left adjoint — so the
Kleisli category inherits the chosen coproduct structure of `Type u` on the nose: `X ⊕ₘ Y` is
still `Sum`, and `inl` is still `Sum.inl`, now viewed as a value morphism `pure ∘ Sum.inl`.

That the injections are *values* is the whole point.  With `Limits.HasBinaryCoproducts` the
injections come from `Classical.choice` and nothing can be proved about them; with the chosen
structure they are pure by construction.

The two presentations are related by `addObjIsoCoprod` (to Mathlib's `⨿`) and by
`toKleisli_map_inl` and friends (to the value category `Type u`).
-/

universe u

namespace CategoryTheory

open Category Limits
open scoped AddMonoidalCategory

namespace Kleisli.Type

variable (m : Type u → Type u) [_root_.Monad m] [LawfulMonad m]

/-! ### Computing in the Kleisli category -/

@[simp] theorem id_of' (X : Kleisli (TM m)) :
    (𝟙 X : X ⟶ X).of = fun x => (pure x : m X.of) := rfl

theorem comp_of' {X Y Z : Kleisli (TM m)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).of =
      ((fun x => ((f.of x : m Y.of) >>= (g.of : Y.of → m Z.of))) : X.of → m Z.of) := by
  funext x; simp [joinM, bind_map_left]

@[simp] theorem toKleisli_map_of {X Y : Type u} (f : X → Y) :
    ((Kleisli.Adjunction.toKleisli (TM m)).map f).of = fun x => (pure (f x) : m Y) := rfl

/-! ### The additive monoidal structure -/

/-- The Kleisli category of a monad on `Type u` is additively monoidal, with `Sum` — inherited
from `Type u`, because the Kleisli inclusion is a left adjoint. -/
instance addMonoidalCategory : AddMonoidalCategory (Kleisli (TM m)) where
  addObj X Y := Kleisli.mk (TM m) (X.of ⊕ Y.of)
  addWhiskerLeft := fun X {Y₁ Y₂} f =>
    Kleisli.Hom.mk (Sum.elim
      (fun x => (pure (Sum.inl x) : m (X.of ⊕ Y₂.of)))
      (fun y => ((Sum.inr <$> (f.of y : m Y₂.of)) : m (X.of ⊕ Y₂.of))))
  addWhiskerRight := fun {X₁ X₂} f Y =>
    Kleisli.Hom.mk (Sum.elim
      (fun x => ((Sum.inl <$> (f.of x : m X₂.of)) : m (X₂.of ⊕ Y.of)))
      (fun y => (pure (Sum.inr y) : m (X₂.of ⊕ Y.of))))
  addHom := fun {X₁ Y₁ X₂ Y₂} f g =>
    Kleisli.Hom.mk (Sum.elim
      (fun x => ((Sum.inl <$> (f.of x : m Y₁.of)) : m (Y₁.of ⊕ Y₂.of)))
      (fun y => ((Sum.inr <$> (g.of y : m Y₂.of)) : m (Y₁.of ⊕ Y₂.of))))
  addUnit := Kleisli.mk (TM m) PEmpty
  addAssociator X Y Z :=
    (Kleisli.Adjunction.toKleisli (TM m)).mapIso (Equiv.sumAssoc X.of Y.of Z.of).toIso
  addLeftUnitor X :=
    (Kleisli.Adjunction.toKleisli (TM m)).mapIso (Equiv.emptySum PEmpty X.of).toIso
  addRightUnitor X :=
    (Kleisli.Adjunction.toKleisli (TM m)).mapIso (Equiv.sumEmpty X.of PEmpty).toIso
  addHom_def _ _ := by
    apply Kleisli.hom_ext; funext x; rcases x with x | x <;> simp [joinM, bind_map_left]
  id_addHom_id _ _ := by
    apply Kleisli.hom_ext; funext x; rcases x with x | x <;> simp
  addHom_comp_addHom _ _ _ _ := by
    apply Kleisli.hom_ext; funext x; rcases x with x | x <;> simp [joinM, bind_map_left]
  addWhiskerLeft_id _ _ := by
    apply Kleisli.hom_ext; funext x; rcases x with x | x <;> simp
  id_addWhiskerRight _ _ := by
    apply Kleisli.hom_ext; funext x; rcases x with x | x <;> simp
  addAssociator_naturality _ _ _ := by
    apply Kleisli.hom_ext; funext x; rcases x with (x | x) | x <;>
      simp [joinM, bind_map_left, Equiv.sumAssoc]
  addLeftUnitor_naturality _ := by
    apply Kleisli.hom_ext; funext x
    rcases x with x | x
    · exact x.elim
    · simp [joinM, bind_map_left, Equiv.emptySum]
  addRightUnitor_naturality _ := by
    apply Kleisli.hom_ext; funext x
    rcases x with x | x
    · simp [joinM, bind_map_left, Equiv.sumEmpty]
    · exact x.elim
  addPentagon _ _ _ _ := by
    apply Kleisli.hom_ext; funext x; rcases x with ((x | x) | x) | x <;>
      simp [Equiv.sumAssoc]
  addTriangle _ _ := by
    apply Kleisli.hom_ext; funext x
    rcases x with (x | x) | x
    · simp [Equiv.sumAssoc, Equiv.sumEmpty, Equiv.emptySum]
    · exact x.elim
    · simp [Equiv.sumAssoc, Equiv.sumEmpty, Equiv.emptySum]

@[simp] theorem addObj_of (X Y : Kleisli (TM m)) : (X ⊕ₘ Y).of = (X.of ⊕ Y.of) := rfl

@[simp] theorem addUnit_of : (𝟘_ (Kleisli (TM m))).of = PEmpty := rfl

@[simp] theorem addHom_of {X₁ Y₁ X₂ Y₂ : Kleisli (TM m)} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊕ₕ g).of =
      Sum.elim (fun x => ((Sum.inl <$> (f.of x : m Y₁.of)) : m (Y₁.of ⊕ Y₂.of)))
        (fun y => ((Sum.inr <$> (g.of y : m Y₂.of)) : m (Y₁.of ⊕ Y₂.of))) := rfl

@[simp] theorem addWhiskerLeft_of (X : Kleisli (TM m)) {Y₁ Y₂ : Kleisli (TM m)}
    (f : Y₁ ⟶ Y₂) :
    (X ◁⁺ f).of = Sum.elim (fun x => (pure (Sum.inl x) : m (X.of ⊕ Y₂.of)))
      (fun y => ((Sum.inr <$> (f.of y : m Y₂.of)) : m (X.of ⊕ Y₂.of))) := rfl

@[simp] theorem addWhiskerRight_of {X₁ X₂ : Kleisli (TM m)} (f : X₁ ⟶ X₂)
    (Y : Kleisli (TM m)) :
    (f ▷⁺ Y).of = Sum.elim
      (fun x => ((Sum.inl <$> (f.of x : m X₂.of)) : m (X₂.of ⊕ Y.of)))
      (fun y => (pure (Sum.inr y) : m (X₂.of ⊕ Y.of))) := rfl

@[simp] theorem addRightUnitor_inv_of (X : Kleisli (TM m)) :
    (ρ⁺_ X).inv.of = fun x => (pure (Sum.inl x) : m (X.of ⊕ PEmpty)) := rfl

@[simp] theorem addLeftUnitor_inv_of (X : Kleisli (TM m)) :
    (λ⁺_ X).inv.of = fun x => (pure (Sum.inr x) : m (PEmpty ⊕ X.of)) := rfl

/-! ### The chosen coproduct -/

/-- The Kleisli category of a monad on `Type u` is cocartesian monoidal.  The injections are
`pure ∘ Sum.inl` and `pure ∘ Sum.inr`: *values*, on the nose. -/
instance cocartesianMonoidalCategory : CocartesianMonoidalCategory (Kleisli (TM m)) where
  isInitialAddUnit :=
    IsInitial.ofUniqueHom (fun _ => Kleisli.Hom.mk PEmpty.elim)
      (fun _ _ => Kleisli.hom_ext (by funext x; exact x.elim))
  inl X Y := (Kleisli.Adjunction.toKleisli (TM m)).map (Sum.inl : X.of → X.of ⊕ Y.of)
  inr X Y := (Kleisli.Adjunction.toKleisli (TM m)).map (Sum.inr : Y.of → X.of ⊕ Y.of)
  inl_def _ _ := by
    apply Kleisli.hom_ext; funext x
    simp [joinM, bind_map_left, Equiv.sumEmpty, Functor.mapIso, Equiv.toIso]
  inr_def _ _ := by
    apply Kleisli.hom_ext; funext x
    simp [joinM, bind_map_left, Equiv.emptySum, Functor.mapIso, Equiv.toIso]
  addObjIsBinaryCoproduct X Y :=
    BinaryCofan.IsColimit.mk _
      (fun f g => Kleisli.Hom.mk (Sum.elim f.of g.of))
      (fun _ _ => Kleisli.hom_ext (by funext x; simp [joinM, bind_map_left]))
      (fun _ _ => Kleisli.hom_ext (by funext x; simp [joinM, bind_map_left]))
      (fun f g q h₁ h₂ => Kleisli.hom_ext (by
        funext x
        rcases x with x | x
        · have h := congrFun (congrArg Kleisli.Hom.of h₁) x
          simpa [joinM, bind_map_left] using h
        · have h := congrFun (congrArg Kleisli.Hom.of h₂) x
          simpa [joinM, bind_map_left] using h))

/-! ### Interrelating the presentations -/

@[simp] theorem inl_of (X Y : Kleisli (TM m)) :
    (CocartesianMonoidalCategory.inl X Y).of = fun x => (pure (Sum.inl x) : m (X.of ⊕ Y.of)) :=
  rfl

@[simp] theorem inr_of (X Y : Kleisli (TM m)) :
    (CocartesianMonoidalCategory.inr X Y).of = fun y => (pure (Sum.inr y) : m (X.of ⊕ Y.of)) :=
  rfl

/-- The copairing in the Kleisli category is `Sum.elim`. -/
@[simp] theorem desc_of {X Y T : Kleisli (TM m)} (f : X ⟶ T) (g : Y ⟶ T) :
    (CocartesianMonoidalCategory.desc f g).of = Sum.elim f.of g.of := rfl

/-- The Kleisli inclusion preserves the chosen coproduct on the nose. -/
@[simp] theorem toKleisli_obj_addObj (X Y : Type u) :
    (Kleisli.Adjunction.toKleisli (TM m)).obj (X ⊕ₘ Y) =
      (Kleisli.Adjunction.toKleisli (TM m)).obj X ⊕ₘ
        (Kleisli.Adjunction.toKleisli (TM m)).obj Y := rfl

@[simp] theorem toKleisli_obj_addUnit :
    (Kleisli.Adjunction.toKleisli (TM m)).obj (𝟘_ (Type u)) =
      𝟘_ (Kleisli (TM m)) := rfl

@[simp] theorem toKleisli_map_inl (X Y : Type u) :
    (Kleisli.Adjunction.toKleisli (TM m)).map (CocartesianMonoidalCategory.inl X Y) =
      CocartesianMonoidalCategory.inl
        ((Kleisli.Adjunction.toKleisli (TM m)).obj X)
        ((Kleisli.Adjunction.toKleisli (TM m)).obj Y) := rfl

@[simp] theorem toKleisli_map_inr (X Y : Type u) :
    (Kleisli.Adjunction.toKleisli (TM m)).map (CocartesianMonoidalCategory.inr X Y) =
      CocartesianMonoidalCategory.inr
        ((Kleisli.Adjunction.toKleisli (TM m)).obj X)
        ((Kleisli.Adjunction.toKleisli (TM m)).obj Y) := rfl

/-- The Kleisli inclusion preserves copairing: this is the sense in which a monad preserves
coproducts. -/
theorem toKleisli_map_desc {X Y T : Type u} (f : X ⟶ T) (g : Y ⟶ T) :
    (Kleisli.Adjunction.toKleisli (TM m)).map (CocartesianMonoidalCategory.desc f g) =
      CocartesianMonoidalCategory.desc
        ((Kleisli.Adjunction.toKleisli (TM m)).map f)
        ((Kleisli.Adjunction.toKleisli (TM m)).map g) := by
  apply Kleisli.hom_ext
  funext x
  rcases x with x | x <;> simp [joinM, bind_map_left]

/-- The chosen injections are *value* morphisms, hence pure for the two-point effect lattice. -/
theorem inl_mem_eff_bot (X Y : Kleisli (TM m)) :
    Kleisli.eff (TM m) ⊥ (CocartesianMonoidalCategory.inl X Y) :=
  (Kleisli.Adjunction.toKleisli (TM m)).imageProperty_map _

theorem inr_mem_eff_bot (X Y : Kleisli (TM m)) :
    Kleisli.eff (TM m) ⊥ (CocartesianMonoidalCategory.inr X Y) :=
  (Kleisli.Adjunction.toKleisli (TM m)).imageProperty_map _

/-- The chosen coproduct agrees with the objectwise-sum cocone used elsewhere in the
development. -/
theorem addObjIsoCoprod_eq (X Y : Kleisli (TM m)) :
    CocartesianMonoidalCategory.addObjIsoCoprod X Y = (coprodIsoSum m X Y).symm := by
  apply Iso.ext
  apply CocartesianMonoidalCategory.hom_ext
  · rw [CocartesianMonoidalCategory.inl_addObjIsoCoprod]
    exact (binary_inl_coprodIsoSum_inv m X Y).symm
  · rw [CocartesianMonoidalCategory.inr_addObjIsoCoprod]
    exact (binary_inr_coprodIsoSum_inv m X Y).symm

end Kleisli.Type

end CategoryTheory
