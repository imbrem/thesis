import Isotope.CategoryTheory.Freyd.Subcategory
import Isotope.CategoryTheory.Freyd.Elgot
import Isotope.CategoryTheory.Premonoidal.Cocartesian

/-!
# Distributive and Elgot structure on the pure subcategory

`Isotope.CategoryTheory.Freyd.Subcategory` shows that the inclusion of a cartesian central wide
subcategory is a Freyd category.  This file transports the rest of the structure needed by the
categorical semantics of λ-iter from `C` down to `C_⊥`:

* `IsCocartesianSubcategory` gives `C_⊥` finite coproducts and makes the inclusion preserve
  them (this is `Isotope.CategoryTheory.Premonoidal.Cocartesian`);
* `IsDistributiveSubcategory` — the ambient distributor has a pure inverse — makes `C_⊥`
  distributive, hence the inclusion a `DistributiveFreydCategory`;
* `IsUniformIteration` and `IsStrongIteration` are the two remaining Elgot axioms, both
  statements about `C` alone, and they upgrade the inclusion to a `StrongElgotFreydCategory`.

The upshot is that a premonoidal category with all this structure *is* a model of λ-iter in the
subcategory presentation, with no separate value category.
-/

universe v u

namespace CategoryTheory

open Category Limits
open scoped MonoidalCategory

namespace PremonoidalCategory

variable {C : Type u} [Category.{v} C] [PremonoidalCategory C] (P : MorphismProperty C)

/-- The ambient left distributor has a pure inverse. -/
class IsDistributiveSubcategory [HasFiniteCoproducts C] [DistributiveTensor C] : Prop where
  leftInv_mem (X Y Z : C) : P (DistributiveTensor.leftIso X Y Z).inv

section Distributive

variable [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C] [DistributiveTensor C]
  [IsCentralSubcategory P] [IsCocartesianSubcategory P] [IsDistributiveSubcategory P]

/-- The distributor of the wide subcategory, conjugated into `C` along the coproduct
comparison, is the distributor of `C`. -/
theorem wideLeftHom_aux (X Y Z : WideSubcategory P) :
    (wideCoprodIso P (X ⊗ Y) (X ⊗ Z)).hom ≫ (DistributiveTensor.leftHom X Y Z).1 =
      DistributiveTensor.leftHom X.obj Y.obj Z.obj ≫
        (X.obj ◁ (wideCoprodIso P Y Z).hom) := by
  refine coprod.hom_ext ?_ ?_
  · have hV := congrArg Subtype.val (DistributiveTensor.inl_leftHom X Y Z)
    simp only [WideSubcategory.comp_def, whiskerLeft_val] at hV
    rw [← Category.assoc, inl_wideCoprodIso, hV, ← Category.assoc,
      DistributiveTensor.inl_leftHom, ← PremonoidalCategory.whiskerLeft_comp,
      inl_wideCoprodIso]
  · have hV := congrArg Subtype.val (DistributiveTensor.inr_leftHom X Y Z)
    simp only [WideSubcategory.comp_def, whiskerLeft_val] at hV
    rw [← Category.assoc, inr_wideCoprodIso, hV, ← Category.assoc,
      DistributiveTensor.inr_leftHom, ← PremonoidalCategory.whiskerLeft_comp,
      inr_wideCoprodIso]

theorem wideLeftHom_val (X Y Z : WideSubcategory P) :
    (DistributiveTensor.leftHom X Y Z).1 =
      (wideCoprodIso P (X ⊗ Y) (X ⊗ Z)).inv ≫
        DistributiveTensor.leftHom X.obj Y.obj Z.obj ≫
        (X.obj ◁ (wideCoprodIso P Y Z).hom) := by
  rw [← wideLeftHom_aux, Iso.inv_hom_id_assoc]

/-- The inverse distributor of the wide subcategory, at the level of `C`. -/
noncomputable def wideLeftInvVal (X Y Z : WideSubcategory P) :
    (X ⊗ (Y ⨿ Z) : WideSubcategory P).obj ⟶ ((X ⊗ Y) ⨿ (X ⊗ Z) : WideSubcategory P).obj :=
  (X.obj ◁ (wideCoprodIso P Y Z).inv) ≫
    (DistributiveTensor.leftIso X.obj Y.obj Z.obj).inv ≫
    (wideCoprodIso P (X ⊗ Y) (X ⊗ Z)).hom

theorem wideLeftInvVal_mem (X Y Z : WideSubcategory P) : P (wideLeftInvVal P X Y Z) :=
  P.comp_mem _ _
    (IsPremonoidalSubcategory.whiskerLeft_mem _ (wideCoprodIso_inv_mem P Y Z))
    (P.comp_mem _ _ (IsDistributiveSubcategory.leftInv_mem X.obj Y.obj Z.obj)
      (wideCoprodIso_hom_mem P _ _))

/-- **The pure subcategory is distributive.** -/
instance wideDistributiveTensor : DistributiveTensor (WideSubcategory P) where
  left_isIso X Y Z := by
    refine ⟨⟨⟨wideLeftInvVal P X Y Z, wideLeftInvVal_mem P X Y Z⟩, ?_, ?_⟩⟩
    · apply Subtype.ext
      show (DistributiveTensor.leftHom X Y Z).1 ≫ wideLeftInvVal P X Y Z = _
      rw [wideLeftHom_val, wideLeftInvVal]
      simp only [Category.assoc, DistributiveTensor.leftIso, asIso_inv]
      rw [← PremonoidalCategory.whiskerLeft_comp_assoc, Iso.hom_inv_id,
        PremonoidalCategory.whiskerLeft_id, Category.id_comp, IsIso.hom_inv_id_assoc,
        Iso.inv_hom_id]
      rfl
    · apply Subtype.ext
      show wideLeftInvVal P X Y Z ≫ (DistributiveTensor.leftHom X Y Z).1 = _
      rw [wideLeftHom_val, wideLeftInvVal]
      simp only [Category.assoc, DistributiveTensor.leftIso, asIso_inv]
      rw [Iso.hom_inv_id_assoc, IsIso.inv_hom_id_assoc,
        ← PremonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id,
        PremonoidalCategory.whiskerLeft_id]
      rfl

end Distributive

/-! ### The Elgot axioms -/

/-- Uniformity of the ambient iteration operator with respect to `P`-morphisms. -/
class IsUniformIteration [HasFiniteCoproducts C] [Iteration C] : Prop where
  uniformity {A D B : C} (f : A ⟶ B ⨿ A) (g : D ⟶ B ⨿ D) {h : A ⟶ D} (hh : P h)
    (comm : f ≫ coprod.map (𝟙 B) h = h ≫ g) : iterate f = h ≫ iterate g

/-- Strength of the ambient iteration operator.  This is a statement about `C` alone. -/
class IsStrongIteration (C : Type u) [Category.{v} C] [PremonoidalCategory C]
    [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
    [DistributivePremonoidalCategory C] [Iteration C] : Prop where
  iterate_whiskerLeft {X Y : C} (Z : C) (f : X ⟶ Y ⨿ X) :
    iterate ((Z ◁ f) ≫ DistributivePremonoidalCategory.leftInv Z Y X) = Z ◁ iterate f

section Elgot

variable [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C] [DistributiveTensor C]
  [Iteration C] [ElgotCategory C]
  [IsCentralSubcategory P] [IsSemiCartesianSubcategory P] [IsCartesianSubcategory P]
  [IsCocartesianSubcategory P] [IsDistributiveSubcategory P]

/-- **The inclusion of the pure subcategory is a distributive Freyd category.** -/
instance pureInclusionDistributiveFreyd :
    DistributiveFreydCategory (pureInclusion P) where
  preservesFiniteCoproducts := inferInstance

variable [IsUniformIteration P]

/-- **…and an Elgot Freyd category**, since the ambient iteration is uniform for pure
morphisms. -/
instance pureInclusionElgotFreyd : ElgotFreydCategory (pureInclusion P) where
  uniformity f g h comm := IsUniformIteration.uniformity (P := P) f g h.2 comm

variable [IsStrongIteration C]

/-- **…and a strong Elgot Freyd category**, since the ambient iteration is strong. -/
instance pureInclusionStrongElgotFreyd :
    StrongElgotFreydCategory (pureInclusion P) where
  iterate_whiskerLeft Z f := IsStrongIteration.iterate_whiskerLeft Z f

end Elgot

end PremonoidalCategory

end CategoryTheory
