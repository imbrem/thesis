import Isotope.CategoryTheory.Freyd.Elgot
import Isotope.CategoryTheory.Monad.Types
import Isotope.Elgot.Basic
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Elgot structure on Kleisli categories of type monads -/

universe u

namespace CategoryTheory

open Category Limits
open scoped MonoidalCategory

namespace Kleisli.Type

variable (m : Type u → Type u) [_root_.Monad m] [LawfulMonad m]

abbrev TM (m : Type u → Type u) [_root_.Monad m] [LawfulMonad m] :
    CategoryTheory.Monad (Type u) := ofTypeMonad m

/-- The binary coproduct cocone in the Kleisli category is inherited objectwise from `Type`. -/
def binaryCofan (X Y : Kleisli (TM m)) : BinaryCofan X Y :=
  BinaryCofan.mk
    ((Kleisli.Adjunction.toKleisli (TM m)).map (Sum.inl : X.of → X.of ⊕ Y.of))
    ((Kleisli.Adjunction.toKleisli (TM m)).map (Sum.inr : Y.of → X.of ⊕ Y.of))

/-- The objectwise sum satisfies the Kleisli coproduct universal property. -/
def binaryCofanIsColimit (X Y : Kleisli (TM m)) : IsColimit (binaryCofan m X Y) :=
  BinaryCofan.IsColimit.mk _
    (fun f g ↦ .mk (Sum.elim f.of g.of))
    (fun f g ↦ by
      apply Kleisli.hom_ext
      funext x
      simp [binaryCofan, Kleisli.Adjunction.toKleisli])
    (fun f g ↦ by
      apply Kleisli.hom_ext
      funext y
      simp [binaryCofan, Kleisli.Adjunction.toKleisli])
    (fun f g q hf hg ↦ by
      apply Kleisli.hom_ext
      funext z
      cases z with
      | inl x =>
          have hx := congrArg Kleisli.Hom.of hf
          simpa [binaryCofan, Kleisli.Adjunction.toKleisli] using congrFun hx x
      | inr y =>
          have hy := congrArg Kleisli.Hom.of hg
          simpa [binaryCofan, Kleisli.Adjunction.toKleisli] using congrFun hy y)

instance hasBinaryCoproduct (X Y : Kleisli (TM m)) : HasColimit (pair X Y) :=
  ⟨⟨binaryCofan m X Y, binaryCofanIsColimit m X Y⟩⟩

instance hasBinaryCoproducts : HasBinaryCoproducts (Kleisli (TM m)) :=
  hasBinaryCoproducts_of_hasColimit_pair (C := Kleisli (TM m))

/-- The empty type is initial in the Kleisli category. -/
def initial : IsInitial (Kleisli.mk (TM m) PEmpty) :=
  IsInitial.ofUniqueHom
    (fun _ ↦ Kleisli.Hom.mk PEmpty.elim)
    (fun _ f ↦ by
      apply Kleisli.hom_ext
      funext x
      exact x.elim)

instance emptyHomNonempty (X : Kleisli (TM m)) :
    Nonempty ((Kleisli.mk (TM m) PEmpty) ⟶ X) := ⟨Kleisli.Hom.mk PEmpty.elim⟩

instance emptyHomSubsingleton (X : Kleisli (TM m)) :
    Subsingleton ((Kleisli.mk (TM m) PEmpty) ⟶ X) :=
  ⟨fun f g ↦ by
    apply Kleisli.hom_ext
    funext x
    exact x.elim⟩

instance hasInitial : HasInitial (Kleisli (TM m)) :=
  hasInitial_of_unique (Kleisli.mk (TM m) PEmpty)

instance hasFiniteCoproducts : HasFiniteCoproducts (Kleisli (TM m)) :=
  hasFiniteCoproducts_of_has_binary_and_initial

/-- The pure embedding preserves finite coproducts, since it is the left adjoint in the Kleisli
adjunction. -/
noncomputable instance toKleisliPreservesFiniteCoproducts :
    PreservesFiniteCoproducts (Kleisli.Adjunction.toKleisli (TM m)) := by
  haveI : PreservesColimitsOfSize.{u, u} (Kleisli.Adjunction.toKleisli (TM m)) :=
    (_root_.CategoryTheory.Kleisli.Adjunction.adj (TM m)).leftAdjoint_preservesColimits
  infer_instance

/-- Comparison between Mathlib's selected Kleisli coproduct and the objectwise sum cocone. -/
noncomputable def coprodIsoSum (X Y : Kleisli (TM m)) :
    X ⨿ Y ≅ Kleisli.mk (TM m) (X.of ⊕ Y.of) :=
  (coprodIsCoprod X Y).coconePointUniqueUpToIso (binaryCofanIsColimit m X Y)

@[reassoc (attr := simp)] theorem inl_coprodIsoSum_hom (X Y : Kleisli (TM m)) :
    (coprod.inl : X ⟶ X ⨿ Y) ≫ (coprodIsoSum m X Y).hom =
      (binaryCofan m X Y).inl :=
  by
    simpa [coprodIsoSum] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod X Y)
        (binaryCofanIsColimit m X Y) (Discrete.mk WalkingPair.left))

@[reassoc (attr := simp)] theorem inr_coprodIsoSum_hom (X Y : Kleisli (TM m)) :
    (coprod.inr : Y ⟶ X ⨿ Y) ≫ (coprodIsoSum m X Y).hom =
      (binaryCofan m X Y).inr :=
  by
    simpa [coprodIsoSum] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod X Y)
        (binaryCofanIsColimit m X Y) (Discrete.mk WalkingPair.right))

@[reassoc (attr := simp)] theorem binary_inl_coprodIsoSum_inv (X Y : Kleisli (TM m)) :
    (binaryCofan m X Y).inl ≫ (coprodIsoSum m X Y).inv =
      (coprod.inl : X ⟶ X ⨿ Y) := by
  simpa [coprodIsoSum] using
    (IsColimit.comp_coconePointUniqueUpToIso_inv (coprodIsCoprod X Y)
      (binaryCofanIsColimit m X Y) (Discrete.mk WalkingPair.left))

@[reassoc (attr := simp)] theorem binary_inr_coprodIsoSum_inv (X Y : Kleisli (TM m)) :
    (binaryCofan m X Y).inr ≫ (coprodIsoSum m X Y).inv =
      (coprod.inr : Y ⟶ X ⨿ Y) := by
  simpa [coprodIsoSum] using
    (IsColimit.comp_coconePointUniqueUpToIso_inv (coprodIsCoprod X Y)
      (binaryCofanIsColimit m X Y) (Discrete.mk WalkingPair.right))

/-- The ordinary type-theoretic distribution equivalence, viewed as an isomorphism in `Type`. -/
def typeLeftDistribIso (X Y Z : Type u) :
    (X × Y) ⊕ (X × Z) ≅ X × (Y ⊕ Z) where
  hom := (Equiv.prodSumDistrib X Y Z).symm
  inv := Equiv.prodSumDistrib X Y Z
  hom_inv_id := by
    funext w
    exact (Equiv.prodSumDistrib X Y Z).apply_symm_apply w
  inv_hom_id := by
    funext w
    exact (Equiv.prodSumDistrib X Y Z).symm_apply_apply w

/-- Explicit left distributor in the Kleisli category: compare selected coproducts with sums,
apply the pure distribution equivalence, then compare back under left whiskering. -/
noncomputable def kleisliLeftDistribIso (X Y Z : Kleisli (TM m)) :
    (X ⊗ Y) ⨿ (X ⊗ Z) ≅ X ⊗ (Y ⨿ Z) :=
  ((coprodIsoSum m (X ⊗ Y) (X ⊗ Z)).trans
    ((Kleisli.Adjunction.toKleisli (TM m)).mapIso
      (typeLeftDistribIso X.of Y.of Z.of))).trans
    (PremonoidalCategory.whiskerLeftIso X (coprodIsoSum m Y Z).symm)

theorem kleisliLeftDistribIso_hom (X Y Z : Kleisli (TM m)) :
    (kleisliLeftDistribIso m X Y Z).hom = DistributiveTensor.leftHom X Y Z := by
  apply coprod.hom_ext
  · simp only [kleisliLeftDistribIso, Iso.trans_hom]
    simp only [Category.assoc]
    rw [inl_coprodIsoSum_hom_assoc]
    rw [DistributiveTensor.inl_leftHom]
    have h : (binaryCofan m (X ⊗ Y) (X ⊗ Z)).inl ≫
        ((Kleisli.Adjunction.toKleisli (TM m)).mapIso
          (typeLeftDistribIso X.of Y.of Z.of)).hom =
          X ◁ (binaryCofan m Y Z).inl := by
      apply Kleisli.hom_ext
      funext p
      simp [binaryCofan, typeLeftDistribIso, Kleisli.Adjunction.toKleisli]
      change pure (p.1, Sum.inl p.2) = (fun q ↦ (p.1, q)) <$> pure (Sum.inl p.2)
      simp
    slice_lhs 1 2 => exact h
    change X ◁ (binaryCofan m Y Z).inl ≫
      X ◁ (coprodIsoSum m Y Z).inv = X ◁ coprod.inl
    rw [← PremonoidalCategory.whiskerLeft_comp]
    rw [binary_inl_coprodIsoSum_inv]
    rfl
  · simp only [kleisliLeftDistribIso, Iso.trans_hom]
    simp only [Category.assoc]
    rw [inr_coprodIsoSum_hom_assoc]
    rw [DistributiveTensor.inr_leftHom]
    have h : (binaryCofan m (X ⊗ Y) (X ⊗ Z)).inr ≫
        ((Kleisli.Adjunction.toKleisli (TM m)).mapIso
          (typeLeftDistribIso X.of Y.of Z.of)).hom =
          X ◁ (binaryCofan m Y Z).inr := by
      apply Kleisli.hom_ext
      funext p
      simp [binaryCofan, typeLeftDistribIso, Kleisli.Adjunction.toKleisli]
      change pure (p.1, Sum.inr p.2) = (fun q ↦ (p.1, q)) <$> pure (Sum.inr p.2)
      simp
    slice_lhs 1 2 => exact h
    change X ◁ (binaryCofan m Y Z).inr ≫
      X ◁ (coprodIsoSum m Y Z).inv = X ◁ coprod.inr
    rw [← PremonoidalCategory.whiskerLeft_comp]
    rw [binary_inr_coprodIsoSum_inv]
    rfl

noncomputable instance distributiveTensor : DistributiveTensor (Kleisli (TM m)) where
  left_isIso X Y Z := by
    rw [← kleisliLeftDistribIso_hom m]
    infer_instance

noncomputable instance iteration [Isotope.Elgot.Iterate m] : Iteration (Kleisli (TM m)) where
  iterate f := Kleisli.Hom.mk
    (Isotope.Elgot.iter (m := m) (f ≫ (coprodIsoSum m _ _).hom).of)

@[simp] theorem iterate_of [Isotope.Elgot.Iterate m]
    {X Y : Kleisli (TM m)} (f : X ⟶ Y ⨿ X) :
    (CategoryTheory.iterate f).of =
      Isotope.Elgot.iter (m := m) (f ≫ (coprodIsoSum m Y X).hom).of := rfl

end Kleisli.Type

end CategoryTheory
