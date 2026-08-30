import Isotope.CategoryTheory.Freyd.Elgot
import Isotope.CategoryTheory.Monad.Types
import Isotope.Elgot.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Closed.Types

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

/-- Pure functions and Kleisli computations form a distributive Freyd category. -/
noncomputable instance distributiveFreydCategory :
    DistributiveFreydCategory (Kleisli.Adjunction.toKleisli (TM m)) := {}

noncomputable instance iteration [Isotope.Elgot.Iterate m] : Iteration (Kleisli (TM m)) where
  iterate f := Kleisli.Hom.mk
    (Isotope.Elgot.iter (m := m) (f ≫ (coprodIsoSum m _ _).hom).of)

@[simp] theorem iterate_of [Isotope.Elgot.Iterate m]
    {X Y : Kleisli (TM m)} (f : X ⟶ Y ⨿ X) :
    (CategoryTheory.iterate f).of =
      Isotope.Elgot.iter (m := m) (f ≫ (coprodIsoSum m Y X).hom).of := rfl

theorem coprodIsoSum_hom_sumElim {X Y Z : Kleisli (TM m)}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    (coprodIsoSum m X Y).hom ≫ Kleisli.Hom.mk (Sum.elim f.of g.of) = coprod.desc f g := by
  apply coprod.hom_ext
  · rw [inl_coprodIsoSum_hom_assoc]
    rw [coprod.inl_desc]
    apply Kleisli.hom_ext
    funext x
    simp [binaryCofan, Kleisli.Adjunction.toKleisli, Isotope.Elgot.kcomp,
      Isotope.Elgot.liftPure, Function.comp_def, joinM, bind_map_left]
  · rw [inr_coprodIsoSum_hom_assoc]
    rw [coprod.inr_desc]
    apply Kleisli.hom_ext
    funext y
    simp [binaryCofan, Kleisli.Adjunction.toKleisli, Isotope.Elgot.kcomp,
      Isotope.Elgot.liftPure, Function.comp_def, joinM, bind_map_left]

theorem comp_of_eq_kcomp {X Y Z : Kleisli (TM m)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).of = Isotope.Elgot.kcomp (m := m) f.of g.of := by
  funext x
  simp [Isotope.Elgot.kcomp, joinM, bind_map_left]

theorem iterate_fixpoint [Isotope.Elgot.Iterate m] [Isotope.Elgot.LawfulElgotMonad m]
    {X Y : Kleisli (TM m)} (f : X ⟶ Y ⨿ X) :
    iterate f = f ≫ coprod.desc (𝟙 Y) (iterate f) := by
  rw [← coprodIsoSum_hom_sumElim m (𝟙 _) (iterate f), ← Category.assoc]
  apply Kleisli.hom_ext
  rw [iterate_of]
  change Isotope.Elgot.iter (m := m) _ =
    ((f ≫ (coprodIsoSum m Y X).hom) ≫
      Kleisli.Hom.mk (Sum.elim ((𝟙 Y : Y ⟶ Y).of) (Isotope.Elgot.iter (m := m) _))).of
  conv_rhs => rw [comp_of_eq_kcomp]
  simp only [ofTypeMonad]
  change Isotope.Elgot.iter (m := m) _ = Isotope.Elgot.kcomp (m := m) _
    (Sum.elim (fun x ↦ (pure x : m _)) (Isotope.Elgot.iter (m := m) _))
  exact Isotope.Elgot.LawfulElgotMonad.fixpoint (m := m) _

theorem coprodMap_coprodIsoSum_hom {X Y Z : Kleisli (TM m)} (g : Y ⟶ Z) :
    coprod.map g (𝟙 X) ≫ (coprodIsoSum m Z X).hom =
      (coprodIsoSum m Y X).hom ≫ Kleisli.Hom.mk
        (Sum.elim
          (Isotope.Elgot.kcomp (m := m) g.of
            (Isotope.Elgot.liftPure (m := m) (Sum.inl : Z.of → Z.of ⊕ X.of)))
          (Isotope.Elgot.liftPure (m := m) (Sum.inr : X.of → Z.of ⊕ X.of))) := by
  apply coprod.hom_ext
  · simp only [Category.assoc, coprod.inl_map, inl_coprodIsoSum_hom,
      inl_coprodIsoSum_hom_assoc]
    apply Kleisli.hom_ext
    funext y
    simp [binaryCofan, Kleisli.Adjunction.toKleisli, Isotope.Elgot.kcomp,
      Isotope.Elgot.liftPure, Function.comp_def, joinM, bind_map_left]
  · simp only [Category.assoc, coprod.inr_map, inr_coprodIsoSum_hom,
      inr_coprodIsoSum_hom_assoc]
    apply Kleisli.hom_ext
    funext x
    simp [binaryCofan, Kleisli.Adjunction.toKleisli, Isotope.Elgot.kcomp,
      Isotope.Elgot.liftPure, Function.comp_def, joinM, bind_map_left]

theorem iterate_naturality [Isotope.Elgot.Iterate m] [Isotope.Elgot.LawfulElgotMonad m]
    {X Y Z : Kleisli (TM m)} (f : X ⟶ Y ⨿ X) (g : Y ⟶ Z) :
    iterate f ≫ g = iterate (f ≫ coprod.map g (𝟙 X)) := by
  apply Kleisli.hom_ext
  rw [comp_of_eq_kcomp, iterate_of, iterate_of]
  have h : (f ≫ coprod.map g (𝟙 X)) ≫ (coprodIsoSum m Z X).hom =
      (f ≫ (coprodIsoSum m Y X).hom) ≫ Kleisli.Hom.mk
        (Sum.elim
          (Isotope.Elgot.kcomp (m := m) g.of
            (Isotope.Elgot.liftPure (m := m) (Sum.inl : Z.of → Z.of ⊕ X.of)))
          (Isotope.Elgot.liftPure (m := m) (Sum.inr : X.of → Z.of ⊕ X.of))) := by
    simp only [Category.assoc, coprodMap_coprodIsoSum_hom]
  have hof := congrArg Kleisli.Hom.of h
  rw [hof]
  conv_rhs => rw [comp_of_eq_kcomp]
  change Isotope.Elgot.kcomp (m := m) (Isotope.Elgot.iter (m := m) _) g.of =
    Isotope.Elgot.iter (m := m) (Isotope.Elgot.mapReturn (m := m) _ g.of)
  exact Isotope.Elgot.LawfulElgotMonad.naturality (m := m) _ _

theorem codiagonal_comparison {X Y : Kleisli (TM m)} :
    coprod.desc (𝟙 (Y ⨿ X)) (coprod.inr : X ⟶ Y ⨿ X) ≫
        (coprodIsoSum m Y X).hom =
      coprod.map (coprodIsoSum m Y X).hom (𝟙 X) ≫
        (coprodIsoSum m (Kleisli.mk (TM m) (Y.of ⊕ X.of)) X).hom ≫
          Kleisli.Hom.mk (Isotope.Elgot.liftPure (m := m)
            (Isotope.Elgot.flatten (A := X.of) (B := Y.of))) := by
  let S := Kleisli.mk (TM m) (Y.of ⊕ X.of)
  let flat : Kleisli.mk (TM m) ((Y.of ⊕ X.of) ⊕ X.of) ⟶ S :=
    Kleisli.Hom.mk (Isotope.Elgot.liftPure (m := m)
      (Isotope.Elgot.flatten (A := X.of) (B := Y.of)))
  have hl : (binaryCofan m S X).inl ≫ flat = 𝟙 S := by
    apply Kleisli.hom_ext
    funext s
    cases s <;> simp [S, flat, binaryCofan, Kleisli.Adjunction.toKleisli,
      Isotope.Elgot.flatten, Isotope.Elgot.liftPure, Function.comp_def]
  have hr : (binaryCofan m S X).inr ≫ flat = (binaryCofan m Y X).inr := by
    apply Kleisli.hom_ext
    funext x
    simp [S, flat, binaryCofan, Kleisli.Adjunction.toKleisli,
      Isotope.Elgot.flatten, Isotope.Elgot.liftPure, Function.comp_def]
  dsimp [S, flat] at hl hr
  apply coprod.hom_ext
  · rw [coprod.inl_desc_assoc, Category.id_comp]
    rw [coprod.inl_map_assoc, inl_coprodIsoSum_hom_assoc]
    exact (Category.comp_id _).symm.trans
      (congrArg ((coprodIsoSum m Y X).hom ≫ ·) hl.symm)
  · rw [coprod.inr_desc_assoc]
    rw [coprod.inr_map_assoc, inr_coprodIsoSum_hom_assoc]
    rw [inr_coprodIsoSum_hom, Category.id_comp]
    exact hr.symm

end Kleisli.Type

end CategoryTheory
