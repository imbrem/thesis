import Isotope.CategoryTheory.Freyd.Elgot
import Isotope.CategoryTheory.Monad.Types
import Isotope.Elgot.Basic

/-! # Elgot structure on Kleisli categories of type monads -/

universe u

namespace CategoryTheory

open Category Limits

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

/-- Comparison between Mathlib's selected Kleisli coproduct and the objectwise sum cocone. -/
noncomputable def coprodIsoSum (X Y : Kleisli (TM m)) :
    X ⨿ Y ≅ Kleisli.mk (TM m) (X.of ⊕ Y.of) :=
  (coprodIsCoprod X Y).coconePointUniqueUpToIso (binaryCofanIsColimit m X Y)

noncomputable instance iteration [Isotope.Elgot.Iterate m] : Iteration (Kleisli (TM m)) where
  iterate f := Kleisli.Hom.mk
    (Isotope.Elgot.iter (m := m) (f ≫ (coprodIsoSum m _ _).hom).of)

@[simp] theorem iterate_of [Isotope.Elgot.Iterate m]
    {X Y : Kleisli (TM m)} (f : X ⟶ Y ⨿ X) :
    (CategoryTheory.iterate f).of =
      Isotope.Elgot.iter (m := m) (f ≫ (coprodIsoSum m Y X).hom).of := rfl

end Kleisli.Type

end CategoryTheory
