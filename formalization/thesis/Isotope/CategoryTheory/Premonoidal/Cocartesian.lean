import Isotope.CategoryTheory.Premonoidal.Subcategory
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Coproducts in a wide subcategory

A wide subcategory `P ⊆ C` inherits the finite coproducts of `C` as soon as the coproduct
injections, the maps out of the initial object, and the copairing of two `P`-morphisms all lie
in `P`.  This is `IsCocartesianSubcategory`.

The resulting coproducts of `WideSubcategory P` are the coproducts of `C`, but only up to the
canonical comparison isomorphism: Mathlib's `HasColimit` is a `Prop`, so the chosen colimit is
not definitionally the cocone we supply.  `wideCoprodIso` names that comparison and the lemmas
below let one compute with it.
-/

universe v u

namespace CategoryTheory

open Category Limits
open scoped MonoidalCategory

namespace PremonoidalCategory

variable {C : Type u} [Category.{v} C] [PremonoidalCategory C] (P : MorphismProperty C)

/-- A wide subcategory closed under the finite coproduct structure of `C`: it contains the
injections and the maps out of the initial object, and the copairing of two of its morphisms is
again one of its morphisms. -/
class IsCocartesianSubcategory [HasFiniteCoproducts C] : Prop where
  initial_to_mem (X : C) : P (initial.to X)
  inl_mem (X Y : C) : P (coprod.inl : X ⟶ X ⨿ Y)
  inr_mem (X Y : C) : P (coprod.inr : Y ⟶ X ⨿ Y)
  desc_mem {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} : P f → P g → P (coprod.desc f g)

export IsCocartesianSubcategory (initial_to_mem inl_mem inr_mem desc_mem)

section

variable [HasFiniteCoproducts C] [IsPremonoidalSubcategory P] [IsCocartesianSubcategory P]

/-- The initial object of `C`, viewed in the wide subcategory. -/
noncomputable def wideInitial : WideSubcategory P := ⟨⊥_ C⟩

/-- It is initial there: the unique `C`-morphism out of `⊥_ C` is pure. -/
noncomputable def wideIsInitial : IsInitial (wideInitial P) :=
  IsInitial.ofUniqueHom (fun X => ⟨initial.to X.obj, initial_to_mem (P := P) X.obj⟩)
    (fun _ _ => Subtype.ext (initial.hom_ext _ _))

instance wideHasInitial : HasInitial (WideSubcategory P) := (wideIsInitial P).hasInitial

/-- The ambient left injection, as a morphism of the wide subcategory. -/
noncomputable def wideInl (X Y : WideSubcategory P) : X ⟶ (⟨X.obj ⨿ Y.obj⟩ : WideSubcategory P) :=
  ⟨coprod.inl, inl_mem (P := P) X.obj Y.obj⟩

/-- The ambient right injection, as a morphism of the wide subcategory. -/
noncomputable def wideInr (X Y : WideSubcategory P) : Y ⟶ (⟨X.obj ⨿ Y.obj⟩ : WideSubcategory P) :=
  ⟨coprod.inr, inr_mem (P := P) X.obj Y.obj⟩

@[simp] theorem wideInl_val (X Y : WideSubcategory P) :
    (wideInl P X Y).1 = (coprod.inl : X.obj ⟶ X.obj ⨿ Y.obj) := rfl

@[simp] theorem wideInr_val (X Y : WideSubcategory P) :
    (wideInr P X Y).1 = (coprod.inr : Y.obj ⟶ X.obj ⨿ Y.obj) := rfl

/-- The binary coproduct cocone of `C`, viewed in the wide subcategory. -/
noncomputable def wideBinaryCofan (X Y : WideSubcategory P) : BinaryCofan X Y :=
  BinaryCofan.mk (P := (⟨X.obj ⨿ Y.obj⟩ : WideSubcategory P))
    (wideInl P X Y) (wideInr P X Y)

@[simp] theorem wideBinaryCofan_pt (X Y : WideSubcategory P) :
    (wideBinaryCofan P X Y).pt = ⟨X.obj ⨿ Y.obj⟩ := rfl

@[simp] theorem wideBinaryCofan_inl (X Y : WideSubcategory P) :
    ((wideBinaryCofan P X Y).inl).1 = (coprod.inl : X.obj ⟶ X.obj ⨿ Y.obj) := rfl

@[simp] theorem wideBinaryCofan_inr (X Y : WideSubcategory P) :
    ((wideBinaryCofan P X Y).inr).1 = (coprod.inr : Y.obj ⟶ X.obj ⨿ Y.obj) := rfl

/-- It is a coproduct there, because copairing preserves purity. -/
noncomputable def wideBinaryCofanIsColimit (X Y : WideSubcategory P) :
    IsColimit (wideBinaryCofan P X Y) :=
  BinaryCofan.IsColimit.mk _
    (fun f g => ⟨coprod.desc f.1 g.1, desc_mem (P := P) f.2 g.2⟩)
    (fun f g => Subtype.ext (coprod.inl_desc _ _))
    (fun f g => Subtype.ext (coprod.inr_desc _ _))
    (fun f g m h₁ h₂ => Subtype.ext (by
      refine coprod.hom_ext ?_ ?_
      · rw [coprod.inl_desc]
        simpa [wideBinaryCofan] using congrArg Subtype.val h₁
      · rw [coprod.inr_desc]
        simpa [wideBinaryCofan] using congrArg Subtype.val h₂))

instance wideHasBinaryCoproduct (X Y : WideSubcategory P) : HasColimit (pair X Y) :=
  HasColimit.mk ⟨_, wideBinaryCofanIsColimit P X Y⟩

instance wideHasBinaryCoproducts : HasBinaryCoproducts (WideSubcategory P) :=
  hasBinaryCoproducts_of_hasColimit_pair _

instance wideHasFiniteCoproducts : HasFiniteCoproducts (WideSubcategory P) :=
  hasFiniteCoproducts_of_has_binary_and_initial

/-! ### The inclusion preserves finite coproducts -/

instance wideInclusionPreservesBinary (X Y : WideSubcategory P) :
    PreservesColimit (pair X Y) (wideSubcategoryInclusion P) :=
  preservesColimit_of_preserves_colimit_cocone (wideBinaryCofanIsColimit P X Y)
    ((isColimitMapCoconeBinaryCofanEquiv _ _ _).symm (coprodIsCoprod X.obj Y.obj))

instance wideInclusionPreservesBinaryShape :
    PreservesColimitsOfShape (Discrete WalkingPair) (wideSubcategoryInclusion P) :=
  preservesBinaryCoproducts_of_isIso_coprodComparison _

instance wideInclusionPreservesInitial :
    PreservesColimit (Functor.empty.{0} (WideSubcategory P)) (wideSubcategoryInclusion P) :=
  preservesInitial_of_iso _
    (((wideSubcategoryInclusion P).mapIso
      (initialIsInitial.uniqueUpToIso (wideIsInitial P))).symm)

instance wideInclusionPreservesEmptyShape :
    PreservesColimitsOfShape (Discrete PEmpty.{1}) (wideSubcategoryInclusion P) :=
  preservesColimitsOfShape_pempty_of_preservesInitial _

instance wideInclusionPreservesFiniteCoproducts :
    PreservesFiniteCoproducts (wideSubcategoryInclusion P) where
  preserves n :=
    PreservesFiniteCoproducts.of_preserves_binary_and_initial (wideSubcategoryInclusion P) (Fin n)

/-! ### The comparison isomorphism -/

/-- Mathlib's chosen coproduct in the wide subcategory is the coproduct of `C`, but only up to
this canonical comparison isomorphism. -/
noncomputable def wideCoprodIso (X Y : WideSubcategory P) :
    X.obj ⨿ Y.obj ≅ (X ⨿ Y : WideSubcategory P).obj :=
  PreservesColimitPair.iso (wideSubcategoryInclusion P) X Y

theorem wideCoprodIso_hom (X Y : WideSubcategory P) :
    (wideCoprodIso P X Y).hom = coprodComparison (wideSubcategoryInclusion P) X Y := rfl

@[reassoc (attr := simp)] theorem inl_wideCoprodIso (X Y : WideSubcategory P) :
    (coprod.inl : X.obj ⟶ X.obj ⨿ Y.obj) ≫ (wideCoprodIso P X Y).hom =
      ((coprod.inl : X ⟶ X ⨿ Y)).1 :=
  coprodComparison_inl (wideSubcategoryInclusion P)

@[reassoc (attr := simp)] theorem inr_wideCoprodIso (X Y : WideSubcategory P) :
    (coprod.inr : Y.obj ⟶ X.obj ⨿ Y.obj) ≫ (wideCoprodIso P X Y).hom =
      ((coprod.inr : Y ⟶ X ⨿ Y)).1 :=
  coprodComparison_inr (wideSubcategoryInclusion P)

theorem wideCoprodIso_hom_mem (X Y : WideSubcategory P) :
    P (wideCoprodIso P X Y).hom :=
  desc_mem (P := P) (coprod.inl (X := X) (Y := Y)).2 (coprod.inr (X := X) (Y := Y)).2

/-- The copairing, inside the subcategory, of the ambient injections. -/
noncomputable def wideCoprodBack (X Y : WideSubcategory P) :
    (X ⨿ Y : WideSubcategory P) ⟶ (⟨X.obj ⨿ Y.obj⟩ : WideSubcategory P) :=
  coprod.desc (wideInl P X Y) (wideInr P X Y)

theorem wideCoprodIso_inv_eq (X Y : WideSubcategory P) :
    (wideCoprodIso P X Y).inv = (wideCoprodBack P X Y).1 := by
  have h : (wideCoprodIso P X Y).hom ≫ (wideCoprodBack P X Y).1 = 𝟙 (X.obj ⨿ Y.obj) := by
    refine coprod.hom_ext ?_ ?_
    · rw [← Category.assoc, inl_wideCoprodIso, Category.comp_id]
      have h := coprod.inl_desc (wideInl P X Y) (wideInr P X Y)
      exact congrArg Subtype.val h
    · rw [← Category.assoc, inr_wideCoprodIso, Category.comp_id]
      have h := coprod.inr_desc (wideInl P X Y) (wideInr P X Y)
      exact congrArg Subtype.val h
  have h' := congrArg (fun k : X.obj ⨿ Y.obj ⟶ X.obj ⨿ Y.obj =>
    (wideCoprodIso P X Y).inv ≫ k) h
  simpa using h'.symm

theorem wideCoprodIso_inv_mem (X Y : WideSubcategory P) :
    P (wideCoprodIso P X Y).inv := by
  rw [wideCoprodIso_inv_eq]; exact (wideCoprodBack P X Y).2

end

end PremonoidalCategory

end CategoryTheory
