import Isotope.CategoryTheory.Premonoidal.Subcategory
import Isotope.CategoryTheory.AddMonoidal.Cocartesian
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Coproducts in a wide subcategory

A wide subcategory `P ⊆ C` inherits the finite coproducts of `C` as soon as the coproduct
injections, the maps out of the initial object, and the copairing of two `P`-morphisms all lie
in `P`.  This is `IsCocartesianSubcategory`.

Crucially the condition is stated for the **chosen** coproduct of a
`CocartesianMonoidalCategory`, not for `Limits.coprod`.  A `HasBinaryCoproducts` coproduct comes
from `Classical.choice` and is pinned down only up to an arbitrary automorphism of its apex, so
purity of *its* injections is not provable of any real model; the chosen injections are data, so
it is.

The resulting coproducts of `WideSubcategory P` are Mathlib's, hence still only determined up to
the comparison `wideCoprodIso` — but that comparison is an isomorphism *of the subcategory*, so
both of its directions are automatically `P`-morphisms.
-/

universe v u

namespace CategoryTheory

open Category Limits
open scoped MonoidalCategory AddMonoidalCategory

namespace PremonoidalCategory

variable {C : Type u} [Category.{v} C] [PremonoidalCategory C] (P : MorphismProperty C)

/-- A wide subcategory closed under the chosen finite coproduct structure of `C`: it contains
the injections and the maps out of the initial object, and the copairing of two of its morphisms
is again one of its morphisms. -/
class IsCocartesianSubcategory [CocartesianMonoidalCategory C] : Prop where
  fromZero_mem (X : C) : P (CocartesianMonoidalCategory.fromZero X)
  inl_mem (X Y : C) : P (CocartesianMonoidalCategory.inl X Y)
  inr_mem (X Y : C) : P (CocartesianMonoidalCategory.inr X Y)
  desc_mem {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} :
    P f → P g → P (CocartesianMonoidalCategory.desc f g)

export IsCocartesianSubcategory (fromZero_mem inl_mem inr_mem desc_mem)

/-- Every morphism is trivially closed under the coproduct structure. -/
instance topIsCocartesianSubcategory [CocartesianMonoidalCategory C] :
    IsCocartesianSubcategory (⊤ : MorphismProperty C) where
  fromZero_mem _ := trivial
  inl_mem _ _ := trivial
  inr_mem _ _ := trivial
  desc_mem _ _ := trivial

section

open CocartesianMonoidalCategory

variable [CocartesianMonoidalCategory C] [IsPremonoidalSubcategory P]
  [IsCocartesianSubcategory P]

/-- The chosen initial object of `C`, viewed in the wide subcategory. -/
def wideInitial : WideSubcategory P := ⟨𝟘_ C⟩

/-- It is initial there: the unique `C`-morphism out of `𝟘_ C` is pure. -/
def wideIsInitial : IsInitial (wideInitial P) :=
  IsInitial.ofUniqueHom (fun X => ⟨fromZero X.obj, fromZero_mem (P := P) X.obj⟩)
    (fun _ _ => Subtype.ext (fromZero_unique _ _))

instance wideHasInitial : HasInitial (WideSubcategory P) := (wideIsInitial P).hasInitial

/-- The chosen left injection, as a morphism of the wide subcategory. -/
def wideInl (X Y : WideSubcategory P) :
    X ⟶ (⟨X.obj ⊕ₘ Y.obj⟩ : WideSubcategory P) :=
  ⟨inl X.obj Y.obj, inl_mem (P := P) X.obj Y.obj⟩

/-- The chosen right injection, as a morphism of the wide subcategory. -/
def wideInr (X Y : WideSubcategory P) :
    Y ⟶ (⟨X.obj ⊕ₘ Y.obj⟩ : WideSubcategory P) :=
  ⟨inr X.obj Y.obj, inr_mem (P := P) X.obj Y.obj⟩

@[simp] theorem wideInl_val (X Y : WideSubcategory P) :
    (wideInl P X Y).1 = inl X.obj Y.obj := rfl

@[simp] theorem wideInr_val (X Y : WideSubcategory P) :
    (wideInr P X Y).1 = inr X.obj Y.obj := rfl

/-- The chosen binary coproduct cocone of `C`, viewed in the wide subcategory. -/
def wideBinaryCofan (X Y : WideSubcategory P) : BinaryCofan X Y :=
  BinaryCofan.mk (P := (⟨X.obj ⊕ₘ Y.obj⟩ : WideSubcategory P))
    (wideInl P X Y) (wideInr P X Y)

@[simp] theorem wideBinaryCofan_pt (X Y : WideSubcategory P) :
    (wideBinaryCofan P X Y).pt = ⟨X.obj ⊕ₘ Y.obj⟩ := rfl

@[simp] theorem wideBinaryCofan_inl (X Y : WideSubcategory P) :
    ((wideBinaryCofan P X Y).inl).1 = inl X.obj Y.obj := rfl

@[simp] theorem wideBinaryCofan_inr (X Y : WideSubcategory P) :
    ((wideBinaryCofan P X Y).inr).1 = inr X.obj Y.obj := rfl

/-- It is a coproduct there, because copairing preserves purity. -/
def wideBinaryCofanIsColimit (X Y : WideSubcategory P) :
    IsColimit (wideBinaryCofan P X Y) :=
  BinaryCofan.IsColimit.mk _
    (fun f g => ⟨desc f.1 g.1, desc_mem (P := P) f.2 g.2⟩)
    (fun f g => Subtype.ext (inl_desc _ _))
    (fun f g => Subtype.ext (inr_desc _ _))
    (fun f g mm h₁ h₂ => Subtype.ext (by
      refine CocartesianMonoidalCategory.hom_ext ?_ ?_
      · rw [inl_desc]
        simpa [wideBinaryCofan] using congrArg Subtype.val h₁
      · rw [inr_desc]
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
    ((isColimitMapCoconeBinaryCofanEquiv _ _ _).symm (addObjIsBinaryCoproduct X.obj Y.obj))

instance wideInclusionPreservesBinaryShape :
    PreservesColimitsOfShape (Discrete WalkingPair) (wideSubcategoryInclusion P) :=
  preservesBinaryCoproducts_of_isIso_coprodComparison _

instance wideInclusionPreservesInitial :
    PreservesColimit (Functor.empty.{0} (WideSubcategory P)) (wideSubcategoryInclusion P) :=
  preservesInitial_of_iso _
    ((initialIsInitial.uniqueUpToIso isInitialAddUnit) ≪≫
      ((wideSubcategoryInclusion P).mapIso
        (initialIsInitial.uniqueUpToIso (wideIsInitial P))).symm)

instance wideInclusionPreservesEmptyShape :
    PreservesColimitsOfShape (Discrete PEmpty.{1}) (wideSubcategoryInclusion P) :=
  preservesColimitsOfShape_pempty_of_preservesInitial _

instance wideInclusionPreservesFiniteCoproducts :
    PreservesFiniteCoproducts (wideSubcategoryInclusion P) where
  preserves n :=
    PreservesFiniteCoproducts.of_preserves_binary_and_initial (wideSubcategoryInclusion P) (Fin n)

/-! ### The comparison isomorphism -/

/-- Comparison, inside the subcategory, between the chosen coproduct of `C` and Mathlib's chosen
coproduct.  Because it is an isomorphism *of the subcategory*, both directions are automatically
`P`-morphisms — which is exactly what the `⨿`-based formulation could not deliver. -/
noncomputable def wideCoprodCompare (X Y : WideSubcategory P) :
    (⟨X.obj ⊕ₘ Y.obj⟩ : WideSubcategory P) ≅ X ⨿ Y :=
  (wideBinaryCofanIsColimit P X Y).coconePointUniqueUpToIso (colimit.isColimit (pair X Y))

/-- The comparison, at the level of `C`. -/
noncomputable def wideCoprodIso (X Y : WideSubcategory P) :
    (X.obj ⊕ₘ Y.obj) ≅ (X ⨿ Y : WideSubcategory P).obj :=
  (wideSubcategoryInclusion P).mapIso (wideCoprodCompare P X Y)

theorem wideCoprodIso_hom_mem (X Y : WideSubcategory P) :
    P (wideCoprodIso P X Y).hom := (wideCoprodCompare P X Y).hom.2

theorem wideCoprodIso_inv_mem (X Y : WideSubcategory P) :
    P (wideCoprodIso P X Y).inv := (wideCoprodCompare P X Y).inv.2

@[reassoc (attr := simp)] theorem inl_wideCoprodIso (X Y : WideSubcategory P) :
    inl X.obj Y.obj ≫ (wideCoprodIso P X Y).hom =
      ((coprod.inl : X ⟶ X ⨿ Y)).1 := by
  have := congrArg Subtype.val
    ((wideBinaryCofanIsColimit P X Y).comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (pair X Y)) (Discrete.mk WalkingPair.left))
  simpa [wideCoprodIso, wideCoprodCompare, coprod.inl] using this

@[reassoc (attr := simp)] theorem inr_wideCoprodIso (X Y : WideSubcategory P) :
    inr X.obj Y.obj ≫ (wideCoprodIso P X Y).hom =
      ((coprod.inr : Y ⟶ X ⨿ Y)).1 := by
  have := congrArg Subtype.val
    ((wideBinaryCofanIsColimit P X Y).comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (pair X Y)) (Discrete.mk WalkingPair.right))
  simpa [wideCoprodIso, wideCoprodCompare, coprod.inr] using this

end

end PremonoidalCategory

end CategoryTheory
