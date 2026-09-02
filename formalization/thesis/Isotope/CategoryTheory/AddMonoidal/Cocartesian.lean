import Isotope.CategoryTheory.AddMonoidal.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# Cocartesian monoidal categories

A `CocartesianMonoidalCategory` is an `AddMonoidalCategory` whose unit is initial and whose
additive tensor is a binary coproduct — the dual of Mathlib's `CartesianMonoidalCategory`, and
the specialisation of `AddMonoidalCategory` promised there.

The point of the class is that the coproduct is *chosen*: `⊕ₘ`, `inl` and `inr` are data.  With
`Limits.HasBinaryCoproducts` the apex and injections come from `Classical.choice` and are
determined only up to an arbitrary automorphism of the apex, so no property of the injections —
purity, centrality, computability — can be proved.  Here they are whatever the instance says.  `Isotope.CategoryTheory.AddMonoidal.Types` gives the
canonical instance on `Type u`, where `⊕ₘ` is `Sum` and `inl`, `inr`, `desc` reduce
definitionally.

This is what a premonoidal subcategory needs in order to be closed under coproducts in a way
that can actually be checked of a model: see the caveat recorded in
`Isotope.CategoryTheory.Premonoidal.Cocartesian`, which the chosen structure is intended to
replace.
-/

universe v u

namespace CategoryTheory

open Category Limits
open scoped AddMonoidalCategory

/-- An additively monoidal category whose unit is initial, with chosen coproduct injections
built from the unit. -/
class SemiCocartesianMonoidalCategory (C : Type u) [Category.{v} C] extends
    AddMonoidalCategory C where
  /-- The additive unit is initial. -/
  isInitialAddUnit : IsInitial (𝟘_ C)
  /-- The left injection. -/
  inl (X Y : C) : X ⟶ X ⊕ₘ Y
  /-- The right injection. -/
  inr (X Y : C) : Y ⟶ X ⊕ₘ Y
  inl_def (X Y : C) : inl X Y = (ρ⁺_ X).inv ≫ (X ◁⁺ isInitialAddUnit.to Y) := by cat_disch
  inr_def (X Y : C) : inr X Y = (λ⁺_ Y).inv ≫ ((isInitialAddUnit.to X) ▷⁺ Y) := by cat_disch

namespace SemiCocartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [SemiCocartesianMonoidalCategory C]

/-- The unique morphism out of the additive unit. -/
def fromZero (X : C) : (𝟘_ C) ⟶ X := isInitialAddUnit.to X

instance (X : C) : Unique ((𝟘_ C) ⟶ X) := isInitialEquivUnique _ _ isInitialAddUnit _

@[ext] lemma fromZero_unique {X : C} (f g : (𝟘_ C) ⟶ X) : f = g := Subsingleton.elim _ _

@[simp] lemma fromZero_zero : fromZero (𝟘_ C) = 𝟙 (𝟘_ C) := fromZero_unique ..

@[reassoc (attr := simp)]
theorem fromZero_comp {X Y : C} (f : X ⟶ Y) : fromZero X ≫ f = fromZero Y :=
  fromZero_unique _ _

end SemiCocartesianMonoidalCategory

/-- **A cocartesian monoidal category**: the additive tensor is a chosen binary coproduct and
the additive unit a chosen initial object. -/
class CocartesianMonoidalCategory (C : Type u) [Category.{v} C] extends
    SemiCocartesianMonoidalCategory C where
  /-- The additive tensor is a binary coproduct. -/
  addObjIsBinaryCoproduct (X Y : C) : IsColimit <| BinaryCofan.mk (inl X Y) (inr X Y)

namespace CocartesianMonoidalCategory

export SemiCocartesianMonoidalCategory (isInitialAddUnit inl inr inl_def inr_def fromZero
  fromZero_unique fromZero_zero fromZero_comp fromZero_comp_assoc)

variable {C : Type u} [Category.{v} C] [CocartesianMonoidalCategory C]

/-- The copairing of two morphisms out of a chosen coproduct. -/
def desc {T X Y : C} (f : X ⟶ T) (g : Y ⟶ T) : X ⊕ₘ Y ⟶ T :=
  (BinaryCofan.IsColimit.desc' (addObjIsBinaryCoproduct X Y) f g).1

@[reassoc (attr := simp)]
lemma inl_desc {T X Y : C} (f : X ⟶ T) (g : Y ⟶ T) : inl X Y ≫ desc f g = f :=
  (BinaryCofan.IsColimit.desc' (addObjIsBinaryCoproduct X Y) f g).2.1

@[reassoc (attr := simp)]
lemma inr_desc {T X Y : C} (f : X ⟶ T) (g : Y ⟶ T) : inr X Y ≫ desc f g = g :=
  (BinaryCofan.IsColimit.desc' (addObjIsBinaryCoproduct X Y) f g).2.2

@[ext 1050]
lemma hom_ext {T X Y : C} {f g : X ⊕ₘ Y ⟶ T}
    (h₁ : inl X Y ≫ f = inl X Y ≫ g) (h₂ : inr X Y ≫ f = inr X Y ≫ g) : f = g :=
  BinaryCofan.IsColimit.hom_ext (addObjIsBinaryCoproduct X Y) h₁ h₂

@[simp] lemma desc_inl_inr (X Y : C) : desc (inl X Y) (inr X Y) = 𝟙 (X ⊕ₘ Y) := by
  ext <;> simp

@[reassoc (attr := simp)]
lemma desc_comp {T T' X Y : C} (f : X ⟶ T) (g : Y ⟶ T) (h : T ⟶ T') :
    desc f g ≫ h = desc (f ≫ h) (g ≫ h) := by ext <;> simp

/-! ### The induced (unchosen) finite coproducts -/

instance (priority := 100) hasBinaryCoproduct (X Y : C) : HasColimit (pair X Y) :=
  ⟨⟨_, addObjIsBinaryCoproduct X Y⟩⟩

instance (priority := 100) hasBinaryCoproducts : HasBinaryCoproducts C :=
  hasBinaryCoproducts_of_hasColimit_pair _

instance (priority := 100) hasInitial : HasInitial C := isInitialAddUnit.hasInitial

instance (priority := 100) hasFiniteCoproducts : HasFiniteCoproducts C :=
  hasFiniteCoproducts_of_has_binary_and_initial

/-- The chosen coproduct agrees with Mathlib's, up to the canonical comparison. -/
noncomputable def addObjIsoCoprod (X Y : C) : X ⊕ₘ Y ≅ X ⨿ Y :=
  (addObjIsBinaryCoproduct X Y).coconePointUniqueUpToIso (colimit.isColimit (pair X Y))

@[reassoc (attr := simp)] lemma inl_addObjIsoCoprod (X Y : C) :
    inl X Y ≫ (addObjIsoCoprod X Y).hom = coprod.inl := by
  simpa [addObjIsoCoprod] using
    (addObjIsBinaryCoproduct X Y).comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (pair X Y)) (Discrete.mk WalkingPair.left)

@[reassoc (attr := simp)] lemma inr_addObjIsoCoprod (X Y : C) :
    inr X Y ≫ (addObjIsoCoprod X Y).hom = coprod.inr := by
  simpa [addObjIsoCoprod] using
    (addObjIsBinaryCoproduct X Y).comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (pair X Y)) (Discrete.mk WalkingPair.right)

end CocartesianMonoidalCategory

end CategoryTheory
