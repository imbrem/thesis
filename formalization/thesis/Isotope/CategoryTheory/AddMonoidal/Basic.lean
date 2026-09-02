import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Additively written monoidal categories

`AddMonoidalCategory` is `MonoidalCategory` written additively: the same axioms, with `⊕ₘ` for
the tensor and `𝟘_ C` for the unit.  It is a separate class rather than a notation for
`MonoidalCategory` because a category can carry both at once — that is exactly what a rig
(bimonoidal) category is, and what a distributive category is a special case of.

The additive structure specialises to a *chosen* finite coproduct structure in
`Isotope.CategoryTheory.AddMonoidal.Cocartesian`.  Unlike `Limits.HasBinaryCoproducts`, a chosen
structure is data: the injections are pinned down rather than determined up to an arbitrary
automorphism of the apex by `Classical.choice`.

## Notation

* `X ⊕ₘ Y` — the additive tensor of objects
* `f ⊕ₕ g` — the additive tensor of morphisms
* `X ◁⁺ f`, `f ▷⁺ X` — additive whiskering
* `𝟘_ C` — the additive unit
* `α⁺_`, `λ⁺_`, `ρ⁺_` — the associator and unitors
-/

universe v u

namespace CategoryTheory

open Category

/-- The data of an additively written monoidal structure: an operation `⊕ₘ` on objects,
functorial in each argument separately, a unit `𝟘_ C`, and coherence isomorphisms. -/
class AddMonoidalCategoryStruct (C : Type u) [Category.{v} C] where
  /-- The additive tensor of objects. -/
  addObj : C → C → C
  /-- Left whiskering by a fixed object. -/
  addWhiskerLeft (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : addObj X Y₁ ⟶ addObj X Y₂
  /-- Right whiskering by a fixed object. -/
  addWhiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) : addObj X₁ Y ⟶ addObj X₂ Y
  /-- The additive tensor of morphisms; by default the two whiskerings in sequence. -/
  addHom {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : addObj X₁ X₂ ⟶ addObj Y₁ Y₂ :=
    addWhiskerRight f X₂ ≫ addWhiskerLeft Y₁ g
  /-- The additive unit. -/
  addUnit (C) : C
  /-- The associator. -/
  addAssociator : ∀ X Y Z : C, addObj (addObj X Y) Z ≅ addObj X (addObj Y Z)
  /-- The left unitor. -/
  addLeftUnitor : ∀ X : C, addObj addUnit X ≅ X
  /-- The right unitor. -/
  addRightUnitor : ∀ X : C, addObj X addUnit ≅ X

namespace AddMonoidalCategory

export AddMonoidalCategoryStruct
  (addObj addWhiskerLeft addWhiskerRight addHom addUnit addAssociator addLeftUnitor
    addRightUnitor)

@[inherit_doc] scoped infixr:70 " ⊕ₘ " => AddMonoidalCategoryStruct.addObj
@[inherit_doc] scoped infixr:70 " ⊕ₕ " => AddMonoidalCategoryStruct.addHom
@[inherit_doc] scoped notation "𝟘_ " C:max => AddMonoidalCategoryStruct.addUnit C
@[inherit_doc] scoped notation:81 X:81 " ◁⁺ " f:80 =>
  AddMonoidalCategoryStruct.addWhiskerLeft X f
@[inherit_doc] scoped notation:81 f:81 " ▷⁺ " Y:80 =>
  AddMonoidalCategoryStruct.addWhiskerRight f Y
@[inherit_doc] scoped notation "α⁺_" => AddMonoidalCategoryStruct.addAssociator
@[inherit_doc] scoped notation "λ⁺_" => AddMonoidalCategoryStruct.addLeftUnitor
@[inherit_doc] scoped notation "ρ⁺_" => AddMonoidalCategoryStruct.addRightUnitor

end AddMonoidalCategory

open scoped AddMonoidalCategory

/-- An additively written monoidal category: the axioms of `MonoidalCategory`, transcribed. -/
class AddMonoidalCategory (C : Type u) [Category.{v} C] extends
    AddMonoidalCategoryStruct C where
  addHom_def {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⊕ₕ g = (f ▷⁺ X₂) ≫ (Y₁ ◁⁺ g) := by cat_disch
  id_addHom_id (X₁ X₂ : C) : 𝟙 X₁ ⊕ₕ 𝟙 X₂ = 𝟙 (X₁ ⊕ₘ X₂) := by cat_disch
  addHom_comp_addHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}
      (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    (f₁ ⊕ₕ f₂) ≫ (g₁ ⊕ₕ g₂) = (f₁ ≫ g₁) ⊕ₕ (f₂ ≫ g₂) := by cat_disch
  addWhiskerLeft_id (X Y : C) : X ◁⁺ 𝟙 Y = 𝟙 (X ⊕ₘ Y) := by cat_disch
  id_addWhiskerRight (X Y : C) : 𝟙 X ▷⁺ Y = 𝟙 (X ⊕ₘ Y) := by cat_disch
  addAssociator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}
      (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    ((f₁ ⊕ₕ f₂) ⊕ₕ f₃) ≫ (α⁺_ Y₁ Y₂ Y₃).hom =
      (α⁺_ X₁ X₂ X₃).hom ≫ (f₁ ⊕ₕ (f₂ ⊕ₕ f₃)) := by cat_disch
  addLeftUnitor_naturality {X Y : C} (f : X ⟶ Y) :
    ((𝟘_ C) ◁⁺ f) ≫ (λ⁺_ Y).hom = (λ⁺_ X).hom ≫ f := by cat_disch
  addRightUnitor_naturality {X Y : C} (f : X ⟶ Y) :
    (f ▷⁺ (𝟘_ C)) ≫ (ρ⁺_ Y).hom = (ρ⁺_ X).hom ≫ f := by cat_disch
  addPentagon (W X Y Z : C) :
    ((α⁺_ W X Y).hom ▷⁺ Z) ≫ (α⁺_ W (X ⊕ₘ Y) Z).hom ≫ (W ◁⁺ (α⁺_ X Y Z).hom) =
      (α⁺_ (W ⊕ₘ X) Y Z).hom ≫ (α⁺_ W X (Y ⊕ₘ Z)).hom := by cat_disch
  addTriangle (X Y : C) :
    (α⁺_ X (𝟘_ C) Y).hom ≫ (X ◁⁺ (λ⁺_ Y).hom) = (ρ⁺_ X).hom ▷⁺ Y := by cat_disch

attribute [reassoc] AddMonoidalCategory.addHom_def
attribute [simp] AddMonoidalCategory.id_addHom_id AddMonoidalCategory.addWhiskerLeft_id
  AddMonoidalCategory.id_addWhiskerRight
attribute [reassoc] AddMonoidalCategory.addHom_comp_addHom
attribute [reassoc] AddMonoidalCategory.addAssociator_naturality
  AddMonoidalCategory.addLeftUnitor_naturality AddMonoidalCategory.addRightUnitor_naturality
attribute [reassoc (attr := simp)] AddMonoidalCategory.addPentagon
  AddMonoidalCategory.addTriangle

namespace AddMonoidalCategory

variable {C : Type u} [Category.{v} C] [AddMonoidalCategory C]

/-- Left whiskering is functorial: it is the additive tensor with an identity. -/
theorem addWhiskerLeft_eq (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : X ◁⁺ f = 𝟙 X ⊕ₕ f := by
  rw [addHom_def]; simp

/-- Right whiskering is functorial: it is the additive tensor with an identity. -/
theorem addWhiskerRight_eq {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) : f ▷⁺ Y = f ⊕ₕ 𝟙 Y := by
  rw [addHom_def]; simp

@[reassoc (attr := simp)]
theorem addWhiskerLeft_comp (X : C) {Y₁ Y₂ Y₃ : C} (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) :
    X ◁⁺ (f ≫ g) = (X ◁⁺ f) ≫ (X ◁⁺ g) := by
  simp only [addWhiskerLeft_eq, addHom_comp_addHom, Category.comp_id]

@[reassoc (attr := simp)]
theorem comp_addWhiskerRight {X₁ X₂ X₃ : C} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (Y : C) :
    (f ≫ g) ▷⁺ Y = (f ▷⁺ Y) ≫ (g ▷⁺ Y) := by
  simp only [addWhiskerRight_eq, addHom_comp_addHom, Category.comp_id]

/-- The additive tensor of two isomorphisms. -/
@[simps]
def addIso {X₁ Y₁ X₂ Y₂ : C} (e : X₁ ≅ Y₁) (f : X₂ ≅ Y₂) : X₁ ⊕ₘ X₂ ≅ Y₁ ⊕ₘ Y₂ where
  hom := e.hom ⊕ₕ f.hom
  inv := e.inv ⊕ₕ f.inv
  hom_inv_id := by rw [addHom_comp_addHom]; simp
  inv_hom_id := by rw [addHom_comp_addHom]; simp

end AddMonoidalCategory

end CategoryTheory
