import Isotope.CategoryTheory.Premonoidal.Center
import Isotope.CategoryTheory.Premonoidal.Symmetric
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Wide subcategories of a premonoidal category

A premonoidal category has no interchange law, so a wide subcategory does not automatically
inherit a tensor product of morphisms.  This file isolates exactly what is needed:

* `IsPremonoidalSubcategory P` closes `P` under whiskering and asks it to contain the
  structural isomorphisms.  This already suffices to lift the *object-level* monoidal data.
* `IsCentralSubcategory P` additionally asks every `P`-morphism to be central.  Centrality is
  precisely the missing interchange law, so `WideSubcategory P` becomes an honest symmetric
  *monoidal* category, and its inclusion into `C` is a strong symmetric premonoidal functor
  which is bijective on objects.
* `CartesianSubcategory P` records that `𝟙_ C` is terminal and `X ⊗ Y` is a binary product
  *inside* `P`.  This makes `WideSubcategory P` cartesian monoidal.

These are the ingredients of the subcategory presentation of a Freyd category: the value
category is recovered as `WideSubcategory P`, never as a separate category related by a
functor.
-/

universe v u

namespace CategoryTheory

open Category Limits
open scoped MonoidalCategory

namespace PremonoidalCategory

variable {C : Type u} [Category.{v} C] [PremonoidalCategory C]

/-! ### Sequential tensor calculus -/

/-- The interchange law holds for the left sequential tensor as soon as the second morphism in
the left position is central. -/
@[reassoc]
theorem leftTensor_comp_leftTensor {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}
    (f₁ : X₁ ⟶ Y₁) (g₁ : Y₁ ⟶ Z₁) (f₂ : X₂ ⟶ Y₂) (g₂ : Y₂ ⟶ Z₂)
    (hg₁ : IsCentral g₁) :
    (f₁ ⋉ f₂) ≫ (g₁ ⋉ g₂) = (f₁ ≫ g₁) ⋉ (f₂ ≫ g₂) := by
  have h : Y₁ ◁ f₂ ≫ g₁ ▷ Y₂ = g₁ ▷ X₂ ≫ Z₁ ◁ f₂ := (hg₁.1 f₂).symm
  simp only [leftTensor, comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [← Category.assoc (Y₁ ◁ f₂), h]
  simp

/-- Associator naturality for the left sequential tensor.  No centrality is needed: each of the
three premonoidal naturality laws only moves one morphism at a time. -/
@[reassoc]
theorem leftTensor_associator {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    ((f₁ ⋉ f₂) ⋉ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⋉ (f₂ ⋉ f₃)) := by
  simp only [leftTensor, comp_whiskerRight, whiskerLeft_comp, Category.assoc,
    associator_naturality_right, associator_naturality_middle_assoc,
    associator_naturality_left_assoc]

/-- `eqToHom` is central: after substituting the equalities it is an identity. -/
theorem isCentral_eqToHom {X Y : C} (h : X = Y) : IsCentral (eqToHom h) := by
  cases h; simpa using isCentral_id X

/-- In a symmetric premonoidal category the inverse of a braiding is the opposite braiding. -/
theorem braiding_inv_eq [SymmetricPremonoidalCategory C] (X Y : C) :
    (BraidedPremonoidalCategory.braiding X Y).inv =
      (BraidedPremonoidalCategory.braiding Y X).hom :=
  (Iso.inv_ext' (SymmetricPremonoidalCategory.symmetry X Y)).symm

/-! ### Premonoidal wide subcategories -/

variable (P : MorphismProperty C)

/-- A wide subcategory of a premonoidal category which is closed under whiskering by objects and
contains the structural isomorphisms together with their inverses. -/
class IsPremonoidalSubcategory : Prop extends P.IsMultiplicative where
  whiskerLeft_mem (Z : C) {X Y : C} {f : X ⟶ Y} : P f → P (Z ◁ f)
  whiskerRight_mem {X Y : C} {f : X ⟶ Y} (Z : C) : P f → P (f ▷ Z)
  associator_hom_mem (X Y Z : C) : P (α_ X Y Z).hom
  associator_inv_mem (X Y Z : C) : P (α_ X Y Z).inv
  leftUnitor_hom_mem (X : C) : P (λ_ X).hom
  leftUnitor_inv_mem (X : C) : P (λ_ X).inv
  rightUnitor_hom_mem (X : C) : P (ρ_ X).hom
  rightUnitor_inv_mem (X : C) : P (ρ_ X).inv

/-- A premonoidal wide subcategory of a symmetric premonoidal category which also contains the
braiding. -/
class IsSymmetricSubcategory [SymmetricPremonoidalCategory C] : Prop
    extends IsPremonoidalSubcategory P where
  braiding_hom_mem (X Y : C) : P (BraidedPremonoidalCategory.braiding X Y).hom

/-- A symmetric wide subcategory all of whose morphisms are central.  Centrality supplies the
interchange law that a premonoidal category lacks. -/
class IsCentralSubcategory [SymmetricPremonoidalCategory C] : Prop
    extends IsSymmetricSubcategory P where
  central {X Y : C} {f : X ⟶ Y} : P f → IsCentral f

export IsPremonoidalSubcategory (whiskerLeft_mem whiskerRight_mem associator_hom_mem
  associator_inv_mem leftUnitor_hom_mem leftUnitor_inv_mem rightUnitor_hom_mem
  rightUnitor_inv_mem)

export IsSymmetricSubcategory (braiding_hom_mem)

/-! ### The induced monoidal structure -/

section Struct

variable [IsPremonoidalSubcategory P]

/-- Package a morphism of `C` lying in `P` together with an inverse also lying in `P` as an
isomorphism of `WideSubcategory P`. -/
@[simps]
def subIso {X Y : WideSubcategory P} (e : X.obj ≅ Y.obj) (h : P e.hom) (h' : P e.inv) :
    X ≅ Y where
  hom := ⟨e.hom, h⟩
  inv := ⟨e.inv, h'⟩
  hom_inv_id := Subtype.ext e.hom_inv_id
  inv_hom_id := Subtype.ext e.inv_hom_id

instance wideSubcategoryMonoidalStruct : MonoidalCategoryStruct (WideSubcategory P) where
  tensorObj X Y := ⟨X.obj ⊗ Y.obj⟩
  whiskerLeft X _ _ f := ⟨X.obj ◁ f.1, whiskerLeft_mem (P := P) X.obj f.2⟩
  whiskerRight f Z := ⟨f.1 ▷ Z.obj, whiskerRight_mem (P := P) Z.obj f.2⟩
  tensorUnit := ⟨𝟙_ C⟩
  associator X Y Z :=
    subIso P (α_ X.obj Y.obj Z.obj)
      (associator_hom_mem (P := P) _ _ _) (associator_inv_mem (P := P) _ _ _)
  leftUnitor X :=
    subIso P (λ_ X.obj) (leftUnitor_hom_mem (P := P) _) (leftUnitor_inv_mem (P := P) _)
  rightUnitor X :=
    subIso P (ρ_ X.obj) (rightUnitor_hom_mem (P := P) _) (rightUnitor_inv_mem (P := P) _)

@[simp] theorem tensorObj_obj (X Y : WideSubcategory P) : (X ⊗ Y).obj = X.obj ⊗ Y.obj := rfl

@[simp] theorem tensorUnit_obj : (𝟙_ (WideSubcategory P)).obj = 𝟙_ C := rfl

@[simp] theorem whiskerLeft_val (X : WideSubcategory P) {Y Z : WideSubcategory P} (f : Y ⟶ Z) :
    (X ◁ f).1 = X.obj ◁ f.1 := rfl

@[simp] theorem whiskerRight_val {X Y : WideSubcategory P} (f : X ⟶ Y) (Z : WideSubcategory P) :
    (f ▷ Z).1 = f.1 ▷ Z.obj := rfl

@[simp] theorem tensorHom_val {X Y X' Y' : WideSubcategory P} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (f ⊗ₘ g).1 = f.1 ⋉ g.1 := rfl

@[simp] theorem associator_hom_val (X Y Z : WideSubcategory P) :
    (α_ X Y Z).hom.1 = (α_ X.obj Y.obj Z.obj).hom := rfl

@[simp] theorem associator_inv_val (X Y Z : WideSubcategory P) :
    (α_ X Y Z).inv.1 = (α_ X.obj Y.obj Z.obj).inv := rfl

@[simp] theorem leftUnitor_hom_val (X : WideSubcategory P) :
    (λ_ X).hom.1 = (λ_ X.obj).hom := rfl

@[simp] theorem leftUnitor_inv_val (X : WideSubcategory P) :
    (λ_ X).inv.1 = (λ_ X.obj).inv := rfl

@[simp] theorem rightUnitor_hom_val (X : WideSubcategory P) :
    (ρ_ X).hom.1 = (ρ_ X.obj).hom := rfl

@[simp] theorem rightUnitor_inv_val (X : WideSubcategory P) :
    (ρ_ X).inv.1 = (ρ_ X.obj).inv := rfl

end Struct

section Monoidal

variable [SymmetricPremonoidalCategory C] [IsCentralSubcategory P]

instance wideSubcategoryMonoidal : MonoidalCategory (WideSubcategory P) where
  tensorHom_def _ _ := rfl
  id_tensorHom_id X Y := Subtype.ext (by simp)
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ :=
    Subtype.ext (leftTensor_comp_leftTensor f₁.1 g₁.1 f₂.1 g₂.1 (IsCentralSubcategory.central g₁.2))
  whiskerLeft_id X Y := Subtype.ext (by simp)
  id_whiskerRight X Y := Subtype.ext (by simp)
  associator_naturality f₁ f₂ f₃ := Subtype.ext (leftTensor_associator f₁.1 f₂.1 f₃.1)
  leftUnitor_naturality f := Subtype.ext (PremonoidalCategory.leftUnitor_naturality f.1)
  rightUnitor_naturality f := Subtype.ext (PremonoidalCategory.rightUnitor_naturality f.1)
  pentagon W X Y Z := Subtype.ext (PremonoidalCategory.pentagon W.obj X.obj Y.obj Z.obj)
  triangle X Y := Subtype.ext (PremonoidalCategory.triangle X.obj Y.obj)

/-- The braiding of the wide subcategory, inherited from `C`. -/
def subBraiding (X Y : WideSubcategory P) : X ⊗ Y ≅ Y ⊗ X :=
  subIso P (BraidedPremonoidalCategory.braiding X.obj Y.obj)
    (braiding_hom_mem (P := P) _ _)
    (by rw [braiding_inv_eq]; exact braiding_hom_mem (P := P) _ _)

@[simp] theorem subBraiding_hom_val (X Y : WideSubcategory P) :
    (subBraiding P X Y).hom.1 = (BraidedPremonoidalCategory.braiding X.obj Y.obj).hom := rfl

@[simp] theorem subBraiding_inv_val (X Y : WideSubcategory P) :
    (subBraiding P X Y).inv.1 = (BraidedPremonoidalCategory.braiding X.obj Y.obj).inv := rfl

instance wideSubcategoryBraided : BraidedCategory (WideSubcategory P) where
  braiding := subBraiding P
  braiding_naturality_right := by
    intro X Y Z f
    apply Subtype.ext
    exact BraidedPremonoidalCategory.naturality_right X.obj f.1
  braiding_naturality_left := by
    intro X Y f Z
    apply Subtype.ext
    exact BraidedPremonoidalCategory.naturality_left f.1 Z.obj
  hexagon_forward := by
    intro X Y Z
    apply Subtype.ext
    exact BraidedPremonoidalCategory.hexagon_forward X.obj Y.obj Z.obj
  hexagon_reverse := by
    intro X Y Z
    apply Subtype.ext
    exact BraidedPremonoidalCategory.hexagon_reverse X.obj Y.obj Z.obj

instance wideSubcategorySymmetric : SymmetricCategory (WideSubcategory P) where
  symmetry := by
    intro X Y
    apply Subtype.ext
    exact SymmetricPremonoidalCategory.symmetry X.obj Y.obj

@[simp] theorem braiding_hom_val (X Y : WideSubcategory P) :
    (BraidedCategory.braiding X Y).hom.1 =
      (BraidedPremonoidalCategory.braiding X.obj Y.obj).hom := rfl

@[simp] theorem braiding_inv_val (X Y : WideSubcategory P) :
    (BraidedCategory.braiding X Y).inv.1 =
      (BraidedPremonoidalCategory.braiding X.obj Y.obj).inv := rfl

end Monoidal


/-! ### Cartesian wide subcategories -/

section Cartesian

variable [SymmetricPremonoidalCategory C] [IsCentralSubcategory P]

/-- The tensor unit is terminal *inside* `P`: there is exactly one `P`-morphism `X ⟶ 𝟙_ C`.
Nothing is claimed about arbitrary morphisms of `C` into `𝟙_ C`. -/
class IsSemiCartesianSubcategory : Prop where
  existsUnique_toUnit (X : C) : ∃! f : X ⟶ 𝟙_ C, P f

namespace IsSemiCartesianSubcategory

variable [IsSemiCartesianSubcategory P]

/-- The unique `P`-morphism into the tensor unit. -/
noncomputable def toUnit (X : C) : X ⟶ 𝟙_ C := (existsUnique_toUnit (P := P) X).choose

theorem toUnit_mem (X : C) : P (toUnit P X) := (existsUnique_toUnit (P := P) X).choose_spec.1

theorem toUnit_unique {X : C} {f : X ⟶ 𝟙_ C} (hf : P f) : f = toUnit P X :=
  (existsUnique_toUnit (P := P) X).choose_spec.2 f hf

theorem toUnit_eq {X : C} {f g : X ⟶ 𝟙_ C} (hf : P f) (hg : P g) : f = g :=
  (toUnit_unique P hf).trans (toUnit_unique P hg).symm

/-- The left projection of the pure product. -/
noncomputable def fst (X Y : C) : X ⊗ Y ⟶ X := X ◁ toUnit P Y ≫ (ρ_ X).hom

/-- The right projection of the pure product. -/
noncomputable def snd (X Y : C) : X ⊗ Y ⟶ Y := toUnit P X ▷ Y ≫ (λ_ Y).hom

theorem fst_mem (X Y : C) : P (fst P X Y) :=
  P.comp_mem _ _ (whiskerLeft_mem (P := P) _ (toUnit_mem P Y)) (rightUnitor_hom_mem (P := P) X)

theorem snd_mem (X Y : C) : P (snd P X Y) :=
  P.comp_mem _ _ (whiskerRight_mem (P := P) _ (toUnit_mem P X)) (leftUnitor_hom_mem (P := P) Y)

/-- The tensor unit is terminal in the wide subcategory. -/
noncomputable def wideIsTerminalUnit : Limits.IsTerminal (𝟙_ (WideSubcategory P)) :=
  Limits.IsTerminal.ofUniqueHom (fun X => ⟨toUnit P X.obj, toUnit_mem P X.obj⟩)
    (fun _ f => Subtype.ext (toUnit_unique P f.2))

@[simp] theorem wideIsTerminalUnit_from_val (X : WideSubcategory P) :
    ((wideIsTerminalUnit P).from X).1 = toUnit P X.obj := rfl

end IsSemiCartesianSubcategory

open IsSemiCartesianSubcategory in
/-- `X ⊗ Y` is a binary product of `X` and `Y` inside `P`.  Together with
`IsSemiCartesianSubcategory` this says the wide subcategory `P` is cartesian, with the ambient
premonoidal tensor as its categorical product: exactly the defining condition of the value
subcategory of a Freyd category. -/
class IsCartesianSubcategory [IsSemiCartesianSubcategory P] : Prop where
  existsUnique_lift {T X Y : C} {f : T ⟶ X} {g : T ⟶ Y} (hf : P f) (hg : P g) :
    ∃! h : {h : T ⟶ X ⊗ Y // P h},
      h.1 ≫ fst P X Y = f ∧ h.1 ≫ snd P X Y = g

namespace IsCartesianSubcategory

open IsSemiCartesianSubcategory

variable [IsSemiCartesianSubcategory P] [IsCartesianSubcategory P]

/-- The pairing of two `P`-morphisms. -/
noncomputable def lift {T X Y : C} {f : T ⟶ X} {g : T ⟶ Y} (hf : P f) (hg : P g) :
    T ⟶ X ⊗ Y :=
  (existsUnique_lift (P := P) hf hg).choose.1

theorem lift_mem {T X Y : C} {f : T ⟶ X} {g : T ⟶ Y} (hf : P f) (hg : P g) :
    P (lift P hf hg) := (existsUnique_lift (P := P) hf hg).choose.2

theorem lift_fst {T X Y : C} {f : T ⟶ X} {g : T ⟶ Y} (hf : P f) (hg : P g) :
    lift P hf hg ≫ fst P X Y = f := (existsUnique_lift (P := P) hf hg).choose_spec.1.1

theorem lift_snd {T X Y : C} {f : T ⟶ X} {g : T ⟶ Y} (hf : P f) (hg : P g) :
    lift P hf hg ≫ snd P X Y = g := (existsUnique_lift (P := P) hf hg).choose_spec.1.2

theorem hom_ext {T X Y : C} {h k : T ⟶ X ⊗ Y} (hh : P h) (hk : P k)
    (e₁ : h ≫ fst P X Y = k ≫ fst P X Y) (e₂ : h ≫ snd P X Y = k ≫ snd P X Y) : h = k := by
  have hu := existsUnique_lift (P := P)
      (P.comp_mem _ _ hh (fst_mem P X Y)) (P.comp_mem _ _ hh (snd_mem P X Y))
  have h1 : (⟨h, hh⟩ : {h : T ⟶ X ⊗ Y // P h}) = hu.choose :=
    hu.choose_spec.2 ⟨h, hh⟩ ⟨rfl, rfl⟩
  have h2 : (⟨k, hk⟩ : {h : T ⟶ X ⊗ Y // P h}) = hu.choose :=
    hu.choose_spec.2 ⟨k, hk⟩ ⟨e₁.symm, e₂.symm⟩
  exact congrArg Subtype.val (h1.trans h2.symm)

/-- The wide subcategory of pure morphisms is cartesian monoidal, with the ambient premonoidal
tensor as its categorical product. -/
noncomputable instance wideSubcategoryCartesianMonoidal :
    CartesianMonoidalCategory (WideSubcategory P) :=
  { wideSubcategoryMonoidal P with
    isTerminalTensorUnit := wideIsTerminalUnit P
    fst := fun X Y => ⟨fst P X.obj Y.obj, fst_mem P _ _⟩
    snd := fun X Y => ⟨snd P X.obj Y.obj, snd_mem P _ _⟩
    fst_def := fun _ _ => rfl
    snd_def := fun _ _ => rfl
    tensorProductIsBinaryProduct := fun X Y =>
      Limits.BinaryFan.IsLimit.mk _
        (fun f g => ⟨lift P f.2 g.2, lift_mem P f.2 g.2⟩)
        (fun f g => Subtype.ext (lift_fst P f.2 g.2))
        (fun f g => Subtype.ext (lift_snd P f.2 g.2))
        (fun f g m h₁ h₂ => Subtype.ext
          (hom_ext P m.2 (lift_mem P f.2 g.2)
            (by
              have h := congrArg Subtype.val h₁
              simp only [WideSubcategory.comp_def, Limits.BinaryFan.mk_fst] at h
              exact h.trans (lift_fst P f.2 g.2).symm)
            (by
              have h := congrArg Subtype.val h₂
              simp only [WideSubcategory.comp_def, Limits.BinaryFan.mk_snd] at h
              exact h.trans (lift_snd P f.2 g.2).symm))) }

end IsCartesianSubcategory

end Cartesian

end PremonoidalCategory

end CategoryTheory
