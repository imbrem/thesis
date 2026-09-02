import Mathlib.CategoryTheory.Category.Basic

/-!
# Idempotent envelope categories

The paper's `Ide(𝒞, d)` (`denotational-semantics-of-ssa.tex` L4927-4939): given an idempotent
`d_A : A ⟶ A` for every object, the morphisms `{f | d_A ≫ f ≫ d_B = f}` form a category whose
identity at `A` is `d_A`, not `𝟙 A`.

The paper stresses that this is *not* a subcategory of `𝒞` unless `d = 𝟙`.  It is nonetheless
a genuine `Category` in Mathlib's sense: `Category` demands `id_comp`/`comp_id` only for its
*own* identity, and `d_A` satisfies them inside the hom-subtype.  `Ide.id_eq` records that the
identity really is `d_A`.

## Honest boundary

Only the category structure is built.  The inheritance chain of L4940-5006 — coproducts,
Elgot structure, premonoidal, distributive, Freyd — is **not** formalised; the paper asserts
those for `d = pflush` without a displayed proof.  In particular nothing here shows that
`Ide(𝒞, d)` is an SSA model.
-/

universe v u

namespace CategoryTheory

/-- A family of idempotent endomorphisms, one at each object. -/
structure IdemFamily (C : Type u) [Category.{v} C] where
  /-- The idempotent at each object. -/
  d : ∀ X : C, X ⟶ X
  /-- Each `d X` is idempotent. -/
  idem : ∀ X : C, d X ≫ d X = d X

variable {C : Type u} [Category.{v} C] (D : IdemFamily C)

/-- The idempotent envelope `Ide(𝒞, d)`: the same objects, morphisms fixed by pre- and
post-composition with `d`, and identity `d`. -/
structure Ide (_D : IdemFamily C) where
  /-- Inclusion of objects. -/
  of ::
  /-- The underlying object. -/
  as : C

/-- Morphisms of `Ide(𝒞, d)` are absorbed by `d` on the left. -/
theorem IdemFamily.d_comp {X Y : C} {f : X ⟶ Y} (hf : D.d X ≫ f ≫ D.d Y = f) :
    D.d X ≫ f = f := by
  conv_lhs => rw [← hf]
  rw [← Category.assoc, D.idem, hf]

/-- Morphisms of `Ide(𝒞, d)` are absorbed by `d` on the right. -/
theorem IdemFamily.comp_d {X Y : C} {f : X ⟶ Y} (hf : D.d X ≫ f ≫ D.d Y = f) :
    f ≫ D.d Y = f := by
  conv_lhs => rw [← hf]
  rw [Category.assoc, Category.assoc, D.idem, hf]

instance : Quiver (Ide D) where
  Hom X Y := {f : X.as ⟶ Y.as // D.d X.as ≫ f ≫ D.d Y.as = f}

instance : CategoryStruct (Ide D) where
  id X := ⟨D.d X.as, by rw [D.idem, D.idem]⟩
  comp f g := ⟨f.1 ≫ g.1, by
    rw [Category.assoc, D.comp_d g.2, ← Category.assoc, D.d_comp f.2]⟩

instance : Category (Ide D) where
  id_comp f := Subtype.ext (D.d_comp f.2)
  comp_id f := Subtype.ext (D.comp_d f.2)
  assoc f g h := Subtype.ext (Category.assoc f.1 g.1 h.1)

/-- The identity of `Ide(𝒞, d)` at `X` is `d X`, not `𝟙 X`.  This is the paper's point at
L4936-4938. -/
theorem Ide.id_eq (X : Ide D) : (𝟙 X : X ⟶ X).1 = D.d X.as := rfl

/-- Composition in `Ide(𝒞, d)` is composition in `𝒞`. -/
theorem Ide.comp_eq {X Y Z : Ide D} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).1 = f.1 ≫ g.1 := rfl

/-- Every morphism of `𝒞` sandwiched by `d` is a morphism of `Ide(𝒞, d)`. -/
def Ide.homMk {X Y : Ide D} (f : X.as ⟶ Y.as) : X ⟶ Y :=
  ⟨D.d X.as ≫ f ≫ D.d Y.as, by
    simp only [Category.assoc]
    rw [← Category.assoc, D.idem, D.idem]⟩

end CategoryTheory
