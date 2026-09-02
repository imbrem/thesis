import Isotope.LambdaIter.Models.SynIteration
import Isotope.CategoryTheory.Freyd.Elgot

/-!
# The syntactic Elgot laws, in Mathlib's binary-coproduct vocabulary

`Models/SynCoproduct.lean` and `Models/SynIteration.lean` build the coproduct
structure of the syntactic category by hand, as `cop`/`injl`/`injr`/`desc`.
This file transports the results along the canonical isomorphism
`cop A B ≅ A ⨿ B` and restates the three iteration laws using Mathlib's
`Limits.coprod`, so that they are *literally* the three fields of
`CategoryTheory.ElgotCategory` rather than something that resembles them.

## Honest boundary

The `ElgotCategory (SynCat S)` **instance is still not registered**, and this
file makes precise why: `CategoryTheory.Iteration` and
`CategoryTheory.ElgotCategory` both take `[HasBinaryCoproducts C]` /
`[HasFiniteCoproducts C]`, and only the binary half is available here.  The
finite half needs an initial object, which would need
`bv 0 ≈ abort (bv 0)` at type `empty`; `StructuralAxiom.emptyInitial` fires
only on a scrutinee of the literal form `.abort a` and so does not supply it.
See `Models/SynCoproduct.lean`.

So `SynCat.iterate'` is *not* declared as an `Iteration` instance either — the
class is available (it only needs binary coproducts), but declaring a global
instance on `SynCat` would be picked up by `ElgotCategory`-shaped searches
that cannot be discharged.  The three theorems below say everything the
instance would.

Uniformity and strength are still absent: see `Models/SynIteration.lean`.
-/

namespace Isotope.LambdaIter

open LocallyNameless CategoryTheory CategoryTheory.Limits

universe u

namespace Syn.SynCat

variable {S : Sig.{u}}

/-- The canonical isomorphism between the object-language coproduct and
Mathlib's chosen binary coproduct in the syntactic category. -/
noncomputable def copIso (A B : SynCat S) : cop A B ≅ A ⨿ B :=
  (isColimitBinaryCofan A B).coconePointUniqueUpToIso (colimit.isColimit (pair A B))

@[simp] theorem injl_copIso_hom (A B : SynCat S) :
    injl A B ≫ (copIso A B).hom = coprod.inl := by
  simpa using (isColimitBinaryCofan A B).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (pair A B)) ⟨WalkingPair.left⟩

@[simp] theorem injr_copIso_hom (A B : SynCat S) :
    injr A B ≫ (copIso A B).hom = coprod.inr := by
  simpa using (isColimitBinaryCofan A B).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (pair A B)) ⟨WalkingPair.right⟩

@[simp] theorem coprod_inl_copIso_inv (A B : SynCat S) :
    (coprod.inl : A ⟶ A ⨿ B) ≫ (copIso A B).inv = injl A B := by
  rw [← injl_copIso_hom A B, Category.assoc, Iso.hom_inv_id, Category.comp_id]

@[simp] theorem coprod_inr_copIso_inv (A B : SynCat S) :
    (coprod.inr : B ⟶ A ⨿ B) ≫ (copIso A B).inv = injr A B := by
  rw [← injr_copIso_hom A B, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The two copairings agree across the isomorphism. -/
@[simp] theorem copIso_inv_desc {A B C : SynCat S} (l : A ⟶ C) (r : B ⟶ C) :
    (copIso A B).inv ≫ desc l r = coprod.desc l r := by
  rw [Iso.inv_comp_eq]
  have h := desc_uniq ((copIso A B).hom ≫ coprod.desc l r)
  rw [← Category.assoc, ← Category.assoc, injl_copIso_hom, injr_copIso_hom,
    coprod.inl_desc, coprod.inr_desc] at h
  exact h.symm

/-- Iteration on the syntactic category, phrased with Mathlib's chosen binary
coproduct.  This is exactly the operation that a `CategoryTheory.Iteration`
instance would carry; it is left as a plain definition, see the module
docstring. -/
noncomputable def iterate' {A B : SynCat S} (f : A ⟶ B ⨿ A) : A ⟶ B :=
  iterate (f ≫ (copIso B A).inv)

/-- **Fixpoint**, in the shape of `CategoryTheory.ElgotCategory.fixpoint`. -/
theorem iterate'_fixpoint {A B : SynCat S} (f : A ⟶ B ⨿ A) :
    iterate' f = f ≫ coprod.desc (𝟙 B) (iterate' f) := by
  conv_lhs => rw [iterate', iterate_fixpoint (f ≫ (copIso B A).inv)]
  rw [Category.assoc, copIso_inv_desc]
  rfl

/-- **Naturality**, in the shape of `CategoryTheory.ElgotCategory.naturality`. -/
theorem iterate'_naturality {A B C : SynCat S} (f : A ⟶ B ⨿ A) (g : B ⟶ C) :
    iterate' f ≫ g = iterate' (f ≫ coprod.map g (𝟙 A)) := by
  have key : (copIso B A).inv ≫ desc (g ≫ injl C A) (injr C A)
      = coprod.map g (𝟙 A) ≫ (copIso C A).inv := by
    rw [copIso_inv_desc]
    refine coprod.hom_ext ?_ ?_ <;> simp [coprod.inl_desc, coprod.inr_desc]
  simp only [iterate']
  rw [iterate_naturality]
  simp only [Category.assoc]
  rw [key]

/-- **Codiagonal**, in the shape of `CategoryTheory.ElgotCategory.codiagonal`. -/
theorem iterate'_codiagonal {A B : SynCat S} (f : A ⟶ (B ⨿ A) ⨿ A) :
    iterate' (iterate' f) =
      iterate' (f ≫ coprod.desc (𝟙 (B ⨿ A)) (coprod.inr : A ⟶ B ⨿ A)) := by
  have key : (copIso (B ⨿ A) A).inv ≫
        (desc ((copIso B A).inv ≫ injl (cop B A) A) (injr (cop B A) A) ≫
          desc (𝟙 (cop B A)) (injr B A))
      = coprod.desc (𝟙 (B ⨿ A)) (coprod.inr : A ⟶ B ⨿ A) ≫ (copIso B A).inv := by
    rw [← Category.assoc, copIso_inv_desc]
    refine coprod.hom_ext ?_ ?_ <;>
      simp [coprod.inl_desc, coprod.inr_desc, injl_desc, injr_desc]
  simp only [iterate']
  rw [iterate_naturality, iterate_codiagonal]
  simp only [Category.assoc]
  rw [key]

/-- The iteration operator, packaged as a `CategoryTheory.Iteration`
structure.  A plain `def`, not an `instance`: see the module docstring. -/
noncomputable def iterationStructure (S : Sig.{u}) : Iteration (SynCat S) where
  iterate := iterate'

/-- **The syntactic category is an Elgot category as soon as it has an initial
object.**  The hypothesis `HasFiniteCoproducts` adds exactly one thing to the
binary coproducts already proved: an initial object.  So this theorem pins
down the whole remaining gap between the syntactic category and
`CategoryTheory.ElgotCategory` — the three equations are done, the initial
object is not.

The hypothesis is **not known to be satisfiable** for `SynCat S`; see the
module docstring and `Models/SynCoproduct.lean`.  Nothing downstream may
therefore describe the syntactic category as an Elgot category. -/
theorem elgotCategory_of_hasFiniteCoproducts (S : Sig.{u})
    [HasFiniteCoproducts (SynCat S)] :
    @ElgotCategory (SynCat S) _ _ (iterationStructure S) := by
  letI : Iteration (SynCat S) := iterationStructure S
  exact
    { fixpoint := fun f => iterate'_fixpoint f
      naturality := fun f g => iterate'_naturality f g
      codiagonal := fun f => iterate'_codiagonal f }

end Syn.SynCat

end Isotope.LambdaIter
