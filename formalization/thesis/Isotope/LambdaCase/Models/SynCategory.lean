import Isotope.LambdaCase.Models.Syntax
import Isotope.LambdaCase.Metatheory.EquivSubst
import Isotope.LambdaCase.Metatheory.Shift
import Mathlib.CategoryTheory.Category.Basic

/-!
# The one-variable syntactic category of lambda-case

The objects are the types of the signature; a morphism `A ⟶ B` is a term with
a single bound variable of type `A` and result type `B`, taken modulo the
equational theory `Equiv`.  Composition is `let`-binding under a shifted
binder, and the identity is the bound variable itself.

This is the author's "quotiented lambda-case", as a category.  Composition is
well defined on classes precisely because `Equiv` is a congruence for `let₁`
and stable under typed renaming (`Equiv.rename`, in
`Isotope/LambdaCase/Metatheory/EquivSubst.lean`).

## What is proved, and what is not

**Proved: exactly the three category laws.**

| law | axiom used |
|---|---|
| `f ≫ 𝟙 = f` | `Equiv.letEta` |
| `𝟙 ≫ g = g` | `Equiv.letBeta` at `Pure.bv`, with `instantiate_underBinder_bv_zero` |
| `(f ≫ g) ≫ h = f ≫ (g ≫ h)` | `Equiv.bindLet`, with `underBinder_let₁_underBinder` |

**Not proved, and deliberately out of scope:** any premonoidal, Freyd,
cartesian-value or distributive structure on this category.  Two obstacles are
worth naming, because they are properties of the presentation and not of the
formalization:

* the value/pure subcategory has no definition, because `Pure` is nowhere
  proved stable under `Equiv`;
* the empty type is **not** available as an initial object.  `Equiv.emptyInitial`
  fires only when the scrutinee of a `let` is literally of the form `.abort a`,
  so it does not prove `bv 0 ≈ abort (bv 0)` at the empty type, and uniqueness
  of a morphism out of `empty` fails for that reason.  This is a gap in the
  presentation; no separating model is built here, so nothing below claims the
  law is *underivable*.

Binary coproducts, by contrast, are available; they are in
`Isotope/LambdaCase/Models/SynCoproduct.lean`.
-/

namespace Isotope.LambdaCase

open LocallyNameless

open Isotope.LambdaIter (Sig)

/-- The empty bound context, spelled without the `BoundCtx` abbreviation (which
is not a namespace here). -/
private abbrev bnil (S : Sig.{u}) : BoundCtx S.Ty 0 :=
  LambdaIter.LocallyNameless.BoundCtx.nil

universe u

namespace Syn

variable {S : Sig.{u}}

/-- Objects of the one-variable syntactic category: the types of `S`.  A type
synonym, so that the `Category` instance does not attach to `Sig.Ty` itself. -/
def SynCat (S : Sig.{u}) : Type u := S.Ty

namespace SynCat

/-- View a type of the signature as an object of the syntactic category. -/
@[reducible] def of (A : S.Ty) : SynCat S := A

/-- The underlying type of an object of the syntactic category. -/
@[reducible] def ty (A : SynCat S) : S.Ty := A

/-- Morphisms `A ⟶ B` of the syntactic category: terms with one bound variable
of type `A` and result type `B`, modulo `Equiv`.  This is exactly the carrier
of the syntactic model at the one-slot bound context. -/
def Arrow (S : Sig.{u}) (A B : SynCat S) : Type u :=
  El S ((bnil S).snoc A.ty) B.ty

/-- The hom-sets of the syntactic category are the carriers of the syntactic
model at a one-slot bound context. -/
theorem arrow_eq_el (A B : SynCat S) :
    Arrow S A B = (Syn S).El ((bnil S).snoc A.ty) B.ty := rfl

/-- The identity morphism: the bound variable. -/
def id' (A : SynCat S) : Arrow S A A :=
  mk (HasType.newest (Φ := S.Instr) (Γ := LambdaIter.Ctx.nil) (β := bnil S)
    (A := A.ty))

/-- Composition of typable one-variable terms: bind the first, then run the
second under the new binder. -/
def compCarrier {A B C : SynCat S}
    (f : Carrier S ((bnil S).snoc A.ty) B.ty)
    (g : Carrier S ((bnil S).snoc B.ty) C.ty) :
    Carrier S ((bnil S).snoc A.ty) C.ty :=
  ⟨.let₁ f.1 (Tm.underBinder g.1),
    f.2.elim fun hf => g.2.elim fun hg => ⟨.let₁ hf hg.underBinder⟩⟩

/-- Composition of morphisms of the syntactic category, well defined because
`Equiv` is a congruence for `let₁` and stable under typed renaming. -/
def comp {A B C : SynCat S} (f : Arrow S A B) (g : Arrow S B C) :
    Arrow S A C :=
  Quotient.map₂ compCarrier
    (fun _ _ hf _ _ hg =>
      LocallyNameless.Equiv.let₁ hf
        (LocallyNameless.Equiv.rename
          (LambdaIter.LocallyNameless.TypedRenaming.underBinder (bnil S) A.ty B.ty)
          hg))
    f g

@[simp] theorem comp_mk {A B C : SynCat S} {a b : Tm Empty S.Instr 1}
    (ha : HasType S.Instr LambdaIter.Ctx.nil ((bnil S).snoc A.ty) a B.ty)
    (hb : HasType S.Instr LambdaIter.Ctx.nil ((bnil S).snoc B.ty) b C.ty) :
    comp (A := A) (B := B) (C := C) (mk ha) (mk hb) =
      mk (HasType.let₁ ha hb.underBinder) := rfl

/-- `f ≫ 𝟙 = f`, by the `let`-eta axiom. -/
theorem comp_id' {A B : SynCat S} (f : Arrow S A B) : comp f (id' B) = f := by
  induction f using Syn.ind with
  | H t hf => exact Quotient.sound (LocallyNameless.Equiv.letEta hf)

/-- `𝟙 ≫ g = g`, by the `let`-beta axiom at the (pure) bound variable. -/
theorem id'_comp {A B : SynCat S} (g : Arrow S A B) : comp (id' A) g = g := by
  induction g using Syn.ind with
  | H t hg =>
    have h := LocallyNameless.Equiv.letBeta (pureEff := S.pureEff)
      (a := (.bv 0 : Tm Empty S.Instr 1)) (b := Tm.underBinder t)
      LocallyNameless.Pure.bv HasType.newest hg.underBinder
    rw [Tm.instantiate_underBinder_bv_zero] at h
    exact Quotient.sound h

/-- Associativity of composition, by the `let`-of-`let` sequencing axiom. -/
theorem comp_assoc {A B C D : SynCat S}
    (f : Arrow S A B) (g : Arrow S B C) (h : Arrow S C D) :
    comp (comp f g) h = comp f (comp g h) := by
  induction f using Syn.ind with
  | H tf hf =>
    induction g using Syn.ind with
    | H tg hg =>
      induction h using Syn.ind with
      | H th hh =>
        have ax := LocallyNameless.Equiv.bindLet (pureEff := S.pureEff) hf
          hg.underBinder hh.underBinder
        rw [← Tm.underBinder_let₁_underBinder] at ax
        exact Quotient.sound ax

/-- **The one-variable syntactic category of lambda-case.**  Objects are the
types of the signature; morphisms are one-variable terms modulo the equational
theory.  Only the three category laws are established here; see the module
docstring for the structure that is deliberately not built. -/
instance instCategory (S : Sig.{u}) :
    CategoryTheory.Category.{u, u} (SynCat S) where
  Hom := Arrow S
  id := id'
  comp := comp
  id_comp := id'_comp
  comp_id := comp_id'
  assoc := comp_assoc

/-- The categorical identity is the bound variable.  Deliberately **not** a
`simp` lemma: rewriting `𝟙` and `≫` into `id'` and `comp` would take goals out
of the vocabulary of Mathlib's category simp set. -/
theorem category_id (A : SynCat S) :
    CategoryTheory.CategoryStruct.id A = id' A := rfl

/-- Categorical composition is `let`-binding under a shifted binder.  Not a
`simp` lemma, for the same reason as `category_id`. -/
theorem category_comp {A B C : SynCat S} (f : A ⟶ B) (g : B ⟶ C) :
    CategoryTheory.CategoryStruct.comp f g = comp f g := rfl

end SynCat

end Syn

end Isotope.LambdaCase
