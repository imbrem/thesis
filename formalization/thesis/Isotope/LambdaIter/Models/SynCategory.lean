import Isotope.LambdaIter.Models.Syntax
import Mathlib.CategoryTheory.Category.Basic

/-!
# The one-variable syntactic category of lambda-iter

The objects are the types of the signature; a morphism `A ⟶ B` is a term with
a single bound variable of type `A` and result type `B`, taken modulo the
equational theory `Eqv`.  Composition is `let`-binding under a shifted binder,
and the identity is the bound variable itself.

This is the author's "quotiented lambda-iter", as a category.

## What is proved, and what is not

**Proved: exactly the three category laws.**

| law | axiom used |
|---|---|
| `f ≫ 𝟙 = f` | `StructuralAxiom.letEta` (with `Tm.underBinder_bv_zero`) |
| `𝟙 ≫ g = g` | `StructuralAxiom.letBeta` at `Pure.bv` (with `instantiate_underBinder_bv_zero`) |
| `(f ≫ g) ≫ h = f ≫ (g ≫ h)` | `SequencingAxiom.bindLet` (with `underBinder_let₁_underBinder`) |

**Not proved, and deliberately out of scope for this file:** any premonoidal,
coproduct, distributive, or Elgot structure on this category.  In particular
there is *no* claim here that the syntactic category is a Freyd, distributive
Freyd, or Elgot Freyd category, and no iteration operator on hom-sets is
constructed.  The obstacle is not the quotient — `Eqv.iter` is a congruence,
so iteration *is* well defined on classes, and it appears as the `iter`
operation of `Syn S` in `Models/Syntax.lean`.  The obstacle is that the
iteration axioms are stated with `let`/`case` on de Bruijn terms while the
Elgot laws are stated with copairing, and bridging the two requires the whole
premonoidal and coproduct layer first.  That layer is not attempted here.

Note also that the value/pure subcategory is *not* constructed: `Pure` is
nowhere proved stable under `Eqv`, so the pure classes have no definition.
-/

namespace Isotope.LambdaIter

open LocallyNameless

universe u w q

namespace LocallyNameless.Tm

variable {ν : Type w} {Φ : Type q} {n : Nat}

/-- Opening the binder introduced by `underBinder` with the variable it
displaced is the identity.  This is the de Bruijn content of `𝟙 ≫ g = g`. -/
theorem instantiate_underBinder_bv_zero (t : Tm ν Φ (n + 1)) :
    Tm.instantiate (Tm.underBinder t) (.bv 0) = t := by
  simp only [Tm.underBinder, Tm.instantiate, Syntax.bsubst_rename]
  rw [Syntax.bsubst_congr (σ' := fun i => Tm.bv i)
    (fun i => by refine Fin.cases rfl (fun j => rfl) i)]
  rw [Syntax.bsubst_bv_eq_rename, Syntax.rename_id]

/-- Shifting a `let` whose body is already shifted.  The two renamings agree
because their common domain is `Fin 1`: this is the de Bruijn content of
associativity of composition in the one-variable syntactic category. -/
theorem underBinder_let₁_underBinder (b c : Tm ν Φ 1) :
    Tm.underBinder (.let₁ b (Tm.underBinder c)) =
      .let₁ (Tm.underBinder b) (Tm.underBinder (Tm.underBinder c)) := by
  rw [Tm.underBinder, Syntax.rename_let₁]
  congr 1
  simp only [Tm.underBinder, Syntax.rename_comp]
  exact Syntax.rename_congr (fun i => by refine Fin.cases rfl (fun j => j.elim0) i) c

end LocallyNameless.Tm

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
of type `A` and result type `B`, modulo `Eqv`.  This is exactly the carrier of
the syntactic model at the one-slot bound context. -/
def Arrow (S : Sig.{u}) (A B : SynCat S) : Type u :=
  El S (BoundCtx.nil.snoc A.ty) B.ty

/-- The hom-sets of the syntactic category are the carriers of the syntactic
model at a one-slot bound context. -/
theorem arrow_eq_el (A B : SynCat S) :
    Arrow S A B = (Syn S).El (BoundCtx.nil.snoc A.ty) B.ty := rfl

/-- The identity morphism: the bound variable. -/
def id' (A : SynCat S) : Arrow S A A :=
  mk (HasType.newest (Φ := S.Instr) (Γ := Ctx.nil) (β := .nil) (A := A.ty))

/-- Composition of typable one-variable terms: bind the first, then run the
second under the new binder. -/
def compCarrier {A B C : SynCat S}
    (f : Carrier S (BoundCtx.nil.snoc A.ty) B.ty)
    (g : Carrier S (BoundCtx.nil.snoc B.ty) C.ty) :
    Carrier S (BoundCtx.nil.snoc A.ty) C.ty :=
  ⟨.let₁ f.1 (Tm.underBinder g.1),
    f.2.elim fun hf => g.2.elim fun hg => ⟨.let₁ hf hg.underBinder⟩⟩

/-- Composition of morphisms of the syntactic category, well defined because
`Eqv` is a congruence for `let₁` and stable under typed renaming. -/
def comp {A B C : SynCat S} (f : Arrow S A B) (g : Arrow S B C) :
    Arrow S A C :=
  Quotient.map₂ compCarrier
    (fun _ _ hf _ _ hg =>
      Eqv.let₁ hf (Eqv.rename (TypedRenaming.underBinder .nil A.ty B.ty) hg))
    f g

@[simp] theorem comp_mk {A B C : SynCat S} {a b : Tm Empty S.Instr 1}
    (ha : HasType S.Instr Ctx.nil (BoundCtx.nil.snoc A.ty) a B.ty)
    (hb : HasType S.Instr Ctx.nil (BoundCtx.nil.snoc B.ty) b C.ty) :
    comp (A := A) (B := B) (C := C) (mk ha) (mk hb) =
      mk (HasType.let₁ ha hb.underBinder) := rfl

/-- `f ≫ 𝟙 = f`, by the `let`-eta axiom. -/
theorem comp_id' {A B : SynCat S} (f : Arrow S A B) : comp f (id' B) = f := by
  induction f using Syn.ind with
  | H t hf =>
    exact Quotient.sound
      (Eqv.ax (.structural (StructuralAxiom.letEta (pureEff := S.pureEff) t))
        (HasType.let₁ hf HasType.newest) hf)

/-- `𝟙 ≫ g = g`, by the `let`-beta axiom at the (pure) bound variable. -/
theorem id'_comp {A B : SynCat S} (g : Arrow S A B) : comp (id' A) g = g := by
  induction g using Syn.ind with
  | H t hg =>
    refine Quotient.sound (Eqv.ax (.structural ?_)
      (HasType.let₁ HasType.newest hg.underBinder) hg)
    have h := StructuralAxiom.letBeta (pureEff := S.pureEff)
      (a := (.bv 0 : Tm Empty S.Instr 1)) (b := Tm.underBinder t) Pure.bv
    rwa [Tm.instantiate_underBinder_bv_zero] at h

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
        refine Quotient.sound (Eqv.ax (.sequencing ?_)
          (HasType.let₁ (HasType.let₁ hf hg.underBinder) hh.underBinder)
          (HasType.let₁ hf (HasType.let₁ hg hh.underBinder).underBinder))
        have ax := SequencingAxiom.bindLet (pureEff := S.pureEff)
          tf (Tm.underBinder tg) (Tm.underBinder th)
        rwa [← Tm.underBinder_let₁_underBinder] at ax

/-- **The one-variable syntactic category of lambda-iter.**  Objects are the
types of the signature; morphisms are one-variable terms modulo the equational
theory.  Only the three category laws are established; see the module
docstring for the structure that is deliberately not built. -/
instance instCategory (S : Sig.{u}) : CategoryTheory.Category.{u, u} (SynCat S) where
  Hom := Arrow S
  id := id'
  comp := comp
  id_comp := id'_comp
  comp_id := comp_id'
  assoc := comp_assoc

@[simp] theorem category_id (A : SynCat S) :
    CategoryTheory.CategoryStruct.id A = id' A := rfl

@[simp] theorem category_comp {A B C : SynCat S} (f : A ⟶ B) (g : B ⟶ C) :
    CategoryTheory.CategoryStruct.comp f g = comp f g := rfl

end SynCat

end Syn

end Isotope.LambdaIter
