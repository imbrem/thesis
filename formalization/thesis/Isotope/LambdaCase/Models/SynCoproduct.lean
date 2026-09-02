import Isotope.LambdaCase.Models.SynCategory
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Binary coproducts in the syntactic category of lambda-case

The object-language `coprod` is a binary coproduct in the one-variable
syntactic category of `Models/SynCategory.lean`, with the full universal
property as a `CategoryTheory.Limits.IsColimit`, hence
`HasBinaryCoproducts (SynCat S)`.

The injections are `inl`/`inr` applied to the bound variable, and the copairing
is `case` on the bound variable.  The laws come from four axioms of the
equational theory:

| law | axiom |
|---|---|
| `injl ≫ desc l r = l` | `letBeta` at `Pure.inl Pure.bv`, then `caseBetaL` |
| `injr ≫ desc l r = r` | `letBeta` at `Pure.inr Pure.bv`, then `caseBetaR` |
| `desc injl injr = 𝟙` | `caseEta` |
| `desc l r ≫ m = desc (l ≫ m) (r ≫ m)` | `bindLetCase` |

and uniqueness of the copairing follows formally from the last two, with no
further axiom.

## Honest boundary

* These are coproducts in the *whole* (effectful) syntactic category, which is
  what a distributive Freyd category asks of its computation category.  Nothing
  is claimed about a value/pure subcategory: `Pure` is nowhere proved stable
  under `Equiv`, so the pure classes have no definition here.
* The **empty type is not shown to be initial**, and no `HasFiniteCoproducts`
  instance is registered.  Uniqueness of a morphism `empty ⟶ C` would need
  `bv 0 ≈ abort (bv 0)` at type `empty`, and `Equiv.emptyInitial` fires only on
  a scrutinee of the literal form `.abort a`, so it does not supply that.  This
  is a reported gap in the presentation, **not** a proof of non-derivability:
  no separating model is constructed here.
* No monoidal, premonoidal, Freyd or distributive structure is constructed.
-/

namespace Isotope.LambdaCase

open LocallyNameless CategoryTheory

open Isotope.LambdaIter (Sig)

universe u

namespace Syn.SynCat

variable {S : Sig.{u}}

private abbrev bnil (S : Sig.{u}) : BoundCtx S.Ty 0 :=
  LambdaIter.LocallyNameless.BoundCtx.nil

/-- The object-language coproduct, as an object of the syntactic category. -/
@[reducible] def cop (A B : SynCat S) : SynCat S :=
  SynCat.of (LambdaIter.TypeFormers.coprod A.ty B.ty)

/-- The left injection. -/
def injl (A B : SynCat S) : A ⟶ cop A B :=
  mk (HasType.inl (B := B.ty)
    (HasType.newest (Φ := S.Instr) (Γ := LambdaIter.Ctx.nil) (β := bnil S)
      (A := A.ty)))

/-- The right injection. -/
def injr (A B : SynCat S) : B ⟶ cop A B :=
  mk (HasType.inr (A := A.ty)
    (HasType.newest (Φ := S.Instr) (Γ := LambdaIter.Ctx.nil) (β := bnil S)
      (A := B.ty)))

/-- The copairing of typable one-variable terms: `case` on the bound
variable. -/
def descCarrier {A B C : SynCat S}
    (l : Carrier S ((bnil S).snoc A.ty) C.ty)
    (r : Carrier S ((bnil S).snoc B.ty) C.ty) :
    Carrier S ((bnil S).snoc (cop A B).ty) C.ty :=
  ⟨.case (.bv 0) (Tm.underBinder l.1) (Tm.underBinder r.1),
    l.2.elim fun hl => r.2.elim fun hr =>
      ⟨HasType.case (A := A.ty) (B := B.ty) HasType.newest
        hl.underBinder hr.underBinder⟩⟩

/-- The copairing of two morphisms out of a coproduct, well defined because
`Equiv` is a congruence for `case` and stable under typed renaming. -/
def desc {A B C : SynCat S} (l : A ⟶ C) (r : B ⟶ C) : cop A B ⟶ C :=
  Quotient.map₂ descCarrier
    (fun _ _ hl _ _ hr =>
      LocallyNameless.Equiv.case (A := A.ty) (B := B.ty)
        (LocallyNameless.Equiv.refl HasType.newest)
        (LocallyNameless.Equiv.rename
          (LambdaIter.LocallyNameless.TypedRenaming.underBinder (bnil S)
            (cop A B).ty A.ty) hl)
        (LocallyNameless.Equiv.rename
          (LambdaIter.LocallyNameless.TypedRenaming.underBinder (bnil S)
            (cop A B).ty B.ty) hr))
    l r

theorem desc_mk {A B C : SynCat S} {a b : Tm Empty S.Instr 1}
    (ha : HasType S.Instr LambdaIter.Ctx.nil ((bnil S).snoc A.ty) a C.ty)
    (hb : HasType S.Instr LambdaIter.Ctx.nil ((bnil S).snoc B.ty) b C.ty) :
    desc (A := A) (B := B) (C := C) (mk ha) (mk hb) =
      mk (HasType.case (A := A.ty) (B := B.ty) HasType.newest
        ha.underBinder hb.underBinder) := rfl

/-- `desc` of the two injections is the identity, by the `case`-eta axiom. -/
theorem desc_injl_injr (A B : SynCat S) :
    desc (injl A B) (injr A B) = 𝟙 (cop A B) :=
  Quotient.sound
    (LocallyNameless.Equiv.caseEta (pureEff := S.pureEff)
      (A := A.ty) (B := B.ty) HasType.newest)

/-- Postcomposition distributes over `desc`, by the `let`-of-`case` commuting
conversion. -/
theorem desc_comp {A B C D : SynCat S} (l : A ⟶ C) (r : B ⟶ C) (m : C ⟶ D) :
    desc l r ≫ m = desc (l ≫ m) (r ≫ m) := by
  induction l using Syn.ind with
  | H tl hl =>
    induction r using Syn.ind with
    | H tr hr =>
      induction m using Syn.ind with
      | H tm hm =>
        have ax := LocallyNameless.Equiv.bindLetCase (pureEff := S.pureEff)
          (A := A.ty) (B := B.ty) HasType.newest hl.underBinder hr.underBinder
          hm.underBinder
        rw [← Tm.underBinder_let₁_underBinder,
          ← Tm.underBinder_let₁_underBinder] at ax
        exact Quotient.sound ax

/-- `injl ≫ desc l r = l`, by `let`-beta at the pure term `inl (bv 0)`,
then `case`-beta, then the identity law. -/
theorem injl_desc {A B C : SynCat S} (l : A ⟶ C) (r : B ⟶ C) :
    injl A B ≫ desc l r = l := by
  induction l using Syn.ind with
  | H tl hl =>
    induction r using Syn.ind with
    | H tr hr =>
      have step1 := LocallyNameless.Equiv.letBeta (pureEff := S.pureEff)
        (a := ((Tm.bv 0).inl : Tm Empty S.Instr 1))
        (b := ((Tm.bv 0).case (Tm.underBinder (Tm.underBinder tl))
          (Tm.underBinder (Tm.underBinder tr))))
        (LocallyNameless.Pure.inl LocallyNameless.Pure.bv)
        (HasType.inl (B := B.ty) HasType.newest)
        (HasType.case (A := A.ty) (B := B.ty) HasType.newest
          hl.underBinder.underBinder hr.underBinder.underBinder)
      rw [Tm.instantiate_case_inl] at step1
      have step2 := LocallyNameless.Equiv.caseBetaL (pureEff := S.pureEff)
        (A := A.ty) (B := B.ty) (e := (Tm.bv 0 : Tm Empty S.Instr 1))
        HasType.newest hl.underBinder hr.underBinder
      have step3 : LocallyNameless.Equiv (Φ := S.Instr) S.pureEff
          LambdaIter.Ctx.nil ((bnil S).snoc A.ty)
          (.let₁ (.bv 0) (Tm.underBinder tl)) tl C.ty :=
        Syn.equiv_of_mk_eq
          (h := HasType.let₁ HasType.newest hl.underBinder) (h' := hl)
          (SynCat.id'_comp (mk hl))
      have key : LocallyNameless.Equiv (Φ := S.Instr) S.pureEff
          LambdaIter.Ctx.nil ((bnil S).snoc A.ty)
          (.let₁ ((Tm.bv 0).inl)
            (Tm.underBinder ((Tm.bv 0).case (Tm.underBinder tl)
              (Tm.underBinder tr))))
          tl C.ty := by
        rw [Tm.underBinder_case_underBinder]
        exact (step1.trans step2).trans step3
      exact Quotient.sound key

/-- `injr ≫ desc l r = r`, by `let`-beta at the pure term `inr (bv 0)`,
then `case`-beta, then the identity law. -/
theorem injr_desc {A B C : SynCat S} (l : A ⟶ C) (r : B ⟶ C) :
    injr A B ≫ desc l r = r := by
  induction l using Syn.ind with
  | H tl hl =>
    induction r using Syn.ind with
    | H tr hr =>
      have step1 := LocallyNameless.Equiv.letBeta (pureEff := S.pureEff)
        (a := ((Tm.bv 0).inr : Tm Empty S.Instr 1))
        (b := ((Tm.bv 0).case (Tm.underBinder (Tm.underBinder tl))
          (Tm.underBinder (Tm.underBinder tr))))
        (LocallyNameless.Pure.inr LocallyNameless.Pure.bv)
        (HasType.inr (A := A.ty) HasType.newest)
        (HasType.case (A := A.ty) (B := B.ty) HasType.newest
          hl.underBinder.underBinder hr.underBinder.underBinder)
      rw [Tm.instantiate_case_inr] at step1
      have step2 := LocallyNameless.Equiv.caseBetaR (pureEff := S.pureEff)
        (A := A.ty) (B := B.ty) (e := (Tm.bv 0 : Tm Empty S.Instr 1))
        HasType.newest hl.underBinder hr.underBinder
      have step3 : LocallyNameless.Equiv (Φ := S.Instr) S.pureEff
          LambdaIter.Ctx.nil ((bnil S).snoc B.ty)
          (.let₁ (.bv 0) (Tm.underBinder tr)) tr C.ty :=
        Syn.equiv_of_mk_eq
          (h := HasType.let₁ HasType.newest hr.underBinder) (h' := hr)
          (SynCat.id'_comp (mk hr))
      have key : LocallyNameless.Equiv (Φ := S.Instr) S.pureEff
          LambdaIter.Ctx.nil ((bnil S).snoc B.ty)
          (.let₁ ((Tm.bv 0).inr)
            (Tm.underBinder ((Tm.bv 0).case (Tm.underBinder tl)
              (Tm.underBinder tr))))
          tr C.ty := by
        rw [Tm.underBinder_case_underBinder]
        exact (step1.trans step2).trans step3
      exact Quotient.sound key

/-- Uniqueness of the copairing: any morphism out of a coproduct is the
copairing of its restrictions.  This follows formally from `desc_injl_injr`
and `desc_comp`; no further axiom of the theory is used. -/
theorem desc_uniq {A B C : SynCat S} (m : cop A B ⟶ C) :
    m = desc (injl A B ≫ m) (injr A B ≫ m) := by
  rw [← desc_comp, desc_injl_injr, Category.id_comp]

/-- **The object-language coproduct is a coproduct in the syntactic
category**, with the full universal property. -/
def isColimitBinaryCofan (A B : SynCat S) :
    Limits.IsColimit (Limits.BinaryCofan.mk (injl A B) (injr A B)) :=
  Limits.BinaryCofan.isColimitMk
    (fun s => desc s.inl s.inr)
    (fun _ => injl_desc _ _)
    (fun _ => injr_desc _ _)
    (fun _ m hl hr => by rw [desc_uniq m, hl, hr])

instance hasBinaryCoproduct (A B : SynCat S) :
    Limits.HasBinaryCoproduct A B :=
  ⟨⟨⟨_, isColimitBinaryCofan A B⟩⟩⟩

/-- The syntactic category of lambda-case has all binary coproducts. -/
instance hasBinaryCoproducts (S : Sig.{u}) :
    Limits.HasBinaryCoproducts (SynCat S) :=
  Limits.hasBinaryCoproducts_of_hasColimit_pair _

end Syn.SynCat

end Isotope.LambdaCase
