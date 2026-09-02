import Isotope.LambdaIter.Models.SynCategory
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Binary coproducts and iteration in the syntactic category

This file adds to the one-variable syntactic category of
`Models/SynCategory.lean`:

* **binary coproducts**, with the full universal property as a
  `CategoryTheory.Limits.IsColimit`, hence `HasBinaryCoproducts (SynCat S)`;
* the **iteration operator** on hom-sets, sending `f : A ⟶ B + A` to
  `iterate f : A ⟶ B`, well defined on classes because `Eqv.iter` is a
  congruence.

The coproduct object is the object-language `coprod`, the injections are
`inl`/`inr` applied to the bound variable, and the copairing is `case` on the
bound variable.  The laws come from four axioms of the equational theory:

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
  what a distributive Freyd category asks of its computation category.
  Nothing is claimed about a value/pure subcategory: `Pure` is nowhere proved
  stable under `Eqv`, so the pure classes have no definition here.
* The **empty type is not shown to be initial**.  Uniqueness of a morphism
  `empty ⟶ C` would need `bv 0 ≈ abort (bv 0)` at type `empty`, and
  `StructuralAxiom.emptyInitial` fires only on a scrutinee of the literal form
  `.abort a`, so it does not supply that.  This is a reported gap in the
  presentation, **not** a proof of non-derivability — no separating model is
  constructed here.  Its consequence is that `HasFiniteCoproducts` is
  unavailable, which is what blocks registering an `ElgotCategory` instance in
  `Models/SynIteration.lean`.
* `SynCat.iterate` is only *defined* here, together with well-definedness.
  **No Elgot law is proved for it.**  Every such law (fixpoint, naturality,
  codiagonal, uniformity) is phrased with copairing on one side and with
  `let`/`case` on de Bruijn terms in `IterationAxiom` on the other, and
  bridging the two also needs the premonoidal and distributive layers, which
  this development does not build.  Issue #57's iteration half therefore
  remains open; this file narrows it rather than closing it.
* No monoidal or premonoidal structure (`tensor`, `unit`) is constructed.
-/

namespace Isotope.LambdaIter

open LocallyNameless CategoryTheory

universe u w q

namespace LocallyNameless.Tm

variable {ν : Type w} {Φ : Type q}

/-- Two renamings of a one-variable term agree as soon as they agree at index
`0`, since that is the only index. -/
theorem rename_eq_of_zero {m : Nat} (ρ ρ' : Fin 1 → Fin m) (h : ρ 0 = ρ' 0)
    (c : Tm ν Φ 1) : Tm.rename ρ c = Tm.rename ρ' c :=
  Syntax.rename_congr (fun i => by refine Fin.cases h (fun j => j.elim0) i) c

/-- A substitution and a renaming act alike on a one-variable term as soon as
they agree at index `0`. -/
theorem bsubst_eq_rename_of_zero {m : Nat} (σ : Fin 1 → Tm ν Φ m)
    (ρ : Fin 1 → Fin m) (h : σ 0 = Tm.bv (ρ 0)) (c : Tm ν Φ 1) :
    Tm.bsubst σ c = Tm.rename ρ c := by
  rw [Syntax.bsubst_congr (σ' := fun i => Tm.bv (ρ i))
    (fun i => by refine Fin.cases h (fun j => j.elim0) i)]
  exact Syntax.bsubst_bv_eq_rename ρ c

/-- Shifting under an extra binder a one-variable term that is already
shifted.  The two renamings agree because their common domain is `Fin 1`. -/
theorem rename_upRen_underBinder (ρ : Fin 1 → Fin 2) (c : Tm ν Φ 1) :
    Tm.rename (Syntax.upRen ρ) (Tm.underBinder c) =
      Tm.underBinder (Tm.underBinder c) := by
  simp only [Tm.underBinder, Syntax.rename_comp]
  refine rename_eq_of_zero _ _ ?_ c
  rfl

/-- Any substitution sending index `0` to `bv 0` takes the double shift of a
one-variable term back to its single shift. -/
theorem bsubst_upSub_underBinder (σ : Fin 2 → Tm ν Φ 1) (c : Tm ν Φ 1) :
    Tm.bsubst (Syntax.upSub σ) (Tm.underBinder (Tm.underBinder c)) =
      Tm.underBinder c := by
  simp only [Tm.underBinder, Syntax.bsubst_rename]
  refine bsubst_eq_rename_of_zero _ _ ?_ c
  rfl

/-- Shifting a `case` on the bound variable whose branches are already
shifted. -/
theorem underBinder_case_underBinder (l r : Tm ν Φ 1) :
    Tm.underBinder ((Tm.bv 0).case (Tm.underBinder l) (Tm.underBinder r)) =
      (Tm.bv 0).case (Tm.underBinder (Tm.underBinder l))
        (Tm.underBinder (Tm.underBinder r)) :=
  congrArg₂ (fun x y : Tm ν Φ 3 => (Tm.bv 0).case x y)
    (rename_upRen_underBinder _ l) (rename_upRen_underBinder _ r)

/-- Opening the `case` redex produced by `injl ≫ desc l r`. -/
theorem instantiate_case_inl (l r : Tm ν Φ 1) :
    Tm.instantiate
        ((Tm.bv 0).case (Tm.underBinder (Tm.underBinder l))
          (Tm.underBinder (Tm.underBinder r)))
        ((Tm.bv 0).inl) =
      ((Tm.bv 0).inl).case (Tm.underBinder l) (Tm.underBinder r) :=
  congrArg₂ (fun x y : Tm ν Φ 2 => ((Tm.bv 0).inl).case x y)
    (bsubst_upSub_underBinder _ l) (bsubst_upSub_underBinder _ r)

/-- Opening the `case` redex produced by `injr ≫ desc l r`. -/
theorem instantiate_case_inr (l r : Tm ν Φ 1) :
    Tm.instantiate
        ((Tm.bv 0).case (Tm.underBinder (Tm.underBinder l))
          (Tm.underBinder (Tm.underBinder r)))
        ((Tm.bv 0).inr) =
      ((Tm.bv 0).inr).case (Tm.underBinder l) (Tm.underBinder r) :=
  congrArg₂ (fun x y : Tm ν Φ 2 => ((Tm.bv 0).inr).case x y)
    (bsubst_upSub_underBinder _ l) (bsubst_upSub_underBinder _ r)

end LocallyNameless.Tm

namespace Syn.SynCat

variable {S : Sig.{u}}

/-- The object-language coproduct, as an object of the syntactic category. -/
@[reducible] def cop (A B : SynCat S) : SynCat S :=
  SynCat.of (LambdaIter.coprod A.ty B.ty)

/-- The left injection. -/
def injl (A B : SynCat S) : A ⟶ cop A B :=
  mk (HasType.inl (B := B.ty)
    (HasType.newest (Φ := S.Instr) (Γ := Ctx.nil) (β := .nil) (A := A.ty)))

/-- The right injection. -/
def injr (A B : SynCat S) : B ⟶ cop A B :=
  mk (HasType.inr (A := A.ty)
    (HasType.newest (Φ := S.Instr) (Γ := Ctx.nil) (β := .nil) (A := B.ty)))

/-- The copairing of typable one-variable terms: `case` on the bound
variable. -/
def descCarrier {A B C : SynCat S}
    (l : Carrier S (BoundCtx.nil.snoc A.ty) C.ty)
    (r : Carrier S (BoundCtx.nil.snoc B.ty) C.ty) :
    Carrier S (BoundCtx.nil.snoc (cop A B).ty) C.ty :=
  ⟨.case (.bv 0) (Tm.underBinder l.1) (Tm.underBinder r.1),
    l.2.elim fun hl => r.2.elim fun hr =>
      ⟨HasType.case (A := A.ty) (B := B.ty) HasType.newest
        hl.underBinder hr.underBinder⟩⟩

/-- The copairing of two morphisms out of a coproduct, well defined because
`Eqv` is a congruence for `case` and stable under typed renaming. -/
def desc {A B C : SynCat S} (l : A ⟶ C) (r : B ⟶ C) : cop A B ⟶ C :=
  Quotient.map₂ descCarrier
    (fun _ _ hl _ _ hr =>
      Eqv.case (A := A.ty) (B := B.ty) (Eqv.refl HasType.newest)
        (Eqv.rename (TypedRenaming.underBinder .nil (cop A B).ty A.ty) hl)
        (Eqv.rename (TypedRenaming.underBinder .nil (cop A B).ty B.ty) hr))
    l r

theorem desc_mk {A B C : SynCat S} {a b : Tm Empty S.Instr 1}
    (ha : HasType S.Instr Ctx.nil (BoundCtx.nil.snoc A.ty) a C.ty)
    (hb : HasType S.Instr Ctx.nil (BoundCtx.nil.snoc B.ty) b C.ty) :
    desc (A := A) (B := B) (C := C) (mk ha) (mk hb) =
      mk (HasType.case (A := A.ty) (B := B.ty) HasType.newest
        ha.underBinder hb.underBinder) := rfl

/-- `desc` of the two injections is the identity, by the `case`-eta axiom. -/
theorem desc_injl_injr (A B : SynCat S) :
    desc (injl A B) (injr A B) = 𝟙 (cop A B) := by
  refine Quotient.sound ?_
  exact Eqv.ax (Φ := S.Instr)
    (.structural (StructuralAxiom.caseEta (pureEff := S.pureEff)
      (.bv (0 : Fin 1))))
    (HasType.case (A := A.ty) (B := B.ty) HasType.newest
      (HasType.inl (B := B.ty) HasType.newest).underBinder
      (HasType.inr (A := A.ty) HasType.newest).underBinder)
    HasType.newest

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
        refine Quotient.sound ?_
        refine Eqv.ax (Φ := S.Instr) (.sequencing ?_)
          (HasType.let₁
            (HasType.case (A := A.ty) (B := B.ty) HasType.newest
              hl.underBinder hr.underBinder)
            hm.underBinder)
          (HasType.case (A := A.ty) (B := B.ty) HasType.newest
            (HasType.let₁ hl hm.underBinder).underBinder
            (HasType.let₁ hr hm.underBinder).underBinder)
        have ax := SequencingAxiom.bindLetCase (pureEff := S.pureEff)
          (.bv (0 : Fin 1)) (Tm.underBinder tl) (Tm.underBinder tr)
          (Tm.underBinder tm)
        rwa [← Tm.underBinder_let₁_underBinder,
          ← Tm.underBinder_let₁_underBinder] at ax

/-- `injl ≫ desc l r = l`, by `let`-beta at the pure term `inl (bv 0)`,
then `case`-beta, then the identity law. -/
theorem injl_desc {A B C : SynCat S} (l : A ⟶ C) (r : B ⟶ C) :
    injl A B ≫ desc l r = l := by
  induction l using Syn.ind with
  | H tl hl =>
    induction r using Syn.ind with
    | H tr hr =>
      have hbig : HasType S.Instr Ctx.nil (BoundCtx.nil.snoc A.ty)
          (.let₁ (.inl (.bv 0))
            ((Tm.bv 0).case (Tm.underBinder (Tm.underBinder tl))
              (Tm.underBinder (Tm.underBinder tr)))) C.ty :=
        HasType.let₁ (HasType.inl (B := B.ty) HasType.newest)
          (HasType.case (A := A.ty) (B := B.ty) HasType.newest
            hl.underBinder.underBinder hr.underBinder.underBinder)
      have hmid : HasType S.Instr Ctx.nil (BoundCtx.nil.snoc A.ty)
          (((Tm.bv 0).inl).case (Tm.underBinder tl) (Tm.underBinder tr))
          C.ty :=
        HasType.case (A := A.ty) (B := B.ty)
          (HasType.inl (B := B.ty) HasType.newest)
          hl.underBinder hr.underBinder
      have hlet : HasType S.Instr Ctx.nil (BoundCtx.nil.snoc A.ty)
          (.let₁ (.bv 0) (Tm.underBinder tl)) C.ty :=
        HasType.let₁ HasType.newest hl.underBinder
      have step1 : Eqv (Φ := S.Instr) S.pureEff Ctx.nil (BoundCtx.nil.snoc A.ty)
          (.let₁ ((Tm.bv 0).inl)
            ((Tm.bv 0).case (Tm.underBinder (Tm.underBinder tl))
              (Tm.underBinder (Tm.underBinder tr))))
          (((Tm.bv 0).inl).case (Tm.underBinder tl) (Tm.underBinder tr))
          C.ty := by
        refine Eqv.ax (Φ := S.Instr) (.structural ?_) hbig hmid
        have ax := StructuralAxiom.letBeta (pureEff := S.pureEff)
          (a := ((Tm.bv 0).inl : Tm Empty S.Instr 1))
          (b := ((Tm.bv 0).case (Tm.underBinder (Tm.underBinder tl))
            (Tm.underBinder (Tm.underBinder tr))))
          (Pure.inl Pure.bv)
        rwa [Tm.instantiate_case_inl] at ax
      have step2 : Eqv (Φ := S.Instr) S.pureEff Ctx.nil (BoundCtx.nil.snoc A.ty)
          (((Tm.bv 0).inl).case (Tm.underBinder tl) (Tm.underBinder tr))
          (.let₁ (.bv 0) (Tm.underBinder tl)) C.ty :=
        Eqv.ax (Φ := S.Instr)
          (.structural (StructuralAxiom.caseBetaL (pureEff := S.pureEff)
            (.bv (0 : Fin 1)) (Tm.underBinder tl) (Tm.underBinder tr)))
          hmid hlet
      have step3 : Eqv (Φ := S.Instr) S.pureEff Ctx.nil (BoundCtx.nil.snoc A.ty)
          (.let₁ (.bv 0) (Tm.underBinder tl)) tl C.ty :=
        Syn.eqv_of_mk_eq (h := hlet) (h' := hl) (id'_comp (mk hl))
      have key : Eqv (Φ := S.Instr) S.pureEff Ctx.nil (BoundCtx.nil.snoc A.ty)
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
      have hbig : HasType S.Instr Ctx.nil (BoundCtx.nil.snoc B.ty)
          (.let₁ (.inr (.bv 0))
            ((Tm.bv 0).case (Tm.underBinder (Tm.underBinder tl))
              (Tm.underBinder (Tm.underBinder tr)))) C.ty :=
        HasType.let₁ (HasType.inr (A := A.ty) HasType.newest)
          (HasType.case (A := A.ty) (B := B.ty) HasType.newest
            hl.underBinder.underBinder hr.underBinder.underBinder)
      have hmid : HasType S.Instr Ctx.nil (BoundCtx.nil.snoc B.ty)
          (((Tm.bv 0).inr).case (Tm.underBinder tl) (Tm.underBinder tr))
          C.ty :=
        HasType.case (A := A.ty) (B := B.ty)
          (HasType.inr (A := A.ty) HasType.newest)
          hl.underBinder hr.underBinder
      have hlet : HasType S.Instr Ctx.nil (BoundCtx.nil.snoc B.ty)
          (.let₁ (.bv 0) (Tm.underBinder tr)) C.ty :=
        HasType.let₁ HasType.newest hr.underBinder
      have step1 : Eqv (Φ := S.Instr) S.pureEff Ctx.nil (BoundCtx.nil.snoc B.ty)
          (.let₁ ((Tm.bv 0).inr)
            ((Tm.bv 0).case (Tm.underBinder (Tm.underBinder tl))
              (Tm.underBinder (Tm.underBinder tr))))
          (((Tm.bv 0).inr).case (Tm.underBinder tl) (Tm.underBinder tr))
          C.ty := by
        refine Eqv.ax (Φ := S.Instr) (.structural ?_) hbig hmid
        have ax := StructuralAxiom.letBeta (pureEff := S.pureEff)
          (a := ((Tm.bv 0).inr : Tm Empty S.Instr 1))
          (b := ((Tm.bv 0).case (Tm.underBinder (Tm.underBinder tl))
            (Tm.underBinder (Tm.underBinder tr))))
          (Pure.inr Pure.bv)
        rwa [Tm.instantiate_case_inr] at ax
      have step2 : Eqv (Φ := S.Instr) S.pureEff Ctx.nil (BoundCtx.nil.snoc B.ty)
          (((Tm.bv 0).inr).case (Tm.underBinder tl) (Tm.underBinder tr))
          (.let₁ (.bv 0) (Tm.underBinder tr)) C.ty :=
        Eqv.ax (Φ := S.Instr)
          (.structural (StructuralAxiom.caseBetaR (pureEff := S.pureEff)
            (.bv (0 : Fin 1)) (Tm.underBinder tl) (Tm.underBinder tr)))
          hmid hlet
      have step3 : Eqv (Φ := S.Instr) S.pureEff Ctx.nil (BoundCtx.nil.snoc B.ty)
          (.let₁ (.bv 0) (Tm.underBinder tr)) tr C.ty :=
        Syn.eqv_of_mk_eq (h := hlet) (h' := hr) (id'_comp (mk hr))
      have key : Eqv (Φ := S.Instr) S.pureEff Ctx.nil (BoundCtx.nil.snoc B.ty)
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
    (fun s => injl_desc _ _)
    (fun s => injr_desc _ _)
    (fun s m hl hr => by rw [desc_uniq m, hl, hr])

instance hasBinaryCoproduct (A B : SynCat S) :
    Limits.HasBinaryCoproduct A B :=
  ⟨⟨⟨_, isColimitBinaryCofan A B⟩⟩⟩

/-- The syntactic category has all binary coproducts. -/
instance hasBinaryCoproducts (S : Sig.{u}) :
    Limits.HasBinaryCoproducts (SynCat S) :=
  Limits.hasBinaryCoproducts_of_hasColimit_pair _

/-- Iteration on typable one-variable terms. -/
def iterCarrier {A B : SynCat S}
    (f : Carrier S (BoundCtx.nil.snoc A.ty) (cop B A).ty) :
    Carrier S (BoundCtx.nil.snoc A.ty) B.ty :=
  ⟨.iter (.bv 0) (Tm.underBinder f.1),
    f.2.elim fun hf =>
      ⟨HasType.iter (A := A.ty) (B := B.ty) HasType.newest hf.underBinder⟩⟩

/-- **Iteration is well defined on morphisms of the syntactic category.**
`Eqv.iter` is a plain congruence rule and `Pure` has no `iter` constructor, so
no purity side condition intrudes; the only work is the shift under the loop
binder, supplied by `Eqv.rename`.

No Elgot law is proved for this operator — see the module docstring. -/
def iterate {A B : SynCat S} (f : A ⟶ cop B A) : A ⟶ B :=
  Quotient.map iterCarrier
    (fun _ _ hf =>
      Eqv.iter (A := A.ty) (B := B.ty) (Eqv.refl HasType.newest)
        (Eqv.rename (TypedRenaming.underBinder .nil A.ty A.ty) hf))
    f

theorem iterate_mk {A B : SynCat S} {a : Tm Empty S.Instr 1}
    (ha : HasType S.Instr Ctx.nil (BoundCtx.nil.snoc A.ty) a (cop B A).ty) :
    iterate (A := A) (B := B) (mk ha) =
      mk (HasType.iter (A := A.ty) (B := B.ty) HasType.newest
        ha.underBinder) := rfl

end Syn.SynCat

end Isotope.LambdaIter
