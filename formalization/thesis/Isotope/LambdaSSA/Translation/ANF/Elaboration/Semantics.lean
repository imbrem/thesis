import Isotope.LambdaSSA.Translation.ANF.Elaboration
import Isotope.LambdaIter.Semantics.Categorical
import Isotope.LambdaIter.Metatheory.Syntax
import Isotope.LambdaIter.Subtyping.Semantics.Substitution

/-! # Semantic preservation of administrative elaboration -/

namespace Isotope.LambdaSSA.Translation.ANF.Elaboration

set_option relaxedAutoImplicit true

open Isotope.Elgot
open Isotope.LambdaIter
open Isotope.LambdaIter.LocallyNameless
open Isotope.LambdaIter.Subtyping.Semantics

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Iterate m] [LawfulElgotMonad m] [InstructionModel Φ τ ε m]

/-- Transport an exact LambdaIter typing derivation along equality of its raw
term index. -/
def transportHasType {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {t t' : Tm ν Φ n} {A : τ} (e : t = t')
    (h : HasType Φ Γ β t A) : HasType Φ Γ β t' A := e ▸ h

/-- Dependent transport changes only the index, not the proof-relevant
contents of an exact typing derivation. -/
theorem transportHasType_heq {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {t t' : Tm ν Φ n} {A : τ} (e : t = t')
    (h : HasType Φ Γ β t A) : HEq (transportHasType e h) h := by
  subst t'
  rfl

theorem transportHasType_proof_irrel {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {t t' : Tm ν Φ n} {A : τ} (e e' : t = t')
    (h : HasType Φ Γ β t A) :
    transportHasType e h = transportHasType e' h := by
  have : e = e' := Subsingleton.elim _ _
  subst e'
  rfl

theorem heq_of_transportHasType_eq {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {t t' : Tm ν Φ n} {A : τ} (e : t = t')
    (h : HasType Φ Γ β t A) (h' : HasType Φ Γ β t' A)
    (hh : transportHasType e h = h') : HEq h h' := by
  subst t'
  exact heq_of_eq hh

@[simp] theorem transportHasType_op {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a a' : Tm ν Φ n} (e : a = a')
    (h : HasType Φ Γ β a (instrSrc f)) :
    transportHasType (congrArg (Tm.op f) e) (.op h) =
      .op (transportHasType e h) := by cases e; rfl

@[simp] theorem transportHasType_pair {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a a' b b' : Tm ν Φ n} (ea : a = a') (eb : b = b')
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B) :
    transportHasType (by cases ea; cases eb; rfl) (.pair ha hb) =
      .pair (transportHasType ea ha) (transportHasType eb hb) := by
  cases ea; cases eb; rfl

@[simp] theorem transportHasType_inl {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a a' : Tm ν Φ n} (e : a = a') (h : HasType Φ Γ β a A) :
    transportHasType (congrArg Tm.inl e) (.inl (B := B) h) =
      .inl (B := B) (transportHasType e h) := by cases e; rfl

@[simp] theorem transportHasType_inr {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {b b' : Tm ν Φ n} (e : b = b') (h : HasType Φ Γ β b B) :
    transportHasType (congrArg Tm.inr e) (.inr (A := A) h) =
      .inr (A := A) (transportHasType e h) := by cases e; rfl

@[simp] theorem transportHasType_abort {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a a' : Tm ν Φ n} (e : a = a')
    (h : HasType Φ Γ β a LambdaIter.empty) :
    transportHasType (congrArg Tm.abort e) (.abort (C := A) h) =
      .abort (C := A) (transportHasType e h) := by cases e; rfl

theorem transportHasType_bv_typed {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {β' : BoundCtx τ k} (r : TypedRenaming β β') (i : Fin n) :
    transportHasType rfl
        ((r.typed i) ▸ (HasType.bv (Φ := Φ) (Γ := Γ) (β := β')
          (ι := r.toFun i))) =
      ((r.typed i) ▸ (HasType.bv (Φ := Φ) (Γ := Γ) (β := β')
        (ι := r.toFun i))) := rfl

/-- Forgetting atom typing commutes with transport in the result-type index. -/
theorem atom_toLambdaIter_transport_type {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a : Atom ν Φ n} {A B : τ} (e : A = B)
    (h : Atom.HasType Γ β a A) :
    ((e ▸ h).toLambdaIter) = (e ▸ h.toLambdaIter) := by
  cases e
  rfl

@[simp] theorem atomRename_toTm (ρ : Fin n → Fin k) (a : Atom ν Φ n) :
    (atomRename ρ a).toTm = a.toTm.rename ρ := by
  induction a <;> simp [atomRename, Atom.toTm, Tm.rename, *]

/-- Forgetting commutes with every mutually recursive ANF renaming. -/
theorem programRename_toTm (p : Program ν Φ n) :
    ∀ {k} (ρ : Fin n → Fin k), (programRename ρ p).toTm = p.toTm.rename ρ := by
  induction p using Program.rec (motive_2 := fun n i =>
    ∀ {k} (ρ : Fin n → Fin k), (instrRename ρ i).toTm = i.toTm.rename ρ) with
  | ret a => intro k ρ; simp [programRename, Program.toTm, atomRename_toTm]
  | let₁ i body ii ib =>
      intro k ρ
      simp only [programRename, Program.toTm, ii, ib, Syntax.rename_let₁]
      congr 1

  | let₂ a body ib =>
      intro k ρ
      simp only [programRename, Program.toTm, atomRename_toTm, ib, Syntax.rename_let₂]
      congr 1
  | atom a => simp [instrRename, Instr.toTm, atomRename_toTm]
  | case e l r il ir =>
      simp only [instrRename, Instr.toTm, atomRename_toTm, il, ir, Syntax.rename_case]
      congr 1
  | iter a body ib =>
      simp only [instrRename, Instr.toTm, atomRename_toTm, ib, Syntax.rename_iter]
      congr 1

theorem atomRename_exact_op {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {β' : BoundCtx τ k} {a : Atom ν Φ n}
    (ha : Atom.HasType Γ β a (instrSrc f)) (r : TypedRenaming β β')
    (ih : transportHasType (atomRename_toTm r.toFun a)
      (atomRename_hasType r ha).toLambdaIter = ha.toLambdaIter.rename r) :
    transportHasType (atomRename_toTm r.toFun (.op f a))
        (atomRename_hasType r (.op ha)).toLambdaIter =
      (Atom.HasType.toLambdaIter (.op ha)).rename r := by
  let ea := atomRename_toTm r.toFun a
  let eop := congrArg (Tm.op f) ea
  calc
    _ = transportHasType eop
        (.op (atomRename_hasType r ha).toLambdaIter) :=
      transportHasType_proof_irrel _ _ _
    _ = .op (transportHasType ea (atomRename_hasType r ha).toLambdaIter) :=
      transportHasType_op ea _
    _ = _ := congrArg Isotope.LambdaIter.LocallyNameless.HasType.op ih

theorem atomRename_exact_heq_fv {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {β' : BoundCtx τ k} {x : ν} {A : τ} (h : Γ.lookup x = some A)
    (r : TypedRenaming β β') :
    let ha : Atom.HasType (Φ := Φ) Γ β (.fv x) A := .fv h
    let hl : HasType Φ Γ β (.fv x) A := ha.toLambdaIter
    HEq (atomRename_hasType r ha).toLambdaIter
      (Isotope.LambdaIter.LocallyNameless.HasType.rename r hl) := by
  dsimp
  apply heq_of_transportHasType_eq (atomRename_toTm r.toFun (.fv x))
  exact transportHasType_proof_irrel _ rfl _

theorem atomRename_exact_heq_unit {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {β' : BoundCtx τ k} (r : TypedRenaming β β') :
    let ha : Atom.HasType (Φ := Φ) Γ β .unit LambdaIter.unit := .unit
    let hl : HasType Φ Γ β .unit LambdaIter.unit := ha.toLambdaIter
    HEq (atomRename_hasType r ha).toLambdaIter
      (Isotope.LambdaIter.LocallyNameless.HasType.rename r hl) := by
  dsimp
  apply heq_of_transportHasType_eq (atomRename_toTm r.toFun .unit)
  exact transportHasType_proof_irrel _ rfl _

theorem atomRename_exact_heq_bv {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {β' : BoundCtx τ k} (i : Fin n) (r : TypedRenaming β β') :
    let ha : Atom.HasType (Φ := Φ) Γ β (.bv i) (β.get i) := .bv
    let hl : HasType Φ Γ β (.bv i) (β.get i) := ha.toLambdaIter
    HEq (atomRename_hasType r ha).toLambdaIter
      (Isotope.LambdaIter.LocallyNameless.HasType.rename r hl) := by
  dsimp [atomRename_hasType, Isotope.LambdaIter.LocallyNameless.HasType.rename]
  exact heq_of_eq (atom_toLambdaIter_transport_type (r.typed i)
    (Atom.HasType.bv (Φ := Φ) (Γ := Γ) (β := β') (i := r.toFun i)))

/-- The normalized exact-renaming equation is closed under pairing. -/
theorem atomRename_exact_pair {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {β' : BoundCtx τ k} {a b : Atom ν Φ n}
    (ha : Atom.HasType Γ β a A) (hb : Atom.HasType Γ β b B)
    (r : TypedRenaming β β')
    (iha : transportHasType (atomRename_toTm r.toFun a)
      (atomRename_hasType r ha).toLambdaIter = ha.toLambdaIter.rename r)
    (ihb : transportHasType (atomRename_toTm r.toFun b)
      (atomRename_hasType r hb).toLambdaIter = hb.toLambdaIter.rename r) :
    transportHasType (atomRename_toTm r.toFun (.pair a b))
        (atomRename_hasType r (.pair ha hb)).toLambdaIter =
      (Atom.HasType.toLambdaIter (.pair ha hb)).rename r := by
  let ea := atomRename_toTm r.toFun a
  let eb := atomRename_toTm r.toFun b
  calc
    _ = transportHasType (congrArg₂ Tm.pair ea eb)
        (.pair (atomRename_hasType r ha).toLambdaIter
          (atomRename_hasType r hb).toLambdaIter) := transportHasType_proof_irrel _ _ _
    _ = .pair (transportHasType ea (atomRename_hasType r ha).toLambdaIter)
          (transportHasType eb (atomRename_hasType r hb).toLambdaIter) :=
      transportHasType_pair ea eb _ _
    _ = _ := congrArg₂ Isotope.LambdaIter.LocallyNameless.HasType.pair iha ihb

theorem atomRename_exact_inl {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {β' : BoundCtx τ k} {a : Atom ν Φ n}
    (h : Atom.HasType Γ β a A) (r : TypedRenaming β β')
    (ih : transportHasType (atomRename_toTm r.toFun a)
      (atomRename_hasType r h).toLambdaIter = h.toLambdaIter.rename r) :
    transportHasType (atomRename_toTm r.toFun (.inl a))
        (atomRename_hasType r (.inl (B := B) h)).toLambdaIter =
      (Atom.HasType.toLambdaIter (.inl (B := B) h)).rename r := by
  let e := atomRename_toTm r.toFun a
  calc
    _ = transportHasType (congrArg Tm.inl e)
        (.inl (B := B) (atomRename_hasType r h).toLambdaIter) :=
      transportHasType_proof_irrel _ _ _
    _ = .inl (B := B) (transportHasType e (atomRename_hasType r h).toLambdaIter) :=
      transportHasType_inl e _
    _ = _ := congrArg (Isotope.LambdaIter.LocallyNameless.HasType.inl (B := B)) ih

theorem atomRename_exact_inr {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {β' : BoundCtx τ k} {b : Atom ν Φ n}
    (h : Atom.HasType Γ β b B) (r : TypedRenaming β β')
    (ih : transportHasType (atomRename_toTm r.toFun b)
      (atomRename_hasType r h).toLambdaIter = h.toLambdaIter.rename r) :
    transportHasType (atomRename_toTm r.toFun (.inr b))
        (atomRename_hasType r (.inr (A := A) h)).toLambdaIter =
      (Atom.HasType.toLambdaIter (.inr (A := A) h)).rename r := by
  let e := atomRename_toTm r.toFun b
  calc
    _ = transportHasType (congrArg Tm.inr e)
        (.inr (A := A) (atomRename_hasType r h).toLambdaIter) :=
      transportHasType_proof_irrel _ _ _
    _ = .inr (A := A) (transportHasType e (atomRename_hasType r h).toLambdaIter) :=
      transportHasType_inr e _
    _ = _ := congrArg (Isotope.LambdaIter.LocallyNameless.HasType.inr (A := A)) ih

theorem atomRename_exact_abort {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {β' : BoundCtx τ k} {a : Atom ν Φ n}
    (h : Atom.HasType Γ β a LambdaIter.empty) (r : TypedRenaming β β')
    (ih : transportHasType (atomRename_toTm r.toFun a)
      (atomRename_hasType r h).toLambdaIter = h.toLambdaIter.rename r) :
    transportHasType (atomRename_toTm r.toFun (.abort a))
        (atomRename_hasType r (.abort (A := A) h)).toLambdaIter =
      (Atom.HasType.toLambdaIter (.abort (A := A) h)).rename r := by
  let e := atomRename_toTm r.toFun a
  calc
    _ = transportHasType (congrArg Tm.abort e)
        (.abort (C := A) (atomRename_hasType r h).toLambdaIter) :=
      transportHasType_proof_irrel _ _ _
    _ = .abort (C := A) (transportHasType e (atomRename_hasType r h).toLambdaIter) :=
      transportHasType_abort e _
    _ = _ := congrArg (Isotope.LambdaIter.LocallyNameless.HasType.abort (C := A)) ih

@[simp] theorem denote_elaborate_fv {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {x : ν} {A : τ} (hx : Γ.lookup x = some A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (HasType.fv (Φ := Φ) hx).toGeneric γ ρ =
      denote (m := m) (ε := ε)
        (elaborate_forget_hasType (HasType.fv (Φ := Φ) hx)).toGeneric γ ρ := rfl

@[simp] theorem denote_elaborate_bv {Γ : Ctx ν τ} {β : BoundCtx τ n}
    (i : Fin n) (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε)
        (show HasType Φ Γ β (.bv i) (β.get i) from .bv).toGeneric γ ρ =
      denote (m := m) (ε := ε)
        (elaborate_forget_hasType
          (show HasType Φ Γ β (.bv i) (β.get i) from .bv)).toGeneric γ ρ := rfl

@[simp] theorem denote_elaborate_unit {Γ : Ctx ν τ} {β : BoundCtx τ n}
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (HasType.unit (Φ := Φ) (Γ := Γ) (β := β)).toGeneric γ ρ =
      denote (m := m) (ε := ε)
        (elaborate_forget_hasType
          (HasType.unit (Φ := Φ) (Γ := Γ) (β := β))).toGeneric γ ρ := rfl

end Isotope.LambdaSSA.Translation.ANF.Elaboration
