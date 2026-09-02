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

@[simp] theorem transportHasType_let₁ {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a a' : Tm ν Φ n} {b b' : Tm ν Φ (n + 1)}
    (ea : a = a') (eb : b = b')
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ (.snoc β A) b B) :
    transportHasType (congrArg₂ Tm.let₁ ea eb) (.let₁ ha hb) =
      .let₁ (transportHasType ea ha) (transportHasType eb hb) := by
  cases ea; cases eb; rfl

@[simp] theorem transportHasType_let₂ {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a a' : Tm ν Φ n} {b b' : Tm ν Φ (n + 2)}
    (ea : a = a') (eb : b = b')
    (ha : HasType Φ Γ β a (LambdaIter.tensor A B))
    (hb : HasType Φ Γ (.snoc (.snoc β A) B) b C) :
    transportHasType (congrArg₂ Tm.let₂ ea eb) (.let₂ ha hb) =
      .let₂ (transportHasType ea ha) (transportHasType eb hb) := by
  cases ea; cases eb; rfl

private theorem congrArg3 {α β γ δ : Sort*} (f : α → β → γ → δ)
    {a a' : α} {b b' : β} {c c' : γ}
    (ea : a = a') (eb : b = b') (ec : c = c') :
    f a b c = f a' b' c' := by cases ea; cases eb; cases ec; rfl

@[simp] theorem transportHasType_case {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {e e' : Tm ν Φ n} {l l' r r' : Tm ν Φ (n + 1)}
    (ee : e = e') (el : l = l') (er : r = r')
    (he : HasType Φ Γ β e (LambdaIter.coprod A B))
    (hl : HasType Φ Γ (.snoc β A) l C)
    (hr : HasType Φ Γ (.snoc β B) r C) :
    transportHasType (by cases ee; cases el; cases er; rfl) (.case he hl hr) =
      .case (transportHasType ee he) (transportHasType el hl)
        (transportHasType er hr) := by
  cases ee; cases el; cases er; rfl

@[simp] theorem transportHasType_iter {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a a' : Tm ν Φ n} {b b' : Tm ν Φ (n + 1)}
    (ea : a = a') (eb : b = b')
    (ha : HasType Φ Γ β a A)
    (hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A)) :
    transportHasType (congrArg₂ Tm.iter ea eb) (.iter ha hb) =
      .iter (transportHasType ea ha) (transportHasType eb hb) := by
  cases ea; cases eb; rfl

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

@[simp] theorem instrRename_toTm (i : Instr ν Φ n) :
    ∀ {k} (ρ : Fin n → Fin k), (instrRename ρ i).toTm = i.toTm.rename ρ := by
  intro k ρ
  cases i with
  | atom a => exact atomRename_toTm ρ a
  | case e l r =>
      simp only [instrRename, Instr.toTm, atomRename_toTm, programRename_toTm,
        Syntax.rename_case]
      rfl
  | iter a body =>
      simp only [instrRename, Instr.toTm, atomRename_toTm, programRename_toTm,
        Syntax.rename_iter]
      rfl

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

/-- Forgetting ANF atom typing commutes with every typed bound renaming. -/
theorem atomRename_exact {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {β' : BoundCtx τ k} {a : Atom ν Φ n} {A : τ}
    (h : Atom.HasType Γ β a A) (r : TypedRenaming β β') :
    transportHasType (atomRename_toTm r.toFun a)
        (atomRename_hasType r h).toLambdaIter = h.toLambdaIter.rename r := by
  induction h with
  | fv h => exact transportHasType_proof_irrel _ rfl _
  | bv =>
      simp only [atomRename_hasType, Atom.HasType.toLambdaIter,
        Isotope.LambdaIter.LocallyNameless.HasType.rename]
      change ((r.typed _ ▸ (Atom.HasType.bv (Φ := Φ) (Γ := Γ)
        (β := β') (i := r.toFun _))).toLambdaIter) =
        (r.typed _ ▸ (HasType.bv (Φ := Φ) (Γ := Γ)
          (β := β') (ι := r.toFun _)))
      exact atom_toLambdaIter_transport_type _ _
  | op h ih => exact atomRename_exact_op h r ih
  | unit => exact transportHasType_proof_irrel _ rfl _
  | pair ha hb iha ihb => exact atomRename_exact_pair ha hb r iha ihb
  | inl h ih => exact atomRename_exact_inl h r ih
  | inr h ih => exact atomRename_exact_inr h r ih
  | abort h ih => exact atomRename_exact_abort h r ih

/-- The Program renaming bridge for an administrative return. -/
theorem programRename_exact_ret {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {β' : BoundCtx τ k} {a : Atom ν Φ n} {A : τ}
    (h : Atom.HasType Γ β a A) (r : TypedRenaming β β') :
    transportHasType (programRename_toTm (.ret a) r.toFun)
        (programRename_hasType r (.ret h)).toLambdaIter =
      (Program.HasType.toLambdaIter (.ret h)).rename r := by
  calc
    _ = transportHasType (atomRename_toTm r.toFun a)
        (atomRename_hasType r h).toLambdaIter :=
      transportHasType_proof_irrel _ _ _
    _ = _ := atomRename_exact h r

@[simp] theorem instrRename_toTm_atom (ρ : Fin n → Fin k) (a : Atom ν Φ n) :
    (instrRename ρ (.atom a)).toTm = (Instr.atom a).toTm.rename ρ :=
  atomRename_toTm ρ a

/-- The Instr renaming bridge for atomic instructions. -/
theorem instrRename_exact_atom {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {β' : BoundCtx τ k} {a : Atom ν Φ n} {A : τ}
    (h : Atom.HasType Γ β a A) (r : TypedRenaming β β') :
    transportHasType (instrRename_toTm_atom r.toFun a)
        (instrRename_hasType r (.atom h)).toLambdaIter =
      (Instr.HasType.toLambdaIter (.atom h)).rename r := by
  calc
    _ = transportHasType (atomRename_toTm r.toFun a)
        (atomRename_hasType r h).toLambdaIter :=
      transportHasType_proof_irrel _ _ _
    _ = _ := atomRename_exact h r

private def programOfHasType {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {p : Program ν Φ n} {A : τ} (_ : Program.HasType Γ β p A) := p

private def instrOfHasType {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {i : Instr ν Φ n} {A : τ} (_ : Instr.HasType Γ β i A) := i

private def atomOfHasType {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a : Atom ν Φ n} {A : τ} (_ : Atom.HasType Γ β a A) := a

private def upForProgram {n k : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ k}
    {Γ : Ctx ν τ} (r : TypedRenaming β β')
    {p : Program ν Φ (n + 1)} {A B : τ}
    (_ : Program.HasType (Φ := Φ) Γ (.snoc β A) p B) :
    TypedRenaming (.snoc β A) (.snoc β' A) := r.up A

private def upTwoForProgram {n k : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ k}
    {Γ : Ctx ν τ} (r : TypedRenaming β β')
    {p : Program ν Φ (n + 2)} {A B C : τ}
    (_ : Program.HasType (Φ := Φ) Γ (.snoc (.snoc β A) B) p C) :
    TypedRenaming (.snoc (.snoc β A) B) (.snoc (.snoc β' A) B) :=
  (r.up A).up B

mutual
  /-- Forgetting ANF Program typing commutes with typed renaming. -/
  theorem programRename_exact {Γ : Ctx ν τ} {β : BoundCtx τ n}
      {β' : BoundCtx τ k} {p : Program ν Φ n} {A : τ}
      (h : Program.HasType Γ β p A) (r : TypedRenaming β β') :
      transportHasType (programRename_toTm p r.toFun)
          (programRename_hasType r h).toLambdaIter = h.toLambdaIter.rename r := by
    cases h with
    | ret h => exact programRename_exact_ret h r
    | let₁ hi hb =>
        let ei := instrRename_toTm (instrOfHasType hi) r.toFun
        let ru := upForProgram r hb
        let eb := programRename_toTm (programOfHasType hb) ru.toFun
        calc
          _ = transportHasType (congrArg₂ Tm.let₁ ei eb)
              (.let₁ (instrRename_hasType r hi).toLambdaIter
                (programRename_hasType ru hb).toLambdaIter) :=
            transportHasType_proof_irrel _ _ _
          _ = .let₁ (transportHasType ei (instrRename_hasType r hi).toLambdaIter)
                (transportHasType eb
                  (programRename_hasType ru hb).toLambdaIter) :=
            transportHasType_let₁ ei eb _ _
          _ = _ := congrArg₂ Isotope.LambdaIter.LocallyNameless.HasType.let₁
            (instrRename_exact hi r) (programRename_exact hb ru)
    | let₂ ha hb =>
        let ea := atomRename_toTm r.toFun (atomOfHasType ha)
        let ru := upTwoForProgram r hb
        let eb := programRename_toTm (programOfHasType hb) ru.toFun
        calc
          _ = transportHasType (congrArg₂ Tm.let₂ ea eb)
              (.let₂ (atomRename_hasType r ha).toLambdaIter
                (programRename_hasType ru hb).toLambdaIter) :=
            transportHasType_proof_irrel _ _ _
          _ = .let₂ (transportHasType ea (atomRename_hasType r ha).toLambdaIter)
                (transportHasType eb
                  (programRename_hasType ru hb).toLambdaIter) :=
            transportHasType_let₂ ea eb _ _
          _ = _ := congrArg₂ Isotope.LambdaIter.LocallyNameless.HasType.let₂
            (atomRename_exact ha r) (programRename_exact hb ru)

  /-- Forgetting ANF Instr typing commutes with typed renaming. -/
theorem instrRename_exact {Γ : Ctx ν τ} {β : BoundCtx τ n}
      {β' : BoundCtx τ k} {i : Instr ν Φ n} {A : τ}
      (h : Instr.HasType Γ β i A) (r : TypedRenaming β β') :
      transportHasType (instrRename_toTm i r.toFun)
          (instrRename_hasType r h).toLambdaIter = h.toLambdaIter.rename r := by
    cases h with
    | atom h => exact instrRename_exact_atom h r
    | case he hl hr =>
        let ee := atomRename_toTm r.toFun (atomOfHasType he)
        let rl := upForProgram r hl
        let rr := upForProgram r hr
        let el := programRename_toTm (programOfHasType hl) rl.toFun
        let er := programRename_toTm (programOfHasType hr) rr.toFun
        calc
          _ = transportHasType (congrArg3 Tm.case ee el er)
              (.case (atomRename_hasType r he).toLambdaIter
                (programRename_hasType rl hl).toLambdaIter
                (programRename_hasType rr hr).toLambdaIter) :=
            transportHasType_proof_irrel _ _ _
          _ = .case (transportHasType ee (atomRename_hasType r he).toLambdaIter)
                (transportHasType el (programRename_hasType rl hl).toLambdaIter)
                (transportHasType er (programRename_hasType rr hr).toLambdaIter) :=
            transportHasType_case ee el er _ _ _
          _ = _ := congrArg3 Isotope.LambdaIter.LocallyNameless.HasType.case
            (atomRename_exact he r) (programRename_exact hl rl)
            (programRename_exact hr rr)
    | iter ha hb =>
        let ea := atomRename_toTm r.toFun (atomOfHasType ha)
        let ru := upForProgram r hb
        let eb := programRename_toTm (programOfHasType hb) ru.toFun
        calc
          _ = transportHasType (congrArg₂ Tm.iter ea eb)
              (.iter (atomRename_hasType r ha).toLambdaIter
                (programRename_hasType ru hb).toLambdaIter) :=
            transportHasType_proof_irrel _ _ _
          _ = .iter (transportHasType ea (atomRename_hasType r ha).toLambdaIter)
                (transportHasType eb (programRename_hasType ru hb).toLambdaIter) :=
            transportHasType_iter ea eb _ _
          _ = _ := congrArg₂ Isotope.LambdaIter.LocallyNameless.HasType.iter
            (atomRename_exact ha r) (programRename_exact hb ru)
end

theorem denote_transportHasType {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {t t' : Tm ν Φ n} {A : τ} (e : t = t')
    (h : HasType Φ Γ β t A) (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (transportHasType e h).toGeneric γ ρ =
      denote (m := m) (ε := ε) h.toGeneric γ ρ := by
  cases e
  rfl

/-- Embedding exact typing into generic typing commutes with transport of the
result type. -/
theorem toGeneric_transport_type {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A B : τ} (e : A = B) (h : HasType Φ Γ β t A) :
    HEq ((e ▸ h).toGeneric) (e ▸ h.toGeneric) := by
  cases e
  rfl

/-- Embedding commutes with the dependent transport introduced when an exact
bound-variable derivation is renamed. -/
theorem toGeneric_rename_bv {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {β' : BoundCtx τ k} (i : Fin n) (r : TypedRenaming β β') :
    HEq ((r.typed i ▸ (HasType.bv (Φ := Φ) (Γ := Γ) (β := β')
      (ι := r.toFun i))).toGeneric)
      (r.typed i ▸ (Isotope.LambdaIter.Subtyping.LocallyNameless.HasType.bv
        (Φ := Φ) (Γ := Γ) (β := β') (ι := r.toFun i))) := by
  exact toGeneric_transport_type (r.typed i)
    (HasType.bv (Φ := Φ) (Γ := Γ) (β := β') (ι := r.toFun i))

/-- Direct denotational naturality for exact renaming, after embedding into
the proof-relevant generic semantics. -/
theorem denote_exact_rename {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {β' : BoundCtx τ k} {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β t A) (r : TypedRenaming β β')
    (γ : CtxDen Γ) (ρ : BoundDen β') :
    denote (m := m) (ε := ε) (h.rename r).toGeneric γ ρ =
      denote (m := m) (ε := ε) h.toGeneric γ
        (BoundDen.pull ({ toFun := r.toFun, typed := r.typed } :
          Isotope.LambdaIter.Subtyping.LocallyNameless.TypedRenaming β β') ρ) := by
  induction h generalizing k β' with
  | fv h =>
      simp only [HasType.rename, HasType.toGeneric]
      unfold denote
      rfl
  | @bv n β i =>
      let rg : Isotope.LambdaIter.Subtyping.LocallyNameless.TypedRenaming β β' :=
        { toFun := r.toFun, typed := r.typed }
      let hg := Isotope.LambdaIter.Subtyping.LocallyNameless.HasType.bv
        (Φ := Φ) (Γ := Γ) (β := β) (ι := i)
      calc
        _ = denote (m := m) (ε := ε) (hg.rename rg) γ ρ := by
          apply congrArg (fun d => denote (m := m) (ε := ε) d γ ρ)
          exact eq_of_heq (toGeneric_rename_bv i r)
        _ = _ := Isotope.LambdaIter.Subtyping.Semantics.denote_rename
          (m := m) (ε := ε) hg rg γ ρ
  | op h ih =>
      simp only [HasType.rename, HasType.toGeneric]
      unfold denote
      change (denote (m := m) (ε := ε) (h.rename r).toGeneric γ ρ >>= _) = _
      rw [ih]
  | let₁ ha hb iha ihb =>
      simp only [HasType.rename, HasType.toGeneric]
      unfold denote
      change (denote (m := m) (ε := ε) (ha.rename r).toGeneric γ ρ >>= fun a =>
        denote (m := m) (ε := ε) (hb.rename (r.up _)).toGeneric γ (ρ, a)) = _
      rw [iha]
      apply bind_congr
      intro a
      rw [ihb]
      rfl
  | unit =>
      simp only [HasType.rename, HasType.toGeneric]
      unfold denote
      change (pure (TypeModel.unitEquiv.symm ()) : m _) = pure _
      rfl
  | pair ha hb iha ihb =>
      simp only [HasType.rename, HasType.toGeneric]
      unfold denote
      change (denote (m := m) (ε := ε) (ha.rename r).toGeneric γ ρ >>= fun a =>
        denote (m := m) (ε := ε) (hb.rename r).toGeneric γ ρ >>= fun b => pure _) = _
      rw [iha, ihb]
  | let₂ ha hc iha ihc =>
      simp only [HasType.rename, HasType.toGeneric]
      unfold denote
      change (denote (m := m) (ε := ε) (ha.rename r).toGeneric γ ρ >>= fun ab =>
        denote (m := m) (ε := ε) (hc.rename ((r.up _).up _)).toGeneric γ
          ((ρ, (TypeModel.tensorEquiv _ _ ab).1),
            (TypeModel.tensorEquiv _ _ ab).2)) = _
      rw [iha]
      apply bind_congr
      intro ab
      rw [ihc]
      rfl
  | inl h ih | inr h ih | abort h ih =>
      simp only [HasType.rename, HasType.toGeneric]
      unfold denote
      change (denote (m := m) (ε := ε) (h.rename r).toGeneric γ ρ >>= _) = _
      rw [ih]
  | case he hl hr ihe ihl ihr =>
      simp only [HasType.rename, HasType.toGeneric]
      unfold denote
      change (denote (m := m) (ε := ε) (he.rename r).toGeneric γ ρ >>= fun e =>
        match TypeModel.coprodEquiv _ _ e with
        | .inl a => denote (m := m) (ε := ε) (hl.rename (r.up _)).toGeneric γ (ρ, a)
        | .inr b => denote (m := m) (ε := ε) (hr.rename (r.up _)).toGeneric γ (ρ, b)) = _
      rw [ihe]
      apply bind_congr
      intro e
      cases TypeModel.coprodEquiv _ _ e with
      | inl a => simp only; rw [ihl]; rfl
      | inr b => simp only; rw [ihr]; rfl
  | iter ha hb iha ihb =>
      simp only [HasType.rename, HasType.toGeneric]
      unfold denote
      change (denote (m := m) (ε := ε) (ha.rename r).toGeneric γ ρ >>= Elgot.iter fun a =>
        denote (m := m) (ε := ε) (hb.rename (r.up _)).toGeneric γ (ρ, a) >>= fun s =>
          pure (TypeModel.coprodEquiv _ _ s)) = _
      rw [iha]
      apply bind_congr
      intro a
      congr 1
      funext x
      rw [ihb]
      rfl

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
