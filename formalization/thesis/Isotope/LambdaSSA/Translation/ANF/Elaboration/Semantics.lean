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
