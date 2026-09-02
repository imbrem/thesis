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
