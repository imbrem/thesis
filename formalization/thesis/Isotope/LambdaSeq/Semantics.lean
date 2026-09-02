import Isotope.LambdaSeq.Equiv
import Isotope.LambdaIter.Subtyping.Semantics.Model
import Isotope.LambdaIter.Subtyping.Semantics.Instruction
import Isotope.LambdaCase.Semantics
import Isotope.LambdaCase.Subtyping.Semantics

/-! # Monadic denotational semantics of lambda-seq -/

namespace Isotope.LambdaSeq.Semantics

open Isotope.LambdaSeq.LocallyNameless

universe u v w q r

variable {τ : Type u} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
  [LambdaIter.Subtyping.Semantics.TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [LambdaIter.HasTy Φ τ]
variable {ε : Type r} [LambdaIter.HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m]
variable [LambdaIter.Subtyping.Semantics.InstructionModel Φ τ ε m]

abbrev TyDen (A : τ) := LambdaIter.Subtyping.Semantics.TyDen A
abbrev CtxDen (Γ : Ctx ν τ) := LambdaIter.Subtyping.Semantics.CtxDen Γ
abbrev BoundDen {n : Nat} (β : BoundCtx τ n) := LambdaIter.Subtyping.Semantics.BoundDen β

/-- Every monad interprets sequencing; products, coproducts, and iteration are unnecessary. -/
def denote : {Γ : Ctx ν τ} → {n : Nat} → {β : BoundCtx τ n} →
    {t : Tm ν Φ n} → {A : τ} → HasType Φ Γ β t A →
      CtxDen Γ → BoundDen β → m (TyDen A)
  | _, _, _, _, _, .fv h, γ, _ => pure (LambdaIter.Subtyping.Semantics.CtxDen.lookup γ _ h)
  | _, _, _, _, _, .bv, _, ρ => pure (LambdaIter.Subtyping.Semantics.BoundDen.get ρ _)
  | _, _, _, _, _, .op ha, γ, ρ =>
      denote ha γ ρ >>= LambdaIter.Subtyping.Semantics.InstructionModel.denote
        (Φ := Φ) (τ := τ) (ε := ε) (m := m) _
  | _, _, _, _, _, .let₁ ha hb, γ, ρ =>
      denote ha γ ρ >>= fun a => denote hb γ (ρ, a)

def denoteClosed {t : Tm Empty Φ 0} {A : τ}
    (h : HasType Φ (.nil : Ctx Empty τ) .nil t A) : m (TyDen A) :=
  denote (ε := ε) h PUnit.unit PUnit.unit

/-- Direct exact semantics agrees with exact lambda-case semantics after inclusion. -/
theorem denote_embedCase [LawfulMonad m]
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β t A) (γ : CtxDen Γ) (ρ : BoundDen β) :
    LambdaCase.Semantics.denote (ε := ε) (m := m) h.embedCase γ ρ =
      denote (ε := ε) (m := m) h γ ρ := by
  induction h with
  | fv | bv => rfl
  | op ha ih =>
      unfold LocallyNameless.HasType.embedCase LambdaCase.Semantics.denote denote
      simp only [ih ρ]
  | let₁ ha hb iha ihb =>
      unfold LocallyNameless.HasType.embedCase LambdaCase.Semantics.denote denote
      rw [iha ρ]
      congr 1
      funext a
      rw [ihb (ρ, a)]

/-- Direct exact semantics agrees with lambda-iter semantics after inclusion. -/
theorem denote_embedIter [LawfulMonad m] [Isotope.Elgot.Iterate m]
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β t A) (γ : CtxDen Γ) (ρ : BoundDen β) :
    LambdaIter.Semantics.denote (ε := ε) (m := m) h.embedIter γ ρ =
      denote (ε := ε) (m := m) h γ ρ := by
  rw [LambdaCase.Semantics.denote_embed h.embedCase γ ρ]
  exact denote_embedCase h γ ρ

end Isotope.LambdaSeq.Semantics

namespace Isotope.LambdaSeq.Subtyping.Semantics

open Isotope.LambdaSeq.Subtyping.LocallyNameless

universe u v w q r

variable {τ : Type u} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
  [LambdaIter.Subtyping.Semantics.TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [LambdaIter.HasTy Φ τ]
variable {ε : Type r} [LambdaIter.HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m]
variable [LambdaIter.Subtyping.Semantics.InstructionModel Φ τ ε m]

abbrev TyDen (A : τ) := LambdaIter.Subtyping.Semantics.TyDen A
abbrev CtxDen (Γ : Ctx ν τ) := LambdaIter.Subtyping.Semantics.CtxDen Γ
abbrev BoundDen {n : Nat} (β : LambdaSeq.LocallyNameless.BoundCtx τ n) :=
  LambdaIter.Subtyping.Semantics.BoundDen β

/-- Coercive lambda-seq semantics, inherited through the lambda-case comparison. -/
def denote {Γ : Ctx ν τ} {n : Nat} {β : LambdaSeq.LocallyNameless.BoundCtx τ n}
    {t : LambdaSeq.LocallyNameless.Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A) :
    CtxDen Γ → BoundDen β → m (TyDen A) :=
  LambdaCase.Subtyping.Semantics.denote (ε := ε) (m := m) h.embedCase

def denoteClosed {t : LambdaSeq.LocallyNameless.Tm Empty Φ 0} {A : τ}
    (h : HasType Φ (.nil : Ctx Empty τ) .nil t A) : m (TyDen A) :=
  denote (ε := ε) h PUnit.unit PUnit.unit

theorem denote_embedCase
    {Γ : Ctx ν τ} {n : Nat} {β : LambdaSeq.LocallyNameless.BoundCtx τ n}
    {t : LambdaSeq.LocallyNameless.Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    LambdaCase.Subtyping.Semantics.denote (ε := ε) (m := m) h.embedCase γ ρ =
      denote (ε := ε) (m := m) h γ ρ := rfl

/-- Coercive lambda-seq semantics agrees with lambda-iter after inclusion. -/
theorem denote_embedIter [LawfulMonad m] [Isotope.Elgot.Iterate m]
    {Γ : Ctx ν τ} {n : Nat} {β : LambdaSeq.LocallyNameless.BoundCtx τ n}
    {t : LambdaSeq.LocallyNameless.Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    LambdaIter.Subtyping.Semantics.denote (ε := ε) (m := m) h.embedIter γ ρ =
      denote (ε := ε) (m := m) h γ ρ := by
  rw [LambdaCase.Subtyping.Semantics.denote_embed h.embedCase γ ρ]
  rfl

end Isotope.LambdaSeq.Subtyping.Semantics
