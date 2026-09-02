import Isotope.LambdaSeq.Equiv
import Isotope.LambdaCase.Semantics

/-! # Monadic denotational semantics of lambda-seq -/

namespace Isotope.LambdaSeq.Semantics

open Isotope.LambdaSeq.LocallyNameless

universe u v w q r

variable {τ : Type u} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
  [LambdaIter.Semantics.TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [LambdaIter.HasTy Φ τ]
variable {ε : Type r} [LambdaIter.HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m]
variable [LambdaIter.Semantics.InstructionModel Φ τ ε m]

abbrev TyDen (A : τ) := LambdaIter.Semantics.TyDen A
abbrev CtxDen (Γ : Ctx ν τ) := LambdaIter.Semantics.CtxDen Γ
abbrev BoundDen {n : Nat} (β : BoundCtx τ n) := LambdaIter.Semantics.BoundDen β

/-- Every monad interprets sequencing; products, coproducts, and iteration are unnecessary. -/
def denote : {Γ : Ctx ν τ} → {n : Nat} → {β : BoundCtx τ n} →
    {t : Tm ν Φ n} → {A : τ} → HasType Φ Γ β t A →
      CtxDen Γ → BoundDen β → m (TyDen A)
  | _, _, _, _, _, .fv h, γ, _ => pure (LambdaIter.Semantics.CtxDen.lookup γ _ h)
  | _, _, _, _, _, .bv, _, ρ => pure (LambdaIter.Semantics.BoundDen.get ρ _)
  | _, _, _, _, _, .op ha, γ, ρ =>
      denote ha γ ρ >>= LambdaIter.Semantics.InstructionModel.denote
        (Φ := Φ) (τ := τ) (ε := ε) (m := m) _
  | _, _, _, _, _, .let₁ ha hb, γ, ρ =>
      denote ha γ ρ >>= fun a => denote hb γ (ρ, a)
  | _, _, _, _, _, .sub ha d, γ, ρ =>
      denote ha γ ρ >>= fun a => pure (LambdaIter.Semantics.coeSub d a)

def denoteClosed {t : Tm Empty Φ 0} {A : τ}
    (h : HasType Φ (.nil : Ctx Empty τ) .nil t A) : m (TyDen A) :=
  denote (ε := ε) h PUnit.unit PUnit.unit

/-- The direct LambdaSeq semantics agrees with the LambdaCase semantics after inclusion. -/
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
  | sub ha d ih =>
      unfold LocallyNameless.HasType.embedCase LambdaCase.Semantics.denote denote
      rw [ih ρ]

end Isotope.LambdaSeq.Semantics
