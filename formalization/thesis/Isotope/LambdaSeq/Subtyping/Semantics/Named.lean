import Isotope.LambdaSeq.Typing
import Isotope.LambdaCase.Subtyping.Semantics.Named

/-! # Named monadic semantics of proof-relevant lambda-seq -/

namespace Isotope.LambdaSeq.Subtyping.Semantics.Named

open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics
open Isotope.LambdaSeq.Subtyping.Named

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [InstructionModel Φ τ ε m]

/-- Direct interpretation of a named sequential derivation. -/
def denote : {Γ : Ctx ν τ} → {t : LambdaSeq.Named.Tm ν Φ} → {A : τ} →
    HasType Γ t A → CtxDen Γ → m (TyDen A)
  | _, _, _, .var h, γ => pure (CtxDen.lookup γ _ h)
  | _, _, _, .op hf ha, γ => denote ha γ >>= fun a =>
      InstructionModel.denote (Φ := Φ) (τ := τ) (ε := ε) (m := m) _
        (coeSub hf.input a) >>= fun b => pure (coeSub hf.output b)
  | _, _, _, .let₁ ha hb, γ => denote ha γ >>= fun a => denote hb (γ, a)
  | _, _, _, .sub ha d, γ => denote ha γ >>= fun a => pure (coeSub d a)

theorem denote_embedCase
    {Γ : Ctx ν τ} {t : LambdaSeq.Named.Tm ν Φ} {A : τ}
    (h : HasType Γ t A) (γ : CtxDen Γ) :
    LambdaCase.Subtyping.Semantics.Named.denote (ε := ε) (m := m) h.embedCase γ =
      denote (ε := ε) (m := m) h γ := by
  induction h with
  | var => rfl
  | op hf ha ih =>
      simp only [HasType.embedCase]
      unfold LambdaCase.Subtyping.Semantics.Named.denote denote
      rw [ih]
  | let₁ ha hb iha ihb =>
      simp only [HasType.embedCase]
      unfold LambdaCase.Subtyping.Semantics.Named.denote denote
      rw [iha]
      apply bind_congr
      intro a
      exact ihb (γ, a)
  | sub ha d ih =>
      simp only [HasType.embedCase]
      unfold LambdaCase.Subtyping.Semantics.Named.denote denote
      rw [ih]

/-- Named lambda-seq inclusion into lambda-iter preserves proof-relevant
coercive semantics. -/
theorem denote_embedIter [Isotope.Elgot.Iterate m]
    {Γ : Ctx ν τ} {t : LambdaSeq.Named.Tm ν Φ} {A : τ}
    (h : HasType Γ t A) (γ : CtxDen Γ) :
    LambdaIter.Subtyping.Semantics.Named.denote (ε := ε) (m := m) h.embedIter γ =
      denote (ε := ε) (m := m) h γ := by
  change LambdaIter.Subtyping.Semantics.Named.denote (ε := ε) (m := m)
    h.embedCase.embed γ = _
  rw [LambdaCase.Subtyping.Semantics.Named.denote_embed h.embedCase γ]
  exact denote_embedCase h γ

end Isotope.LambdaSeq.Subtyping.Semantics.Named
