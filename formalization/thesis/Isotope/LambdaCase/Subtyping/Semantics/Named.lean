import Isotope.LambdaCase.Subtyping.Typing
import Isotope.LambdaIter.Subtyping.Semantics.Named

/-! # Named monadic semantics of proof-relevant lambda-case -/

namespace Isotope.LambdaCase.Subtyping.Semantics.Named

open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics
open Isotope.LambdaCase.Subtyping.Named

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [InstructionModel Φ τ ε m]

/-- Direct interpretation of a named lambda-case typing derivation. -/
def denote : {Γ : Ctx ν τ} → {t : LambdaCase.Named.Tm ν Φ} → {A : τ} →
    HasType Γ t A → CtxDen Γ → m (TyDen A)
  | _, _, _, .var h, γ => pure (CtxDen.lookup γ _ h)
  | _, _, _, .op hf ha, γ => denote ha γ >>= fun a =>
      InstructionModel.denote (Φ := Φ) (τ := τ) (ε := ε) (m := m) _
        (coeSub hf.input a) >>= fun b => pure (coeSub hf.output b)
  | _, _, _, .let₁ ha hb, γ => denote ha γ >>= fun a => denote hb (γ, a)
  | _, _, _, .unit, _ => pure (TypeModel.unitEquiv.symm ())
  | _, _, _, .pair ha hb, γ => denote ha γ >>= fun a => denote hb γ >>= fun b =>
      pure (TypeModel.tensorEquiv _ _ |>.symm (a, b))
  | _, _, _, .let₂ ha hc, γ => denote ha γ >>= fun ab =>
      let p := TypeModel.tensorEquiv _ _ ab
      denote hc ((γ, p.1), p.2)
  | _, _, _, .inl ha, γ => denote ha γ >>= fun a =>
      pure (TypeModel.coprodEquiv _ _ |>.symm (.inl a))
  | _, _, _, .inr hb, γ => denote hb γ >>= fun b =>
      pure (TypeModel.coprodEquiv _ _ |>.symm (.inr b))
  | _, _, _, .case he hl hr, γ => denote he γ >>= fun e =>
      match TypeModel.coprodEquiv _ _ e with
      | .inl a => denote hl (γ, a)
      | .inr b => denote hr (γ, b)
  | _, _, _, .abort ha, γ => denote ha γ >>= fun z => Empty.elim (TypeModel.emptyEquiv z)
  | _, _, _, .sub ha d, γ => denote ha γ >>= fun a => pure (coeSub d a)

/-- Named lambda-case inclusion into lambda-iter preserves the denotation and
the particular subtyping witnesses carried by the derivation. -/
theorem denote_embed [Isotope.Elgot.Iterate m]
    {Γ : Ctx ν τ} {t : LambdaCase.Named.Tm ν Φ} {A : τ}
    (h : HasType Γ t A) (γ : CtxDen Γ) :
    LambdaIter.Subtyping.Semantics.Named.denote (ε := ε) (m := m) h.embed γ =
      denote (ε := ε) (m := m) h γ := by
  induction h with
  | var | unit => rfl
  | op hf ha ih =>
      simp only [HasType.embed]
      unfold LambdaIter.Subtyping.Semantics.Named.denote denote
      rw [ih]
  | let₁ ha hb iha ihb =>
      simp only [HasType.embed]; unfold LambdaIter.Subtyping.Semantics.Named.denote denote
      rw [iha]; apply bind_congr; intro a; exact ihb (γ, a)
  | pair ha hb iha ihb =>
      simp only [HasType.embed]; unfold LambdaIter.Subtyping.Semantics.Named.denote denote
      rw [iha, ihb]
  | let₂ ha hc iha ihc =>
      simp only [HasType.embed]; unfold LambdaIter.Subtyping.Semantics.Named.denote denote
      rw [iha]; apply bind_congr; intro ab; exact ihc _
  | inl ha ih | inr ha ih | abort ha ih | sub ha _ ih =>
      simp only [HasType.embed]; unfold LambdaIter.Subtyping.Semantics.Named.denote denote
      rw [ih]
  | case he hl hr ihe ihl ihr =>
      simp only [HasType.embed]; unfold LambdaIter.Subtyping.Semantics.Named.denote denote
      rw [ihe]; apply bind_congr; intro e
      split <;> simp_all only

end Isotope.LambdaCase.Subtyping.Semantics.Named
