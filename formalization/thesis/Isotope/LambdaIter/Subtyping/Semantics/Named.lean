import Isotope.Elgot.Basic
import Isotope.LambdaIter.Subtyping.Named.Typing
import Isotope.LambdaIter.Subtyping.Semantics.Instruction

/-!
# Denotational semantics of named lambda-iter

Unlike the locally-nameless interpretation, the environment itself grows at
a named binder.  Lookup already implements shadowing, so anonymous and
shadowed context slots remain present semantically without affecting name
resolution.
-/

namespace Isotope.LambdaIter.Subtyping.Semantics.Named

open Isotope.Elgot
open Isotope.LambdaIter

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m] [Iterate m]
variable [InstructionModel Φ τ ε m]

include ε in
/-- Interpretation of a proof-relevant named typing derivation. -/
def denote : {Γ : Ctx ν τ} → {t : LambdaIter.Named.Tm ν Φ} → {A : τ} →
    LambdaIter.Subtyping.Named.HasType Γ t A → CtxDen Γ → m (TyDen A)
  | _, _, _, .var h, γ => pure (CtxDen.lookup γ _ h)
  | _, _, _, .op hf ha, γ =>
      denote ha γ >>= fun a =>
      InstructionModel.denote (Φ := Φ) (τ := τ) (ε := ε) (m := m) _
        (coeSub hf.input a) >>= fun b =>
      pure (coeSub hf.output b)
  | _, _, _, .let₁ ha hb, γ =>
      denote ha γ >>= fun a => denote hb (γ, a)
  | _, _, _, .unit, _ => pure (TypeModel.unitEquiv.symm ())
  | _, _, _, .pair ha hb, γ =>
      denote ha γ >>= fun a =>
      denote hb γ >>= fun b =>
      pure (TypeModel.tensorEquiv _ _ |>.symm (a, b))
  | _, _, _, .let₂ ha hc, γ =>
      denote ha γ >>= fun ab =>
      let p := TypeModel.tensorEquiv _ _ ab
      denote hc ((γ, p.1), p.2)
  | _, _, _, .inl ha, γ =>
      denote ha γ >>= fun a =>
      pure (TypeModel.coprodEquiv _ _ |>.symm (.inl a))
  | _, _, _, .inr hb, γ =>
      denote hb γ >>= fun b =>
      pure (TypeModel.coprodEquiv _ _ |>.symm (.inr b))
  | _, _, _, .case he hl hr, γ =>
      denote he γ >>= fun e =>
      match TypeModel.coprodEquiv _ _ e with
      | .inl a => denote hl (γ, a)
      | .inr b => denote hr (γ, b)
  | _, _, _, .abort ha, γ =>
      denote ha γ >>= fun z => Empty.elim (TypeModel.emptyEquiv z)
  | _, _, _, .iter ha hb, γ =>
      denote ha γ >>= Elgot.iter (fun a =>
        denote hb (γ, a) >>= fun s =>
        pure (TypeModel.coprodEquiv _ _ s))
  | _, _, _, .sub ha d, γ =>
      denote ha γ >>= fun a => pure (coeSub d a)

/-- A closed named derivation denotes a computation. -/
def denoteClosed {t : LambdaIter.Named.Tm Empty Φ} {A : τ}
    (h : LambdaIter.Subtyping.Named.HasType (.nil : Ctx Empty τ) t A) : m (TyDen A) :=
  denote (ε := ε) (m := m) h PUnit.unit

end Isotope.LambdaIter.Subtyping.Semantics.Named
