import Isotope.Elgot.Basic
import Isotope.LambdaIter.Subtyping.Semantics.Instruction

/-!
# Denotational semantics of locally nameless lambda-iter

The semantics is indexed by typing derivations because subtyping is
proof-relevant.  Both free and bound environments retain the full context
spine.  Products are evaluated left-to-right.
-/

namespace Isotope.LambdaIter.Subtyping.Semantics

open Isotope.Elgot
open Isotope.LambdaIter.LocallyNameless

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m] [Iterate m]
variable [InstructionModel Φ τ ε m]

/-- Denotation of a locally nameless typing derivation.  The explicit typing
derivation is semantically relevant precisely at `sub`. -/
def denote : {Γ : Ctx ν τ} → {n : Nat} → {β : BoundCtx τ n} →
    {t : Tm ν Φ n} → {A : τ} → HasType Φ Γ β t A →
      CtxDen Γ → BoundDen β → m (TyDen A)
  | _, _, _, _, _, .fv h, γ, _ => pure (CtxDen.lookup γ _ h)
  | _, _, _, _, _, .bv, _, ρ => pure (BoundDen.get ρ _)
  | _, _, _, _, _, .op ha, γ, ρ =>
      denote ha γ ρ >>=
        InstructionModel.denote (Φ := Φ) (τ := τ) (ε := ε) (m := m) _
  | _, _, _, _, _, .let₁ ha hb, γ, ρ =>
      denote ha γ ρ >>= fun a => denote hb γ (ρ, a)
  | _, _, _, _, _, .unit, _, _ =>
      pure (TypeModel.unitEquiv.symm ())
  | _, _, _, _, _, .pair ha hb, γ, ρ =>
      denote ha γ ρ >>= fun a =>
      denote hb γ ρ >>= fun b =>
      pure (TypeModel.tensorEquiv _ _ |>.symm (a, b))
  | _, _, _, _, _, .let₂ ha hc, γ, ρ =>
      denote ha γ ρ >>= fun ab =>
      let p := TypeModel.tensorEquiv _ _ ab
      denote hc γ ((ρ, p.1), p.2)
  | _, _, _, _, _, .inl ha, γ, ρ =>
      denote ha γ ρ >>= fun a =>
      pure (TypeModel.coprodEquiv _ _ |>.symm (.inl a))
  | _, _, _, _, _, .inr hb, γ, ρ =>
      denote hb γ ρ >>= fun b =>
      pure (TypeModel.coprodEquiv _ _ |>.symm (.inr b))
  | _, _, _, _, _, .case he hl hr, γ, ρ =>
      denote he γ ρ >>= fun e =>
      match TypeModel.coprodEquiv _ _ e with
      | .inl a => denote hl γ (ρ, a)
      | .inr b => denote hr γ (ρ, b)
  | _, _, _, _, _, .abort ha, γ, ρ =>
      denote ha γ ρ >>= fun z => Empty.elim (TypeModel.emptyEquiv z)
  | _, _, _, _, _, .iter ha hb, γ, ρ =>
      denote ha γ ρ >>= Elgot.iter (fun a =>
        denote hb γ (ρ, a) >>= fun s =>
        pure (TypeModel.coprodEquiv _ _ s))
  | _, _, _, _, _, .sub ha d, γ, ρ =>
      denote ha γ ρ >>= fun a => pure (coeSub d a)

/-- Closed denotation is a Kleisli computation. -/
def denoteClosed {t : Tm Empty Φ 0} {A : τ}
    (h : HasType Φ (.nil : Ctx Empty τ) .nil t A) : m (TyDen A) :=
  denote (ε := ε) h PUnit.unit PUnit.unit

end Isotope.LambdaIter.Subtyping.Semantics
