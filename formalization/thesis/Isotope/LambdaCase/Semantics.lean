import Isotope.LambdaCase.Equiv
import Isotope.LambdaIter.Subtyping.Semantics.Denotation

/-! # Monadic denotational semantics of lambda-case -/

namespace Isotope.LambdaCase.Semantics

open Isotope.LambdaCase.LocallyNameless

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

/-- Lambda-case is interpreted by every lawful monad; no iteration operation
or Elgot laws are required. -/
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
  | _, _, _, _, _, .unit, _, _ =>
      pure (LambdaIter.Subtyping.Semantics.TypeModel.unitEquiv.symm ())
  | _, _, _, _, _, .pair ha hb, γ, ρ =>
      denote ha γ ρ >>= fun a => denote hb γ ρ >>= fun b =>
        pure (LambdaIter.Subtyping.Semantics.TypeModel.tensorEquiv _ _ |>.symm (a, b))
  | _, _, _, _, _, .let₂ ha hc, γ, ρ =>
      denote ha γ ρ >>= fun ab =>
        let p := LambdaIter.Subtyping.Semantics.TypeModel.tensorEquiv _ _ ab
        denote hc γ ((ρ, p.1), p.2)
  | _, _, _, _, _, .inl ha, γ, ρ =>
      denote ha γ ρ >>= fun a =>
        pure (LambdaIter.Subtyping.Semantics.TypeModel.coprodEquiv _ _ |>.symm (.inl a))
  | _, _, _, _, _, .inr hb, γ, ρ =>
      denote hb γ ρ >>= fun b =>
        pure (LambdaIter.Subtyping.Semantics.TypeModel.coprodEquiv _ _ |>.symm (.inr b))
  | _, _, _, _, _, .case he hl hr, γ, ρ =>
      denote he γ ρ >>= fun e =>
        match LambdaIter.Subtyping.Semantics.TypeModel.coprodEquiv _ _ e with
        | .inl a => denote hl γ (ρ, a)
        | .inr b => denote hr γ (ρ, b)
  | _, _, _, _, _, .abort ha, γ, ρ =>
      denote ha γ ρ >>= fun z =>
        Empty.elim (LambdaIter.Subtyping.Semantics.TypeModel.emptyEquiv z)

def denoteClosed {t : Tm Empty Φ 0} {A : τ}
    (h : HasType Φ (.nil : Ctx Empty τ) .nil t A) : m (TyDen A) :=
  denote (ε := ε) h PUnit.unit PUnit.unit

end Isotope.LambdaCase.Semantics
