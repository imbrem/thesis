import Isotope.LambdaSSA.Translation.ANF.Elaboration.Subtyping
import Isotope.LambdaIter.Subtyping.Semantics

/-! # Direct monadic semantics of proof-relevant ANF derivations -/

namespace Isotope.LambdaSSA.Translation.ANF.Subtyping

set_option relaxedAutoImplicit true

open Isotope.Elgot Isotope.LambdaIter
open Isotope.LambdaIter.LocallyNameless
open Isotope.LambdaIter.Subtyping.Semantics

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [LambdaIter.Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Iterate m] [LawfulElgotMonad m] [InstructionModel Φ τ ε m]

mutual
  def denoteAtom {Γ : Ctx ν τ} {β : BoundCtx τ n} {a : ANF.Atom ν Φ n} {A : τ}
      (h : Atom.HasType Γ β a A) (γ : CtxDen Γ) (ρ : BoundDen β) : m (TyDen A) :=
    match h with
    | .fv hx => pure (γ.lookup _ hx)
    | .bv => pure (ρ.get _)
    | .op ha => denoteAtom ha γ ρ >>= InstructionModel.denote ε _
    | .unit => pure (TypeModel.unitEquiv.symm ())
    | .pair ha hb => denoteAtom ha γ ρ >>= fun a => denoteAtom hb γ ρ >>= fun b =>
        pure ((TypeModel.tensorEquiv _ _).symm (a, b))
    | .inl ha => denoteAtom ha γ ρ >>= fun a =>
        pure ((TypeModel.coprodEquiv _ _).symm (.inl a))
    | .inr hb => denoteAtom hb γ ρ >>= fun b =>
        pure ((TypeModel.coprodEquiv _ _).symm (.inr b))
    | .abort ha => denoteAtom ha γ ρ >>= fun z => (TypeModel.emptyEquiv z).elim
    | .sub ha d => denoteAtom ha γ ρ >>= fun a => pure (coeSub d a)

  def denoteProgram {Γ : Ctx ν τ} {β : BoundCtx τ n} {p : ANF.Program ν Φ n} {A : τ}
      (h : Program.HasType Γ β p A) (γ : CtxDen Γ) (ρ : BoundDen β) : m (TyDen A) :=
    match h with
    | .ret ha => denoteAtom ha γ ρ
    | .let₁ hi hb => denoteInstr hi γ ρ >>= fun a => denoteProgram hb γ (ρ, a)
    | .let₂ ha hb => denoteAtom ha γ ρ >>= fun ab =>
        let p := TypeModel.tensorEquiv _ _ ab
        denoteProgram hb γ ((ρ, p.1), p.2)

  def denoteInstr {Γ : Ctx ν τ} {β : BoundCtx τ n} {i : ANF.Instr ν Φ n} {A : τ}
      (h : Instr.HasType Γ β i A) (γ : CtxDen Γ) (ρ : BoundDen β) : m (TyDen A) :=
    match h with
    | .atom ha => denoteAtom ha γ ρ
    | .case he hl hr => denoteAtom he γ ρ >>= fun e =>
        match TypeModel.coprodEquiv _ _ e with
        | .inl a => denoteProgram hl γ (ρ, a)
        | .inr b => denoteProgram hr γ (ρ, b)
    | .iter ha hb => denoteAtom ha γ ρ >>= iter fun a => do
        let s ← denoteProgram hb γ (ρ, a)
        pure (TypeModel.coprodEquiv _ _ s)
end

@[simp] theorem denoteAtom_sub {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a : ANF.Atom ν Φ n} {A B : τ}
    (h : Atom.HasType Γ β a A) (d : Subty A B)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denoteAtom (m := m) (ε := ε) (.sub h d) γ ρ =
      (denoteAtom (m := m) (ε := ε) h γ ρ >>= fun a => pure (coeSub d a)) := rfl

end Isotope.LambdaSSA.Translation.ANF.Subtyping
