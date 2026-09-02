import Isotope.LambdaSSA.Translation.ANF.Elaboration.DirectElaborateBasic

/-! # Direct semantic preservation for primitive-operation elaboration -/

namespace Isotope.LambdaSSA.Translation.ANF.Elaboration.Direct

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

private def opContinuation {Γ : Ctx ν τ} {β : BoundCtx τ n} (f : Φ) :
    Program.HasType Γ (.snoc β (instrSrc f))
      (.ret (.op f (.bv 0))) (instrTrg f) :=
  .ret (.op (show Atom.HasType Γ (.snoc β (instrSrc f)) (.bv 0) (instrSrc f) from .bv))

private theorem denote_opContinuation {Γ : Ctx ν τ} {β : BoundCtx τ n} (f : Φ)
    (γ : CtxDen Γ) (ρ : BoundDen β) (x : TypeModel.interp (instrSrc f)) :
    denoteProgram (ε := ε) (m := m) (opContinuation (Γ := Γ) (β := β) f) γ (ρ, x) =
      InstructionModel.denote ε f x := by
  unfold opContinuation denoteProgram denoteAtom
  change (pure x >>= InstructionModel.denote ε f) = InstructionModel.denote ε f x
  simp

private theorem denote_toGeneric_op {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {f : Φ} (ha : HasType Φ Γ β a (instrSrc f))
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (HasType.op ha).toGeneric γ ρ =
      (denote (m := m) (ε := ε) ha.toGeneric γ ρ >>=
        InstructionModel.denote ε f) := by
  simp only [Isotope.LambdaIter.LocallyNameless.HasType.toGeneric,
    Isotope.LambdaIter.Subtyping.Semantics.denote]

theorem denote_elaborate_op {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {f : Φ} (ha : HasType Φ Γ β a (instrSrc f))
    (γ : CtxDen Γ)
    (ih : ∀ ρ : BoundDen β,
      denoteProgram (ε := ε) (m := m) (elaborate_hasType ha) γ ρ =
        denote (m := m) (ε := ε) ha.toGeneric γ ρ)
    (ρ : BoundDen β) :
    denoteProgram (ε := ε) (m := m) (elaborate_hasType (HasType.op ha)) γ ρ =
      denote (m := m) (ε := ε) (HasType.op ha).toGeneric γ ρ := by
  let hk := opContinuation (Γ := Γ) (β := β) f
  calc
    _ = denoteProgram (elaborate_hasType ha) γ ρ >>= fun x =>
          denoteProgram hk γ (ρ, x) :=
      denote_bind (hp := elaborate_hasType ha) (hk := hk) γ ρ
    _ = denote ha.toGeneric γ ρ >>= InstructionModel.denote ε f := by
      rw [ih ρ]
      apply bind_congr
      exact denote_opContinuation f γ ρ
    _ = _ := by
      exact (denote_toGeneric_op ha γ ρ).symm

end Isotope.LambdaSSA.Translation.ANF.Elaboration.Direct
