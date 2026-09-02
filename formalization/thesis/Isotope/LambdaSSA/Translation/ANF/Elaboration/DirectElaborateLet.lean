import Isotope.LambdaSSA.Translation.ANF.Elaboration.DirectElaborateOp

/-! # Direct semantic preservation for unary-let elaboration -/

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

private def letContinuation {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {b : Tm ν Φ (n + 1)} {A B : τ} (hb : HasType Φ Γ (.snoc β A) b B) :
    Program.HasType Γ (.snoc β A) (elaborate b) B := elaborate_hasType hb

private theorem denote_letContinuation {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {b : Tm ν Φ (n + 1)} {A B : τ} (hb : HasType Φ Γ (.snoc β A) b B)
    (γ : CtxDen Γ)
    (ihb : ∀ ρ, denoteProgram (ε := ε) (m := m) (elaborate_hasType hb) γ ρ =
      denote (m := m) (ε := ε) hb.toGeneric γ ρ)
    (ρ : BoundDen β) (x : TypeModel.interp A) :
    denoteProgram (ε := ε) (m := m) (letContinuation hb) γ (ρ, x) =
      denote (m := m) (ε := ε) hb.toGeneric γ (ρ, x) := ihb (ρ, x)

private theorem denote_toGeneric_let₁ {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ (.snoc β A) b B)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (HasType.let₁ ha hb).toGeneric γ ρ =
      (denote (m := m) (ε := ε) ha.toGeneric γ ρ >>= fun x =>
        denote (m := m) (ε := ε) hb.toGeneric γ (ρ, x)) := by
  simp only [Isotope.LambdaIter.LocallyNameless.HasType.toGeneric,
    Isotope.LambdaIter.Subtyping.Semantics.denote]

theorem denote_elaborate_let₁ {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ (.snoc β A) b B)
    (γ : CtxDen Γ)
    (iha : ∀ ρ, denoteProgram (ε := ε) (m := m) (elaborate_hasType ha) γ ρ =
      denote (m := m) (ε := ε) ha.toGeneric γ ρ)
    (ihb : ∀ ρ, denoteProgram (ε := ε) (m := m) (elaborate_hasType hb) γ ρ =
      denote (m := m) (ε := ε) hb.toGeneric γ ρ)
    (ρ : BoundDen β) :
    denoteProgram (ε := ε) (m := m) (elaborate_hasType (HasType.let₁ ha hb)) γ ρ =
      denote (m := m) (ε := ε) (HasType.let₁ ha hb).toGeneric γ ρ := by
  let hk := letContinuation hb
  calc
    _ = denoteProgram (elaborate_hasType ha) γ ρ >>= fun x =>
          denoteProgram hk γ (ρ, x) :=
      denote_bind (hp := elaborate_hasType ha) (hk := hk) γ ρ
    _ = denote ha.toGeneric γ ρ >>= fun x => denote hb.toGeneric γ (ρ, x) := by
      rw [iha ρ]
      apply bind_congr
      exact denote_letContinuation hb γ ihb ρ
    _ = _ := (denote_toGeneric_let₁ ha hb γ ρ).symm

end Isotope.LambdaSSA.Translation.ANF.Elaboration.Direct
