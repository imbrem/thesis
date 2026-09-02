import Isotope.LambdaSSA.Translation.ANF.Elaboration.DirectElaborateInr

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

private def abortContinuation {Γ : Ctx ν τ} {β : BoundCtx τ n} (Φ : Type q)
    [HasTy Φ τ] (A : τ) :
    Program.HasType (Φ := Φ) Γ (.snoc β LambdaIter.empty)
      (.ret (.abort (.bv 0 : Atom ν Φ (n + 1)))) A :=
  .ret (.abort (A := A)
    (show Atom.HasType (Φ := Φ) Γ (.snoc β LambdaIter.empty) (.bv 0)
      LambdaIter.empty from .bv))

private theorem denote_abortContinuation {Γ : Ctx ν τ} {β : BoundCtx τ n} (A : τ)
    (γ : CtxDen Γ) (ρ : BoundDen β) (z : TypeModel.interp LambdaIter.empty) :
    denoteProgram (ε := ε) (m := m)
      (abortContinuation (ν := ν) (Γ := Γ) (β := β) Φ A) γ (ρ, z) =
      (TypeModel.emptyEquiv z).elim := by
  let hz : Atom.HasType (Φ := Φ) Γ (.snoc β LambdaIter.empty) (.bv 0)
      LambdaIter.empty := .bv
  have eh : denoteAtom (ε := ε) (m := m) hz γ (ρ, z) = pure z := by rfl
  unfold abortContinuation denoteProgram denoteAtom
  change (denoteAtom (ε := ε) (m := m) hz γ (ρ, z) >>= fun z =>
    (TypeModel.emptyEquiv z).elim) = _
  rw [eh]
  simp

private theorem denote_toGeneric_abort {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {A : τ} (ha : HasType Φ Γ β a LambdaIter.empty)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (HasType.abort (C := A) ha).toGeneric γ ρ =
      (denote (m := m) (ε := ε) ha.toGeneric γ ρ >>= fun z =>
        (TypeModel.emptyEquiv z).elim) := by
  simp only [Isotope.LambdaIter.LocallyNameless.HasType.toGeneric,
    Isotope.LambdaIter.Subtyping.Semantics.denote]

theorem denote_elaborate_abort {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {A : τ} (ha : HasType Φ Γ β a LambdaIter.empty)
    (γ : CtxDen Γ)
    (ih : ∀ ρ, denoteProgram (ε := ε) (m := m) (elaborate_hasType ha) γ ρ =
      denote (m := m) (ε := ε) ha.toGeneric γ ρ) (ρ : BoundDen β) :
    denoteProgram (ε := ε) (m := m) (elaborate_hasType (HasType.abort (C := A) ha)) γ ρ =
      denote (m := m) (ε := ε) (HasType.abort (C := A) ha).toGeneric γ ρ := by
  let hk := abortContinuation (ν := ν) (Γ := Γ) (β := β) Φ A
  calc
    _ = denoteProgram (elaborate_hasType ha) γ ρ >>= fun z =>
          denoteProgram hk γ (ρ, z) :=
      denote_bind (hp := elaborate_hasType ha) (hk := hk) γ ρ
    _ = (denote (m := m) (ε := ε) ha.toGeneric γ ρ >>= fun z =>
          (TypeModel.emptyEquiv z).elim) := by
      rw [ih ρ]
      apply bind_congr
      exact denote_abortContinuation A γ ρ
    _ = _ := (denote_toGeneric_abort ha γ ρ).symm

end Isotope.LambdaSSA.Translation.ANF.Elaboration.Direct
