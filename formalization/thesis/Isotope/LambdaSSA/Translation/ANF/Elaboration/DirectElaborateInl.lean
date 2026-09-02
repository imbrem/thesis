import Isotope.LambdaSSA.Translation.ANF.Elaboration.DirectElaborateLet

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

private def inlContinuation {Γ : Ctx ν τ} {β : BoundCtx τ n} (Φ : Type q)
    [HasTy Φ τ] (A B : τ) :
    Program.HasType (Φ := Φ) Γ (.snoc β A)
      (.ret (.inl (.bv 0 : Atom ν Φ (n + 1)))) (LambdaIter.coprod A B) :=
  .ret (.inl (B := B)
    (show Atom.HasType (Φ := Φ) Γ (.snoc β A) (.bv 0) A from .bv))

private theorem denote_inlContinuation {Γ : Ctx ν τ} {β : BoundCtx τ n} (A B : τ)
    (γ : CtxDen Γ) (ρ : BoundDen β) (x : TypeModel.interp A) :
    denoteProgram (ε := ε) (m := m)
      (inlContinuation (ν := ν) (Γ := Γ) (β := β) Φ A B) γ (ρ, x) =
      (pure ((TypeModel.coprodEquiv A B).symm (.inl x)) :
        m (TypeModel.interp (LambdaIter.coprod A B))) := by
  let hb : Atom.HasType (Φ := Φ) Γ (.snoc β A) (.bv 0) A := .bv
  have eh : denoteAtom (ε := ε) (m := m) hb γ (ρ, x) = pure x := by rfl
  unfold inlContinuation denoteProgram denoteAtom
  change (denoteAtom (ε := ε) (m := m) hb γ (ρ, x) >>= fun a =>
    pure ((TypeModel.coprodEquiv A B).symm (.inl a))) = _
  rw [eh]
  simp
  rfl

private theorem denote_toGeneric_inl {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {A B : τ} (ha : HasType Φ Γ β a A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (HasType.inl (B := B) ha).toGeneric γ ρ =
      (denote (m := m) (ε := ε) ha.toGeneric γ ρ >>= fun x =>
        pure ((TypeModel.coprodEquiv A B).symm (.inl x))) := by
  simp only [Isotope.LambdaIter.LocallyNameless.HasType.toGeneric,
    Isotope.LambdaIter.Subtyping.Semantics.denote]
  rfl

theorem denote_elaborate_inl {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {A B : τ} (ha : HasType Φ Γ β a A) (γ : CtxDen Γ)
    (ih : ∀ ρ, denoteProgram (ε := ε) (m := m) (elaborate_hasType ha) γ ρ =
      denote (m := m) (ε := ε) ha.toGeneric γ ρ) (ρ : BoundDen β) :
    denoteProgram (ε := ε) (m := m) (elaborate_hasType (HasType.inl (B := B) ha)) γ ρ =
      denote (m := m) (ε := ε) (HasType.inl (B := B) ha).toGeneric γ ρ := by
  let hk := inlContinuation (ν := ν) (Γ := Γ) (β := β) Φ A B
  calc
    _ = denoteProgram (elaborate_hasType ha) γ ρ >>= fun x =>
          denoteProgram hk γ (ρ, x) :=
      denote_bind (hp := elaborate_hasType ha) (hk := hk) γ ρ
    _ = (denote (m := m) (ε := ε) ha.toGeneric γ ρ >>= fun x =>
          (pure ((TypeModel.coprodEquiv A B).symm (.inl x)) :
            m (TypeModel.interp (LambdaIter.coprod A B)))) := by
      rw [ih ρ]
      apply bind_congr
      exact denote_inlContinuation A B γ ρ
    _ = _ := (denote_toGeneric_inl ha γ ρ).symm

end Isotope.LambdaSSA.Translation.ANF.Elaboration.Direct
