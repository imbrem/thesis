import Isotope.LambdaSSA.Translation.ANF.Elaboration.DirectElaborateInl

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

private def inrContinuation {Γ : Ctx ν τ} {β : BoundCtx τ n} (Φ : Type q)
    [HasTy Φ τ] (A B : τ) :
    Program.HasType (Φ := Φ) Γ (.snoc β B)
      (.ret (.inr (.bv 0 : Atom ν Φ (n + 1)))) (LambdaIter.coprod A B) :=
  .ret (.inr (A := A)
    (show Atom.HasType (Φ := Φ) Γ (.snoc β B) (.bv 0) B from .bv))

private theorem denote_inrContinuation {Γ : Ctx ν τ} {β : BoundCtx τ n} (A B : τ)
    (γ : CtxDen Γ) (ρ : BoundDen β) (x : TypeModel.interp B) :
    denoteProgram (ε := ε) (m := m)
      (inrContinuation (ν := ν) (Γ := Γ) (β := β) Φ A B) γ (ρ, x) =
      (pure ((TypeModel.coprodEquiv A B).symm (.inr x)) :
        m (TypeModel.interp (LambdaIter.coprod A B))) := by
  let hb : Atom.HasType (Φ := Φ) Γ (.snoc β B) (.bv 0) B := .bv
  have eh : denoteAtom (ε := ε) (m := m) hb γ (ρ, x) = pure x := by rfl
  unfold inrContinuation denoteProgram denoteAtom
  change (denoteAtom (ε := ε) (m := m) hb γ (ρ, x) >>= fun b =>
    pure ((TypeModel.coprodEquiv A B).symm (.inr b))) = _
  rw [eh]
  simp
  rfl

private theorem denote_toGeneric_inr {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {b : Tm ν Φ n} {A B : τ} (hb : HasType Φ Γ β b B)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (HasType.inr (A := A) hb).toGeneric γ ρ =
      (denote (m := m) (ε := ε) hb.toGeneric γ ρ >>= fun x =>
        pure ((TypeModel.coprodEquiv A B).symm (.inr x))) := by
  simp only [Isotope.LambdaIter.LocallyNameless.HasType.toGeneric,
    Isotope.LambdaIter.Subtyping.Semantics.denote]
  rfl

theorem denote_elaborate_inr {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {b : Tm ν Φ n} {A B : τ} (hb : HasType Φ Γ β b B) (γ : CtxDen Γ)
    (ih : ∀ ρ, denoteProgram (ε := ε) (m := m) (elaborate_hasType hb) γ ρ =
      denote (m := m) (ε := ε) hb.toGeneric γ ρ) (ρ : BoundDen β) :
    denoteProgram (ε := ε) (m := m) (elaborate_hasType (HasType.inr (A := A) hb)) γ ρ =
      denote (m := m) (ε := ε) (HasType.inr (A := A) hb).toGeneric γ ρ := by
  let hk := inrContinuation (ν := ν) (Γ := Γ) (β := β) Φ A B
  calc
    _ = denoteProgram (elaborate_hasType hb) γ ρ >>= fun x =>
          denoteProgram hk γ (ρ, x) :=
      denote_bind (hp := elaborate_hasType hb) (hk := hk) γ ρ
    _ = (denote (m := m) (ε := ε) hb.toGeneric γ ρ >>= fun x =>
          (pure ((TypeModel.coprodEquiv A B).symm (.inr x)) :
            m (TypeModel.interp (LambdaIter.coprod A B)))) := by
      rw [ih ρ]
      apply bind_congr
      exact denote_inrContinuation A B γ ρ
    _ = _ := (denote_toGeneric_inr hb γ ρ).symm

end Isotope.LambdaSSA.Translation.ANF.Elaboration.Direct
