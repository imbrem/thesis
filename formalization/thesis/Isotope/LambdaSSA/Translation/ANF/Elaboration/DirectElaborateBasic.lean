import Isotope.LambdaSSA.Translation.ANF.Elaboration.DirectBind

/-! # Direct semantic preservation for basic ANF elaboration constructors -/

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

theorem denote_elaborate_fv {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {x : ν} {A : τ} (hx : Γ.lookup x = some A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denoteProgram (ε := ε) (m := m)
      (elaborate_hasType (HasType.fv (Φ := Φ) hx)) γ ρ =
    denote (m := m) (ε := ε) (HasType.fv (Φ := Φ) hx).toGeneric γ ρ := by
  unfold elaborate_hasType denoteProgram denoteAtom
  unfold Isotope.LambdaIter.LocallyNameless.HasType.toGeneric
  unfold Isotope.LambdaIter.Subtyping.Semantics.denote
  rfl

theorem denote_elaborate_bv {Γ : Ctx ν τ} {β : BoundCtx τ n}
    (i : Fin n) (γ : CtxDen Γ) (ρ : BoundDen β) :
    denoteProgram (ε := ε) (m := m)
      (elaborate_hasType (show HasType Φ Γ β (.bv i) (β.get i) from .bv)) γ ρ =
    denote (m := m) (ε := ε)
      (show HasType Φ Γ β (.bv i) (β.get i) from .bv).toGeneric γ ρ := by
  unfold elaborate_hasType denoteProgram denoteAtom
  unfold Isotope.LambdaIter.LocallyNameless.HasType.toGeneric
  unfold Isotope.LambdaIter.Subtyping.Semantics.denote
  rfl

theorem denote_elaborate_unit {Γ : Ctx ν τ} {β : BoundCtx τ n}
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denoteProgram (ε := ε) (m := m)
      (elaborate_hasType (HasType.unit (Φ := Φ) (Γ := Γ) (β := β))) γ ρ =
    denote (m := m) (ε := ε)
      (HasType.unit (Φ := Φ) (Γ := Γ) (β := β)).toGeneric γ ρ := by
  unfold elaborate_hasType denoteProgram denoteAtom
  unfold Isotope.LambdaIter.LocallyNameless.HasType.toGeneric
  unfold Isotope.LambdaIter.Subtyping.Semantics.denote
  rfl

end Isotope.LambdaSSA.Translation.ANF.Elaboration.Direct
