import Isotope.LambdaSSA.Translation.ANF.Elaboration.DirectElaborateIter

/-! # Direct denotational preservation of LambdaIter-to-ANF elaboration -/

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

/-- Direct execution of the elaborated ANF program agrees with the monadic
denotation of the exactly typed LambdaIter source. -/
theorem denote_elaborate {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denoteProgram (ε := ε) (m := m) (elaborate_hasType h) γ ρ =
      denote (m := m) (ε := ε) h.toGeneric γ ρ := by
  induction h with
  | fv hx => exact denote_elaborate_fv hx γ ρ
  | bv => exact denote_elaborate_bv _ γ ρ
  | op ha ih => exact denote_elaborate_op ha γ ih ρ
  | let₁ ha hb iha ihb => exact denote_elaborate_let₁ ha hb γ iha ihb ρ
  | unit => exact denote_elaborate_unit γ ρ
  | pair ha hb iha ihb => exact denote_elaborate_pair ha hb γ iha ihb ρ
  | let₂ ha hb iha ihb => exact denote_elaborate_let₂ ha hb γ iha ihb ρ
  | inl ha ih => exact denote_elaborate_inl ha γ ih ρ
  | inr hb ih => exact denote_elaborate_inr hb γ ih ρ
  | case he hl hr ihe ihl ihr => exact denote_elaborate_case he hl hr γ ihe ihl ihr ρ
  | abort ha ih => exact denote_elaborate_abort ha γ ih ρ
  | iter ha hb iha ihb => exact denote_elaborate_iter ha hb γ iha ihb ρ

end Isotope.LambdaSSA.Translation.ANF.Elaboration.Direct
