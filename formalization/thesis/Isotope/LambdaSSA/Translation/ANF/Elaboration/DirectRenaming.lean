import Isotope.LambdaSSA.Translation.ANF.Elaboration.DirectLaws

/-! # Renaming naturality of the direct typed ANF evaluator -/

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

/-- Naturality of direct program evaluation under a typed bound renaming. -/
theorem denote_programRename {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {β' : BoundCtx τ k} {p : Program ν Φ n} {A : τ}
    (h : Program.HasType Γ β p A) (s : TypedRenaming β β')
    (γ : CtxDen Γ) (ρ : BoundDen β') :
    denoteProgram (ε := ε) (m := m) (programRename_hasType s h) γ ρ =
      denoteProgram (ε := ε) (m := m) h γ
        (BoundDen.pull ({ toFun := s.toFun, typed := s.typed } :
          Isotope.LambdaIter.Subtyping.LocallyNameless.TypedRenaming β β') ρ) := by
  rw [denoteProgram_toLambdaIter, denoteProgram_toLambdaIter]
  exact Isotope.LambdaSSA.Translation.ANF.Elaboration.denote_programRename h s γ ρ

end Isotope.LambdaSSA.Translation.ANF.Elaboration.Direct
