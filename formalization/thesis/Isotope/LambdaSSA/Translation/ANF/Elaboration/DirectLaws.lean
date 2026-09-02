import Isotope.LambdaSSA.Translation.ANF.Elaboration.Semantics

/-! # Laws of the direct typed ANF evaluator -/

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

theorem denoteAtom_toLambdaIter {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a : Atom ν Φ n} {A : τ} (h : Atom.HasType Γ β a A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denoteAtom (ε := ε) (m := m) h γ ρ =
      denote (m := m) (ε := ε) h.toLambdaIter.toGeneric γ ρ := by
  induction h with
  | fv | bv | unit =>
      unfold denoteAtom Atom.HasType.toLambdaIter
      unfold Isotope.LambdaIter.LocallyNameless.HasType.toGeneric
      unfold Isotope.LambdaIter.Subtyping.Semantics.denote
      rfl
  | op h ih | inl h ih | inr h ih | abort h ih =>
      unfold denoteAtom Atom.HasType.toLambdaIter
      unfold Isotope.LambdaIter.LocallyNameless.HasType.toGeneric
      unfold Isotope.LambdaIter.Subtyping.Semantics.denote
      rw [ih]
  | pair ha hb iha ihb =>
      unfold denoteAtom Atom.HasType.toLambdaIter
      unfold Isotope.LambdaIter.LocallyNameless.HasType.toGeneric
      unfold Isotope.LambdaIter.Subtyping.Semantics.denote
      rw [iha, ihb]

mutual
  theorem denoteProgram_toLambdaIter {Γ : Ctx ν τ} {β : BoundCtx τ n}
      {p : Program ν Φ n} {A : τ} (h : Program.HasType Γ β p A)
      (γ : CtxDen Γ) (ρ : BoundDen β) :
      denoteProgram (ε := ε) (m := m) h γ ρ =
        denote (m := m) (ε := ε) h.toLambdaIter.toGeneric γ ρ := by
    cases h with
    | ret h => exact denoteAtom_toLambdaIter h γ ρ
    | let₁ hi hb =>
        unfold denoteProgram Program.HasType.toLambdaIter
        unfold Isotope.LambdaIter.LocallyNameless.HasType.toGeneric
        unfold Isotope.LambdaIter.Subtyping.Semantics.denote
        rw [denoteInstr_toLambdaIter hi]
        apply bind_congr
        intro a
        rw [denoteProgram_toLambdaIter hb]
    | let₂ ha hb =>
        unfold denoteProgram Program.HasType.toLambdaIter
        unfold Isotope.LambdaIter.LocallyNameless.HasType.toGeneric
        unfold Isotope.LambdaIter.Subtyping.Semantics.denote
        rw [denoteAtom_toLambdaIter ha]
        apply bind_congr
        intro ab
        rw [denoteProgram_toLambdaIter hb]

  theorem denoteInstr_toLambdaIter {Γ : Ctx ν τ} {β : BoundCtx τ n}
      {i : Instr ν Φ n} {A : τ} (h : Instr.HasType Γ β i A)
      (γ : CtxDen Γ) (ρ : BoundDen β) :
      denoteInstr (ε := ε) (m := m) h γ ρ =
        denote (m := m) (ε := ε) h.toLambdaIter.toGeneric γ ρ := by
    cases h with
    | atom h => exact denoteAtom_toLambdaIter h γ ρ
    | case he hl hr =>
        unfold denoteInstr Instr.HasType.toLambdaIter
        unfold Isotope.LambdaIter.LocallyNameless.HasType.toGeneric
        unfold Isotope.LambdaIter.Subtyping.Semantics.denote
        rw [denoteAtom_toLambdaIter he]
        apply bind_congr
        intro e
        cases TypeModel.coprodEquiv _ _ e with
        | inl a => simp only; exact denoteProgram_toLambdaIter hl γ (ρ, a)
        | inr b => simp only; exact denoteProgram_toLambdaIter hr γ (ρ, b)
    | iter ha hb =>
        unfold denoteInstr Instr.HasType.toLambdaIter
        unfold Isotope.LambdaIter.LocallyNameless.HasType.toGeneric
        unfold Isotope.LambdaIter.Subtyping.Semantics.denote
        rw [denoteAtom_toLambdaIter ha]
        apply bind_congr
        intro a
        congr 1
        funext x
        rw [denoteProgram_toLambdaIter hb]
end

end Isotope.LambdaSSA.Translation.ANF.Elaboration.Direct
