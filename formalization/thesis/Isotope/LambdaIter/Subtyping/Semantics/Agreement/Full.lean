import Isotope.LambdaIter.Subtyping.Semantics.Agreement.Combinators

namespace Isotope.LambdaIter.Subtyping.Semantics

open CategoryTheory CategoryTheory.Limits Isotope.Elgot
open Isotope.LambdaIter.LocallyNameless

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Iterate m] [LawfulElgotMonad m]
variable [InstructionModel Φ τ ε m]

/-- The abstract categorical semantics, specialized to the Kleisli category of the
monadic model, agrees pointwise with the direct monadic semantics. -/
theorem categorical_denote_eq {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    (Categorical.denoteOfType (ε := ε) (m := m) h).of
        (envToCategorical γ ρ) =
      denote (ε := ε) (m := m) h γ ρ := by
  letI := Categorical.ofInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  induction h with
  | fv h =>
      simp [Categorical.denoteOfType, Categorical.denote, denote,
        freeLookup_toCategorical]
  | bv =>
      simp [Categorical.denoteOfType, Categorical.denote, denote,
        boundVar_toCategorical]
  | op ha ih =>
      have hi := ih ρ
      unfold Categorical.denoteOfType at hi
      simp [Categorical.denoteOfType, Categorical.denote, denote,
        Categorical.ofInstructionModel, Isotope.Elgot.kcomp, joinM,
        bind_map_left, hi]
      rfl
  | let₁ ha hb iha ihb =>
      have hia := iha ρ
      unfold Categorical.denoteOfType at hia
      have hib (a) := ihb (ρ, a)
      unfold Categorical.denoteOfType at hib
      simp [Categorical.denoteOfType, Categorical.denote, denote,
        Categorical.bind_of, hia, hib, envSnocIso_toCategorical,
        Isotope.Elgot.kcomp]
      rfl
  | unit =>
      simp [Categorical.denoteOfType, Categorical.denote, denote,
        Categorical.ofTypeModel, Kleisli.Adjunction.toKleisli]
  | pair ha hb iha ihb =>
      have hia := iha ρ
      unfold Categorical.denoteOfType at hia
      have hib := ihb ρ
      unfold Categorical.denoteOfType at hib
      simp [Categorical.denoteOfType, Categorical.denote, denote,
        Categorical.pair_of, Categorical.comp_map_of, hia, hib,
        Categorical.ofTypeModel, Isotope.Elgot.kcomp, Isotope.Elgot.liftPure,
        joinM, bind_map_left]
  | let₂ ha hc iha ihc =>
      have hia := iha ρ
      unfold Categorical.denoteOfType at hia
      have hic (a : TyDen _) (b : TyDen _) := ihc ((ρ, a), b)
      unfold Categorical.denoteOfType at hic
      simp [Categorical.denoteOfType, Categorical.denote, denote,
        Categorical.bind_of, Categorical.comp_map_of, hia, hic,
        Categorical.ofTypeModel, envPairHom_toCategorical,
        Isotope.Elgot.kcomp, joinM, bind_map_left]
      apply bind_congr
      intro ab
      generalize hp : TypeModel.tensorEquiv _ _ ab = p
      rcases p with ⟨a, b⟩
      simp only [hp]
      rw [envPairHom_toCategorical]
      exact hic a b
  | inl ha ih =>
      have hi := ih ρ
      unfold Categorical.denoteOfType at hi
      simp [Categorical.denoteOfType, Categorical.denote, denote,
        Categorical.comp_map_of, Categorical.ofTypeModel, hi,
        Isotope.Elgot.kcomp, joinM, bind_map_left]
  | inr hb ih =>
      have hi := ih ρ
      unfold Categorical.denoteOfType at hi
      simp [Categorical.denoteOfType, Categorical.denote, denote,
        Categorical.comp_map_of, Categorical.ofTypeModel, hi,
        Isotope.Elgot.kcomp, joinM, bind_map_left]
  | case he hl hr ihe ihl ihr =>
      have hie := ihe ρ
      unfold Categorical.denoteOfType at hie
      have hil (a) := ihl (ρ, a)
      unfold Categorical.denoteOfType at hil
      have hir (b) := ihr (ρ, b)
      unfold Categorical.denoteOfType at hir
      simp [Categorical.denoteOfType, Categorical.denote, denote,
        Categorical.caseWithContext_of, Categorical.comp_map_of,
        Categorical.ofTypeModel, hie, hil, hir, envSnocIso_toCategorical,
        Isotope.Elgot.kcomp, joinM, bind_map_left]
      apply bind_congr
      intro e
      cases h : TypeModel.coprodEquiv _ _ e with
      | inl a =>
          simp only [h]
          rw [envSnocIso_toCategorical]
          exact hil a
      | inr b =>
          simp only [h]
          rw [envSnocIso_toCategorical]
          exact hir b
  | abort ha ih =>
      have hi := ih ρ
      unfold Categorical.denoteOfType at hi
      simp [Categorical.denoteOfType, Categorical.denote, denote,
        Categorical.abort, Categorical.abort_of, Categorical.ofTypeModel, hi,
        Isotope.Elgot.kcomp, joinM, bind_map_left]
      apply bind_congr
      intro z
      exact Empty.elim (TypeModel.emptyEquiv z)
  | iter ha hb iha ihb =>
      have hia := iha ρ
      unfold Categorical.denoteOfType at hia
      have hib (a) := ihb (ρ, a)
      unfold Categorical.denoteOfType at hib
      simp [Categorical.denoteOfType, Categorical.denote, denote,
        Categorical.bind_of, Categorical.contextualLoop_of,
        Categorical.comp_map_of, Categorical.ofTypeModel, hia, hib,
        envSnocIso_toCategorical, Isotope.Elgot.kcomp, joinM, bind_map_left]
      apply bind_congr
      intro a
      apply congrArg (fun q => Isotope.Elgot.iter (m := m) q a)
      funext x
      rw [envSnocIso_toCategorical, hib x]
  | sub ha hAB ih =>
      have hi := ih ρ
      unfold Categorical.denoteOfType at hi
      simp [Categorical.denoteOfType, Categorical.denote, denote,
        Categorical.comp_map_of, Categorical.ofTypeModel, hi,
        Isotope.Elgot.kcomp, Isotope.Elgot.liftPure, joinM, bind_map_left,
        coeSub, bind_pure_comp]
      change (denote ha γ ρ >>= fun a => pure (TypeModel.coe hAB a)) = _
      exact bind_pure_comp _ _

end Isotope.LambdaIter.Subtyping.Semantics
