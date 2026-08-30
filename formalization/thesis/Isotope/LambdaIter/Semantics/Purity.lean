import Isotope.LambdaIter.Semantics.Denotation

/-!
# Denotation of pure terms

Iteration is intentionally absent from `LocallyNameless.Pure`: an iteration
whose instructions are pure can still diverge.  A purity certificate is a
proposition, so its semantic content is stated propositionally as existence
of an ordinary value through which the computation factors.
-/

namespace Isotope.LambdaIter.Semantics

open Isotope.LambdaIter.LocallyNameless

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m] [Elgot.Iterate m]
variable [InstructionModel Φ τ ε m]

/-- Every syntactically pure, well-typed term denotes a monadic `pure` value. -/
theorem denote_pure_factor {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (hp : Pure (⊥ : ε) t)
    (h : HasType Φ Γ β t A) (γ : CtxDen Γ) (ρ : BoundDen β) :
    ∃ a : TyDen A, denote (ε := ε) h γ ρ = (pure a : m (TyDen A)) := by
  induction h with
  | fv h => exact ⟨CtxDen.lookup γ _ h, by simp [denote]⟩
  | bv => exact ⟨BoundDen.get ρ _, by simp [denote]⟩
  | op ha ih =>
      cases hp with
      | op hf hpa =>
          rcases ih hpa ρ with ⟨a, ha'⟩
          refine ⟨InstructionModel.denotePure
            (Φ := Φ) (τ := τ) (ε := ε) (m := m) _ hf a, ?_⟩
          rw [denote, ha', LawfulMonad.pure_bind]
          exact InstructionModel.denote_pure
            (Φ := Φ) (τ := τ) (ε := ε) (m := m) _ hf a
  | let₁ ha hb iha ihb =>
      cases hp with
      | let₁ hpa hpb =>
          rcases iha hpa ρ with ⟨a, ha'⟩
          rcases ihb hpb (ρ, a) with ⟨b, hb'⟩
          exact ⟨b, by simp [denote, ha', hb']⟩
  | unit => exact ⟨TypeModel.unitEquiv.symm (), by simp [denote]⟩
  | pair ha hb iha ihb =>
      cases hp with
      | pair hpa hpb =>
          rcases iha hpa ρ with ⟨a, ha'⟩
          rcases ihb hpb ρ with ⟨b, hb'⟩
          exact ⟨TypeModel.tensorEquiv _ _ |>.symm (a, b), by simp [denote, ha', hb']⟩
  | let₂ ha hb iha ihb =>
      cases hp with
      | let₂ hpa hpb =>
          rcases iha hpa ρ with ⟨ab, hab⟩
          let p := TypeModel.tensorEquiv _ _ ab
          rcases ihb hpb ((ρ, p.1), p.2) with ⟨c, hc⟩
          exact ⟨c, by simp [denote, hab, p, hc]⟩
  | inl ha ih =>
      cases hp with
      | inl hpa =>
          rcases ih hpa ρ with ⟨a, ha'⟩
          exact ⟨TypeModel.coprodEquiv _ _ |>.symm (.inl a), by simp [denote, ha']⟩
  | inr hb ih =>
      cases hp with
      | inr hpb =>
          rcases ih hpb ρ with ⟨b, hb'⟩
          exact ⟨TypeModel.coprodEquiv _ _ |>.symm (.inr b), by simp [denote, hb']⟩
  | case he hl hr ihe ihl ihr =>
      cases hp with
      | case hpe hpl hpr =>
          rcases ihe hpe ρ with ⟨e, he'⟩
          rw [denote, he', LawfulMonad.pure_bind]
          cases hs : TypeModel.coprodEquiv _ _ e with
          | inl a =>
              rcases ihl hpl (ρ, a) with ⟨c, hc⟩
              exact ⟨c, by simpa [hs] using hc⟩
          | inr b =>
              rcases ihr hpr (ρ, b) with ⟨c, hc⟩
              exact ⟨c, by simpa [hs] using hc⟩
  | abort ha ih =>
      cases hp with
      | abort hpa =>
          rcases ih hpa ρ with ⟨z, hz⟩
          exact Empty.elim (TypeModel.emptyEquiv z)
  | iter ha hb iha ihb => cases hp
  | sub ha d ih =>
      rcases ih hp ρ with ⟨a, ha'⟩
      exact ⟨coeSub d a, by simp [denote, ha']⟩

end Isotope.LambdaIter.Semantics
