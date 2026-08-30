import Isotope.LambdaIter.Semantics.Substitution
import Isotope.LambdaIter.LocallyNameless.TypedEquiv

/-! # Soundness of the typed lambda-iter equations -/

namespace Isotope.LambdaIter.Semantics

open Isotope.Elgot
open Isotope.LambdaIter.LocallyNameless

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m] [Iterate m]
variable [InstructionModel Φ τ ε m]

theorem sound_letBeta {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (hp : Pure (⊥ : ε) a) (ha : HasType Φ Γ β a A)
    (hb : HasType Φ Γ (.snoc β A) b B) (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (.let₁ ha hb) γ ρ =
      denote (m := m) (ε := ε) (hb.instantiate ha) γ ρ := by
  rcases denote_pure_factor (m := m) (ε := ε) hp ha γ ρ with ⟨x, hx⟩
  simp only [denote, hx, LawfulMonad.pure_bind]
  exact (denote_instantiate (m := m) (ε := ε) hb ha γ ρ x hx).symm

theorem sound_letEta {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {A : τ} (ha : HasType Φ Γ β a A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (.let₁ ha HasType.newest) γ ρ =
      denote (m := m) (ε := ε) ha γ ρ := by
  simp [denote]

theorem sound_unitEta {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} (ha : HasType Φ Γ β a TypeFormers.unit)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (.let₁ ha .unit) γ ρ =
      denote (m := m) (ε := ε) ha γ ρ := by
  simp only [denote]
  calc
    _ = denote (m := m) (ε := ε) ha γ ρ >>= pure := by
      apply bind_congr
      intro x
      congr 1
      exact TypeModel.unitEquiv.injective (Subsingleton.elim _ _)
    _ = _ := bind_pure _

theorem sound_pairEta {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {A B : τ}
    (ha : HasType Φ Γ β a (TypeFormers.tensor A B))
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε)
        (.let₂ ha (.pair HasType.previous HasType.newest)) γ ρ =
      denote (m := m) (ε := ε) ha γ ρ := by
  simp [denote]
  rfl

theorem sound_caseEta {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {e : Tm ν Φ n} {A B : τ}
    (he : HasType Φ Γ β e (TypeFormers.coprod A B))
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε)
        (.case he (.inl HasType.newest) (.inr HasType.newest)) γ ρ =
      denote (m := m) (ε := ε) he γ ρ := by
  simp only [denote]
  rw [← bind_pure (denote (m := m) (ε := ε) he γ ρ)]
  apply bind_congr
  intro e
  cases hs : TypeModel.coprodEquiv A B e with
  | inl a =>
      simp only [denote_newest, LawfulMonad.pure_bind]
      congr 1
      simpa [hs] using (TypeModel.coprodEquiv A B).symm_apply_apply e
  | inr b =>
      simp only [denote_newest, LawfulMonad.pure_bind]
      congr 1
      simpa [hs] using (TypeModel.coprodEquiv A B).symm_apply_apply e

end Isotope.LambdaIter.Semantics
