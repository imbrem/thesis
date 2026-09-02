import Isotope.LambdaIter.Named.ToLocallyNameless
import Isotope.LambdaIter.Typing

/-! # Exact typed named-to-locally-nameless translation -/

namespace Isotope.LambdaSSA.Translation.Frontend.NamedToLocallyNameless

open Isotope.LambdaIter

variable {τ : Type u} [TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]

abbrev Scope := LambdaIter.Named.ToLocallyNameless.Scope

def Aligned (Γ : Ctx ν τ) (ρ : Scope ν n)
    (β : LambdaIter.LocallyNameless.BoundCtx τ n) (Δ : Ctx ν τ) : Prop :=
  ∀ {x A}, Δ.lookup x = some A →
    match ρ.resolve x with
    | .inl i => β.get i = A
    | .inr y => Γ.lookup y = some A

theorem Aligned.nil (Γ : Ctx ν τ) : Aligned Γ .nil .nil Γ := fun h => h

theorem Aligned.push (h : Aligned Γ ρ β Δ)
    (q : LambdaIter.Named.Binder ν) (A : τ) :
    Aligned Γ (.push q ρ) (.snoc β A) (.snoc Δ q A) := by
  intro x B hx
  cases q with
  | none =>
      simp only [Ctx.lookup] at hx
      rw [LambdaIter.Named.ToLocallyNameless.Scope.resolve_push_none]
      cases hr : ρ.resolve x <;> simpa [hr] using h hx
  | some y =>
      by_cases e : x = y
      · subst x
        have hAB : A = B := by simpa [Ctx.lookup] using hx
        simpa [LambdaIter.LocallyNameless.BoundCtx.get, hAB]
      · have hx' : Δ.lookup x = some B := by simpa [Ctx.lookup, e] using hx
        rw [LambdaIter.Named.ToLocallyNameless.Scope.resolve_push_ne _ e]
        cases hr : ρ.resolve x <;> simpa [hr] using h hx'

/-- Exact named typing translates to an exact locally nameless witness.  The
witness is proposition-truncated at the Prop-to-Type boundary. -/
theorem translateHasType {ρ : Scope ν n}
    {β : LambdaIter.LocallyNameless.BoundCtx τ n} {Γ Δ : Ctx ν τ}
    {t : LambdaIter.Named.Tm ν Φ} {A : τ} (hρ : Aligned Γ ρ β Δ)
    (h : LambdaIter.Named.HasType Φ Δ t A) :
    Nonempty (LambdaIter.LocallyNameless.HasType Φ Γ β
      (LambdaIter.Named.ToLocallyNameless.translate ρ t) A) := by
  induction h generalizing n ρ β Γ with
  | var hx =>
      unfold LambdaIter.Named.ToLocallyNameless.translate
      split <;> rename_i hr
      · have ht := hρ hx; rw [hr] at ht; exact ⟨ht ▸ .bv⟩
      · have ht := hρ hx; rw [hr] at ht; exact ⟨.fv ht⟩
  | op _ ih => exact (ih hρ).map LambdaIter.LocallyNameless.HasType.op
  | let₁ _ _ iha ihb =>
      obtain ⟨ha⟩ := iha hρ
      obtain ⟨hb⟩ := ihb (Aligned.push hρ _ _)
      exact ⟨.let₁ ha hb⟩
  | unit => exact ⟨.unit⟩
  | pair _ _ iha ihb =>
      obtain ⟨ha⟩ := iha hρ
      obtain ⟨hb⟩ := ihb hρ
      exact ⟨.pair ha hb⟩
  | let₂ _ _ iha ihb =>
      obtain ⟨ha⟩ := iha hρ
      obtain ⟨hb⟩ := ihb (Aligned.push (Aligned.push hρ _ _) _ _)
      exact ⟨.let₂ ha hb⟩
  | inl _ ih => exact (ih hρ).map LambdaIter.LocallyNameless.HasType.inl
  | inr _ ih => exact (ih hρ).map LambdaIter.LocallyNameless.HasType.inr
  | case _ _ _ ihe ihl ihr =>
      obtain ⟨he⟩ := ihe hρ
      obtain ⟨hl⟩ := ihl (Aligned.push hρ _ _)
      obtain ⟨hr⟩ := ihr (Aligned.push hρ _ _)
      exact ⟨.case he hl hr⟩
  | abort _ ih => exact (ih hρ).map LambdaIter.LocallyNameless.HasType.abort
  | iter _ _ iha ihb =>
      obtain ⟨ha⟩ := iha hρ
      obtain ⟨hb⟩ := ihb (Aligned.push hρ _ _)
      exact ⟨.iter ha hb⟩

theorem translateHasTypeClosed {Γ : Ctx ν τ} {t : LambdaIter.Named.Tm ν Φ} {A : τ}
    (h : LambdaIter.Named.HasType Φ Γ t A) :
    Nonempty (LambdaIter.LocallyNameless.HasType Φ Γ .nil
      (LambdaIter.Named.ToLocallyNameless.translateClosed t) A) :=
  translateHasType (Aligned.nil Γ) h

end Isotope.LambdaSSA.Translation.Frontend.NamedToLocallyNameless
