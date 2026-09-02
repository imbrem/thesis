import Isotope.LambdaIter.Subtyping.Named.Typing
import Isotope.LambdaIter.Subtyping.LocallyNameless.Typing
import Isotope.LambdaIter.Named.ToLocallyNameless

/-! # Typed named-to-locally-nameless translation with subtyping -/

namespace Isotope.LambdaIter.Subtyping.Named.ToLocallyNameless

open Isotope.LambdaIter

universe u v w

variable {ν : Type u} {τ : Type v} {Φ : Type w}
variable [DecidableEq ν] [TypeFormers τ] [Subtyping τ] [HasTy Φ τ]

abbrev Scope := LambdaIter.Named.ToLocallyNameless.Scope

/-- A name scope and a bound context jointly describe the suffix added to a
fixed free-variable context.  The lookup formulation handles anonymous and
shadowing binders without imposing uniqueness of names. -/
def Aligned (Γ : LambdaIter.Ctx ν τ) (ρ : Scope ν n)
    (β : LocallyNameless.BoundCtx τ n) (Δ : LambdaIter.Ctx ν τ) : Prop :=
  ∀ {x A}, Δ.lookup x = some A →
    match ρ.resolve x with
    | .inl i => β.get i = A
    | .inr y => Γ.lookup y = some A

namespace Aligned

theorem nil (Γ : LambdaIter.Ctx ν τ) :
    Aligned Γ .nil .nil Γ := by
  intro x A hx
  exact hx

theorem push (h : Aligned Γ ρ β Δ)
    (q : LambdaIter.Named.Binder ν) (A : τ) :
    Aligned Γ (.push q ρ) (.snoc β A) (.snoc Δ q A) := by
  intro x B hx
  cases q with
  | none =>
      simp only [LambdaIter.Ctx.lookup] at hx
      rw [LambdaIter.Named.ToLocallyNameless.Scope.resolve_push_none]
      cases hr : ρ.resolve x with
      | inl i => simpa [hr] using h hx
      | inr y => simpa [hr] using h hx
  | some y =>
      by_cases e : x = y
      · subst x
        have hAB : A = B := by simpa [LambdaIter.Ctx.lookup] using hx
        simpa [LambdaIter.LocallyNameless.BoundCtx.get, hAB]
      · have hx' : Δ.lookup x = some B := by
          simpa [LambdaIter.Ctx.lookup, e] using hx
        rw [LambdaIter.Named.ToLocallyNameless.Scope.resolve_push_ne _ e]
        cases hr : ρ.resolve x with
        | inl i => simpa [hr] using h hx'
        | inr z => simpa [hr] using h hx'

end Aligned

/-- Translate a proof-relevant named typing derivation.  In the instruction
case the input and output subtype witnesses carried by `InstTy` become the
two explicit locally nameless coercion nodes, so no proof data is discarded. -/
def translateHasType {ρ : Scope ν n} {β : LocallyNameless.BoundCtx τ n}
    {Γ Δ : LambdaIter.Ctx ν τ} {t : LambdaIter.Named.Tm ν Φ} {A : τ}
    (hρ : Aligned Γ ρ β Δ) : Named.HasType Δ t A →
      LocallyNameless.HasType Φ Γ β
        (LambdaIter.Named.ToLocallyNameless.translate ρ t) A
  | .var hx => by
      unfold LambdaIter.Named.ToLocallyNameless.translate
      split <;> rename_i hr
      · have h := hρ hx
        rw [hr] at h
        exact h ▸ .bv
      · have h := hρ hx
        rw [hr] at h
        exact .fv h
  | .op hf ha =>
      .sub (.op (.sub (translateHasType hρ ha) hf.input)) hf.output
  | .let₁ ha hb => .let₁ (translateHasType hρ ha)
      (translateHasType (Aligned.push hρ _ _) hb)
  | .unit => .unit
  | .pair ha hb => .pair (translateHasType hρ ha) (translateHasType hρ hb)
  | .let₂ ha hc => .let₂ (translateHasType hρ ha)
      (translateHasType (Aligned.push (Aligned.push hρ _ _) _ _) hc)
  | .inl ha => .inl (translateHasType hρ ha)
  | .inr hb => .inr (translateHasType hρ hb)
  | .case he hl hr => .case (translateHasType hρ he)
      (translateHasType (Aligned.push hρ _ _) hl)
      (translateHasType (Aligned.push hρ _ _) hr)
  | .abort ha => .abort (translateHasType hρ ha)
  | .iter ha hb => .iter (translateHasType hρ ha)
      (translateHasType (Aligned.push hρ _ _) hb)
  | .sub ha hAB => .sub (translateHasType hρ ha) hAB

/-- Translation at the empty binder scope, retaining the original free
context. -/
def translateHasTypeClosed {Γ : LambdaIter.Ctx ν τ}
    {t : LambdaIter.Named.Tm ν Φ} {A : τ} (h : Named.HasType Γ t A) :
    LocallyNameless.HasType Φ Γ .nil
      (LambdaIter.Named.ToLocallyNameless.translateClosed t) A :=
  translateHasType (Aligned.nil Γ) h

end Isotope.LambdaIter.Subtyping.Named.ToLocallyNameless
