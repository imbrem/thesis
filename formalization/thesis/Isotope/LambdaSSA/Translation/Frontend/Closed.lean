import Isotope.LambdaIter.Typing

/-! # Erasure of impossible free names from closed exact terms -/

namespace Isotope.LambdaSSA.Translation.Frontend.Closed

open Isotope.LambdaIter
open Isotope.LambdaIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]

/-- A closed term with its free-name type erased. -/
def erase : {β : BoundCtx τ n} → {t : Tm ν Φ n} → {A : τ} →
    HasType Φ (Ctx.nil : Ctx ν τ) β t A →
    Σ t' : Tm Empty Φ n, HasType Φ (Ctx.nil : Ctx Empty τ) β t' A
  | _, _, _, .fv h => by simp [Ctx.lookup] at h
  | _, _, _, .bv => ⟨.bv _, .bv⟩
  | _, _, _, .op h =>
      let ⟨a, ha⟩ := erase h
      ⟨.op _ a, .op ha⟩
  | _, _, _, .let₁ ha hb =>
      let ⟨a, ha'⟩ := erase ha
      let ⟨b, hb'⟩ := erase hb
      ⟨.let₁ a b, .let₁ ha' hb'⟩
  | _, _, _, .unit => ⟨.unit, .unit⟩
  | _, _, _, .pair ha hb =>
      let ⟨a, ha'⟩ := erase ha
      let ⟨b, hb'⟩ := erase hb
      ⟨.pair a b, .pair ha' hb'⟩
  | _, _, _, .let₂ ha hb =>
      let ⟨a, ha'⟩ := erase ha
      let ⟨b, hb'⟩ := erase hb
      ⟨.let₂ a b, .let₂ ha' hb'⟩
  | _, _, _, .inl ha =>
      let ⟨a, ha'⟩ := erase ha
      ⟨.inl a, .inl ha'⟩
  | _, _, _, .inr hb =>
      let ⟨b, hb'⟩ := erase hb
      ⟨.inr b, .inr hb'⟩
  | _, _, _, .case he hl hr =>
      let ⟨e, he'⟩ := erase he
      let ⟨l, hl'⟩ := erase hl
      let ⟨r, hr'⟩ := erase hr
      ⟨.case e l r, .case he' hl' hr'⟩
  | _, _, _, .abort ha =>
      let ⟨a, ha'⟩ := erase ha
      ⟨.abort a, .abort ha'⟩
  | _, _, _, .iter ha hb =>
      let ⟨a, ha'⟩ := erase ha
      let ⟨b, hb'⟩ := erase hb
      ⟨.iter a b, .iter ha' hb'⟩

end Isotope.LambdaSSA.Translation.Frontend.Closed
