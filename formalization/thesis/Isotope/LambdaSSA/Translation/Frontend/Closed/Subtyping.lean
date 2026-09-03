import Isotope.LambdaSSA.Translation.Frontend.Closed
import Isotope.LambdaIter.Subtyping.LocallyNameless.Typing

namespace Isotope.LambdaSSA.Translation.Frontend.Closed.Subtyping

open Isotope.LambdaIter

variable {τ : Type u} [TypeFormers τ] [LambdaIter.Subtyping τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]

/-- Erase an impossible free-name type while retaining proof-relevant subtype
witnesses. -/
def erase : {β : LambdaIter.LocallyNameless.BoundCtx τ n} →
    {t : LambdaIter.LocallyNameless.Tm ν Φ n} → {A : τ} →
    LambdaIter.Subtyping.LocallyNameless.HasType Φ (Ctx.nil : Ctx ν τ) β t A →
    Σ t' : LambdaIter.LocallyNameless.Tm Empty Φ n,
      LambdaIter.Subtyping.LocallyNameless.HasType Φ
        (Ctx.nil : Ctx Empty τ) β t' A
  | _, _, _, .fv h => by simp [Ctx.lookup] at h
  | _, _, _, .bv => ⟨.bv _, .bv⟩
  | _, _, _, .op h => let ⟨a, ha⟩ := erase h; ⟨.op _ a, .op ha⟩
  | _, _, _, .let₁ ha hb =>
      let ⟨a, ha'⟩ := erase ha; let ⟨b, hb'⟩ := erase hb
      ⟨.let₁ a b, .let₁ ha' hb'⟩
  | _, _, _, .unit => ⟨.unit, .unit⟩
  | _, _, _, .pair ha hb =>
      let ⟨a, ha'⟩ := erase ha; let ⟨b, hb'⟩ := erase hb
      ⟨.pair a b, .pair ha' hb'⟩
  | _, _, _, .let₂ ha hb =>
      let ⟨a, ha'⟩ := erase ha; let ⟨b, hb'⟩ := erase hb
      ⟨.let₂ a b, .let₂ ha' hb'⟩
  | _, _, _, .inl ha => let ⟨a, ha'⟩ := erase ha; ⟨.inl a, .inl ha'⟩
  | _, _, _, .inr hb => let ⟨b, hb'⟩ := erase hb; ⟨.inr b, .inr hb'⟩
  | _, _, _, .case he hl hr =>
      let ⟨e, he'⟩ := erase he; let ⟨l, hl'⟩ := erase hl
      let ⟨r, hr'⟩ := erase hr; ⟨.case e l r, .case he' hl' hr'⟩
  | _, _, _, .abort ha => let ⟨a, ha'⟩ := erase ha; ⟨.abort a, .abort ha'⟩
  | _, _, _, .iter ha hb =>
      let ⟨a, ha'⟩ := erase ha; let ⟨b, hb'⟩ := erase hb
      ⟨.iter a b, .iter ha' hb'⟩
  | _, _, _, .sub ha d => let ⟨a, ha'⟩ := erase ha; ⟨a, .sub ha' d⟩

end Isotope.LambdaSSA.Translation.Frontend.Closed.Subtyping
