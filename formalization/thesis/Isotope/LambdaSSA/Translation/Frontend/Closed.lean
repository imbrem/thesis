import Isotope.LambdaIter.Semantics.Denotation

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

section Semantics

variable [Subtyping τ] [Subtyping.Semantics.TypeModel.{u, v} τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Isotope.Elgot.Iterate m]
variable [Subtyping.Semantics.InstructionModel Φ τ ε m]

/-- Erasing the impossible free-name type of an exactly typed closed term
does not change its direct monadic denotation. -/
theorem erase_denotes {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ (Ctx.nil : Ctx ν τ) β t A)
    (ρ : Subtyping.Semantics.BoundDen β) :
    LambdaIter.Semantics.denote (ε := ε) (m := m) (erase h).2 PUnit.unit ρ =
      LambdaIter.Semantics.denote (ε := ε) (m := m) h PUnit.unit ρ := by
  induction h with
  | fv hx => simp [Ctx.lookup] at hx
  | bv | unit => rfl
  | op ha ih =>
      simp only [erase, LambdaIter.Semantics.denote]
      congr 1
      exact ih ρ
  | let₁ ha hb iha ihb =>
      simp only [erase, LambdaIter.Semantics.denote]
      congr 1
      · exact iha ρ
      funext a
      exact ihb (ρ, a)
  | pair ha hb iha ihb =>
      simp only [erase, LambdaIter.Semantics.denote]
      rw [iha, ihb]
  | let₂ ha hb iha ihb =>
      simp only [erase, LambdaIter.Semantics.denote]
      congr 1
      · exact iha ρ
      funext ab
      exact ihb _
  | inl ha ih | inr ha ih =>
      simp only [erase, LambdaIter.Semantics.denote]
      rw [ih]
  | abort ha ih =>
      simp only [erase, LambdaIter.Semantics.denote]
      congr 1
      exact ih ρ
  | case he hl hr ihe ihl ihr =>
      simp only [erase, LambdaIter.Semantics.denote]
      congr 1
      · exact ihe ρ
      funext e
      cases hs : Subtyping.Semantics.TypeModel.coprodEquiv _ _ e with
      | inl a => simpa only [hs] using ihl (ρ, a)
      | inr b => simpa only [hs] using ihr (ρ, b)
  | iter ha hb iha ihb =>
      simp only [erase, LambdaIter.Semantics.denote]
      congr 1
      · exact iha ρ
      funext a
      congr 1
      funext x
      congr 1
      exact ihb (ρ, x)

end Semantics

end Isotope.LambdaSSA.Translation.Frontend.Closed
