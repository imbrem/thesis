import Isotope.LambdaSSA.Named.ToLocallyNameless.Typing
import Isotope.LambdaSSA.Subtyping.Named.Typing
import Isotope.LambdaSSA.Subtyping.LocallyNameless.Typing

/-! # Proof-relevant named-to-locally-nameless SSA typing preservation -/

namespace Isotope.LambdaSSA.Subtyping.Named.ToLocallyNameless

open Isotope.LambdaSSA
open Isotope.LambdaSSA.Named.ToLocallyNameless

variable {ν κ τ Φ : Type*}

noncomputable def translateTm_hasType [DecidableEq ν]
    [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ] [LambdaIter.HasTy Φ τ]
    {n : Nat} {ρ : Scope ν n}
    {β : LambdaSSA.LocallyNameless.BoundCtx τ n} {Γ Δ : LambdaIter.Ctx ν τ}
    {t : LambdaSSA.Named.Tm ν Φ} {A : τ} (hρ : Aligned Γ ρ β Δ)
    (h : Subtyping.Named.Tm.HasType Δ t A) :
    Subtyping.LocallyNameless.Tm.HasType Φ Γ β (translateTm ρ t) A := by
  induction h generalizing n ρ β with
  | var hx =>
      unfold translateTm
      split <;> rename_i e
      · exact (hρ.lookup_bound hx e) ▸ .bv
      · exact .fv (hρ.lookup_free hx e)
  | op _ ih => exact .op (ih hρ)
  | let₁ _ _ iha ihb => exact .let₁ (iha hρ) (ihb (.push hρ))
  | pair _ _ iha ihb => exact .pair (iha hρ) (ihb hρ)
  | unit => exact .unit
  | let₂ _ _ iha ihb => exact .let₂ (iha hρ) (ihb (.push (.push hρ)))
  | inl _ ih => exact .inl (ih hρ)
  | inr _ ih => exact .inr (ih hρ)
  | case _ _ _ ihe ihl ihr => exact .case (ihe hρ) (ihl (.push hρ)) (ihr (.push hρ))
  | abort _ ih => exact .abort (ih hρ)
  | sub _ d ih => exact .sub (ih hρ) d

noncomputable def translateRegion_hasType [DecidableEq ν] [DecidableEq κ]
    [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ] [LambdaIter.HasTy Φ τ]
    {n l : Nat} {ρ : Scope ν n} {ls : Scope κ l}
    {β : LambdaSSA.LocallyNameless.BoundCtx τ n}
    {δ : LambdaSSA.LocallyNameless.BoundCtx τ l}
    {Γ Δ : LambdaIter.Ctx ν τ} {K L : LambdaIter.Ctx κ τ}
    {r : LambdaSSA.Named.Region ν κ Φ} (hρ : Aligned Γ ρ β Δ)
    (hls : LookupAligned K ls δ L) (h : Subtyping.Named.Region.HasType Δ r L) :
    Subtyping.LocallyNameless.Region.HasType Φ Γ K β δ
      (translateRegion ρ ls r) := by
  induction h generalizing n l ρ ls β δ with
  | br hlabel harg =>
      rename_i L' A' Γ' label arg
      unfold translateRegion
      cases er : ls.resolve label with
      | inl i =>
          have hl : δ.get i = A' := by simpa [er] using hls hlabel
          exact .br_bound (hl ▸ translateTm_hasType hρ harg)
      | inr y =>
          have hl : K.lookup y = some A' := by simpa [er] using hls hlabel
          exact .br_free hl (translateTm_hasType hρ harg)
  | case hdiscr hleft hright ihleft ihright =>
      exact .case (translateTm_hasType hρ hdiscr)
        (ihleft (.push hρ) hls) (ihright (.push hρ) hls)
  | let₁ hvalue hbody ihbody =>
      exact .let₁ (translateTm_hasType hρ hvalue) (ihbody (.push hρ) hls)
  | let₂ hvalue hbody ihbody =>
      exact .let₂ (translateTm_hasType hρ hvalue) (ihbody (.push (.push hρ)) hls)
  | cfg R hentry hblocks ihentry ihblocks =>
      exact .cfg R (ihentry hρ (hls.pushAll _ R))
        (fun i => ihblocks i (.push hρ) (hls.pushAll _ R))

end Isotope.LambdaSSA.Subtyping.Named.ToLocallyNameless
