import Isotope.LambdaIter.Named.Equiv

/-! # Weakening of the named equational judgment -/

namespace Isotope.LambdaIter.Named

variable {ν τ : Type*} [DecidableEq ν] [TypeFormers τ] [Subtyping τ]
  {S : Signature τ}

theorem Eqv.wk {Γ Δ : Ctx ν τ} {a b : Tm ν S} {A : τ}
    (w : Ctx.Wk Γ Δ) (hw : LookupWk w) (h : Eqv S Δ a b A) :
    Eqv S Γ a b A := by
  induction h generalizing Γ with
  | refl h => exact .refl (h.wk w hw)
  | symm _ ih => exact .symm (ih w hw)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ w hw) (ih₂ w hw)
  | op hf _ ih => exact .op hf (ih w hw)
  | let₁ _ _ iha ihb => exact .let₁ (iha w hw) (ihb _ (hw.snoc _ _))
  | pair _ _ iha ihb => exact .pair (iha w hw) (ihb w hw)
  | let₂ _ _ ihe ihc => exact .let₂ (ihe w hw) (ihc _ ((hw.snoc _ _).snoc _ _))
  | inl _ ih => exact .inl (ih w hw)
  | inr _ ih => exact .inr (ih w hw)
  | case _ _ _ ihe iha ihb =>
      exact .case (ihe w hw) (iha _ (hw.snoc _ _)) (ihb _ (hw.snoc _ _))
  | abort _ ih => exact .abort (ih w hw)
  | iter _ _ iha ihb => exact .iter (iha w hw) (ihb _ (hw.snoc _ _))
  | ax hax ha hb => exact .ax hax (ha.wk w hw) (hb.wk w hw)
  | alpha hab ha hb => exact .alpha hab (ha.wk w hw) (hb.wk w hw)
  | uniformity hp ha hh _ ih =>
      exact .uniformity hp (ha.wk w hw) (hh.wk _ (hw.snoc _ _)) (ih _ (hw.snoc _ _))
  | sub _ hAB ih => exact .sub (ih w hw) hAB

theorem Eqv.subtypeWk {Γ Δ : Ctx ν τ} {a b : Tm ν S} {A : τ}
    (w : Ctx.SubtypeWk Γ Δ) (hw : LookupSubtypeWk w) (h : Eqv S Δ a b A) :
    Eqv S Γ a b A := by
  induction h generalizing Γ with
  | refl h => exact .refl (h.subtypeWk w hw)
  | symm _ ih => exact .symm (ih w hw)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ w hw) (ih₂ w hw)
  | op hf _ ih => exact .op hf (ih w hw)
  | let₁ _ _ iha ihb => exact .let₁ (iha w hw) (ihb _ (hw.snoc _ _))
  | pair _ _ iha ihb => exact .pair (iha w hw) (ihb w hw)
  | let₂ _ _ ihe ihc => exact .let₂ (ihe w hw) (ihc _ ((hw.snoc _ _).snoc _ _))
  | inl _ ih => exact .inl (ih w hw)
  | inr _ ih => exact .inr (ih w hw)
  | case _ _ _ ihe iha ihb =>
      exact .case (ihe w hw) (iha _ (hw.snoc _ _)) (ihb _ (hw.snoc _ _))
  | abort _ ih => exact .abort (ih w hw)
  | iter _ _ iha ihb => exact .iter (iha w hw) (ihb _ (hw.snoc _ _))
  | ax hax ha hb => exact .ax hax (ha.subtypeWk w hw) (hb.subtypeWk w hw)
  | alpha hab ha hb => exact .alpha hab (ha.subtypeWk w hw) (hb.subtypeWk w hw)
  | uniformity hp ha hh _ ih =>
      exact .uniformity hp (ha.subtypeWk w hw)
        (hh.subtypeWk _ (hw.snoc _ _)) (ih _ (hw.snoc _ _))
  | sub _ hAB ih => exact .sub (ih w hw) hAB

end Isotope.LambdaIter.Named
