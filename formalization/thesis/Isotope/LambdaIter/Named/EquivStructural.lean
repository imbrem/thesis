import Isotope.LambdaIter.Named.Equiv

/-! # Weakening of the named equational judgment -/

namespace Isotope.LambdaIter.Named

variable {ν τ Φ ε : Type*} [DecidableEq ν] [TypeFormers τ] [Subtyping τ]
  [HasTy Φ τ] [HasEff Φ ε]

theorem Eqv.strictWk (pureEff : ε) {Γ Δ : Ctx ν τ} {a b : Tm ν Φ} {A : τ}
    (w : Ctx.StrictWk Γ Δ) (hw : LookupStrictWk w)
    (h : Eqv pureEff Δ a b A) : Eqv pureEff Γ a b A := by
  induction h generalizing Γ with
  | refl h => exact .refl (h.strictWk w hw)
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
  | ax hax ha hb => exact .ax hax (ha.strictWk w hw) (hb.strictWk w hw)
  | alpha hab ha hb => exact .alpha hab (ha.strictWk w hw) (hb.strictWk w hw)
  | uniformity hp ha hh hcapture hcapture' _ ih =>
      exact .uniformity hp (ha.strictWk w hw)
        (hh.strictWk _ (hw.snoc _ _)) hcapture hcapture'
        (ih _ (hw.snoc _ _))
  | sub _ hAB ih => exact .sub (ih w hw) hAB

theorem Eqv.wk (pureEff : ε) {Γ Δ : Ctx ν τ} {a b : Tm ν Φ} {A : τ}
    (w : Ctx.Wk Γ Δ) (hw : LookupWk w) (h : Eqv pureEff Δ a b A) :
    Eqv pureEff Γ a b A := by
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
  | uniformity hp ha hh hcapture hcapture' _ ih =>
      exact .uniformity hp (ha.wk w hw)
        (hh.wk _ (hw.snoc _ _)) hcapture hcapture'
        (ih _ (hw.snoc _ _))
  | sub _ hAB ih => exact .sub (ih w hw) hAB

theorem Eqv.lookupEq (pureEff : ε) {Γ Δ : Ctx ν τ} {a b : Tm ν Φ} {A : τ}
    (h : Eqv pureEff Γ a b A) (heq : ∀ x, Γ.lookup x = Δ.lookup x) :
    Eqv pureEff Δ a b A := by
  induction h generalizing Δ with
  | refl h => exact .refl (h.lookupEq heq)
  | symm _ ih => exact .symm (ih heq)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ heq) (ih₂ heq)
  | op hf _ ih => exact .op hf (ih heq)
  | let₁ _ _ iha ihb =>
      exact .let₁ (iha heq) (ihb (lookup_snoc_eq heq _ _))
  | pair _ _ iha ihb => exact .pair (iha heq) (ihb heq)
  | let₂ _ _ ihe ihb =>
      exact .let₂ (ihe heq)
        (ihb (lookup_snoc_eq (lookup_snoc_eq heq _ _) _ _))
  | inl _ ih => exact .inl (ih heq)
  | inr _ ih => exact .inr (ih heq)
  | case _ _ _ ihe iha ihb =>
      exact .case (ihe heq)
        (iha (lookup_snoc_eq heq _ _))
        (ihb (lookup_snoc_eq heq _ _))
  | abort _ ih => exact .abort (ih heq)
  | iter _ _ iha ihb =>
      exact .iter (iha heq) (ihb (lookup_snoc_eq heq _ _))
  | ax hax ha hb => exact .ax hax (ha.lookupEq heq) (hb.lookupEq heq)
  | alpha hab ha hb => exact .alpha hab (ha.lookupEq heq) (hb.lookupEq heq)
  | uniformity hp ha hh hcapture hcapture' _ ih =>
      exact .uniformity hp (ha.lookupEq heq)
        (hh.lookupEq (lookup_snoc_eq heq _ _))
        hcapture hcapture'
        (ih (lookup_snoc_eq heq _ _))
  | sub _ hAB ih => exact .sub (ih heq) hAB

theorem Eqv.shadowEdit (pureEff : ε) {Γ Δ : Ctx ν τ}
    {a b : Tm ν Φ} {A : τ} (d : Ctx.ShadowEdit Γ Δ)
    (h : Eqv pureEff Γ a b A) : Eqv pureEff Δ a b A :=
  h.lookupEq pureEff d.lookup_eq

end Isotope.LambdaIter.Named
