import Isotope.LambdaSSA.Named.ToLocallyNameless

/-! # Typing preservation for named-to-locally-nameless lambda-SSA -/

namespace Isotope.LambdaSSA.Named.ToLocallyNameless

variable {ν κ τ Φ : Type*}

/-- A scope and bound context describe the suffix added to a fixed free
context. Anonymous binders occupy a bound slot without becoming resolvable. -/
inductive Aligned (Γ : LambdaIter.Ctx ν τ) : {n : Nat} → Scope ν n →
    LocallyNameless.BoundCtx τ n → LambdaIter.Ctx ν τ → Prop where
  | nil : Aligned Γ .nil .nil Γ
  | push : Aligned Γ ρ β Δ →
      Aligned Γ (.push x ρ) (.snoc β A) (.snoc Δ x A)

namespace Aligned

theorem lookup_bound [DecidableEq ν] (h : Aligned (ν := ν) Γ ρ β Δ)
    (hx : LambdaIter.Ctx.lookup Δ x = some A) (hr : ρ.resolve x = .inl i) :
    β.get i = A := by
  induction h with
  | nil => simp at hr
  | @push n ρ β Δ q B h ih =>
      cases q with
      | none =>
          simp only [LambdaIter.Ctx.lookup] at hx
          simp only [LambdaIter.Named.ToLocallyNameless.Scope.resolve_push_none] at hr
          cases e : ρ.resolve x with
          | inl j =>
              have hj : Fin.succ j = i := by simpa [e] using hr
              subst i
              exact ih hx e
          | inr y => simp [e] at hr
      | some y =>
          by_cases e : x = y
          · subst x
            have hBA : B = A := by simpa [LambdaIter.Ctx.lookup] using hx
            have hi : i = 0 := by simpa using hr.symm
            subst i
            exact hBA
          · have hx' : LambdaIter.Ctx.lookup Δ x = some A := by
              simpa [LambdaIter.Ctx.lookup, e] using hx
            rw [LambdaIter.Named.ToLocallyNameless.Scope.resolve_push_ne _ e] at hr
            cases er : ρ.resolve x with
            | inl j =>
                have hj : Fin.succ j = i := by simpa [er] using hr
                subst i
                exact ih hx' er
            | inr z => simp [er] at hr

theorem lookup_free [DecidableEq ν] (h : Aligned (ν := ν) Γ ρ β Δ)
    (hx : LambdaIter.Ctx.lookup Δ x = some A) (hr : ρ.resolve x = .inr y) :
    LambdaIter.Ctx.lookup Γ y = some A := by
  induction h with
  | nil =>
      have hxy : x = y := by simpa using hr
      subst y
      exact hx
  | @push n ρ β Δ q B h ih =>
      cases q with
      | none =>
          simp only [LambdaIter.Ctx.lookup] at hx
          simp only [LambdaIter.Named.ToLocallyNameless.Scope.resolve_push_none] at hr
          cases er : ρ.resolve x with
          | inl i => simp [er] at hr
          | inr z =>
              have hz : z = y := by simpa [er] using hr
              subst y
              exact ih hx er
      | some z =>
          by_cases e : x = z
          · subst x; simp at hr
          · have hx' : LambdaIter.Ctx.lookup Δ x = some A := by
              simpa [LambdaIter.Ctx.lookup, e] using hx
            rw [LambdaIter.Named.ToLocallyNameless.Scope.resolve_push_ne _ e] at hr
            cases er : ρ.resolve x with
            | inl i => simp [er] at hr
            | inr w =>
                have hw : w = y := by simpa [er] using hr
                subst y
                exact ih hx' er

end Aligned

noncomputable def translateTm_hasType [DecidableEq ν] [LambdaIter.TypeFormers τ]
    [LambdaIter.HasTy Φ τ] {n : Nat} {ρ : Scope ν n}
    {β : LocallyNameless.BoundCtx τ n} {Γ Δ : LambdaIter.Ctx ν τ}
    {t : Named.Tm ν Φ} {A : τ} (hρ : Aligned Γ ρ β Δ)
    (h : Named.Tm.HasType Δ t A) :
    LocallyNameless.Tm.HasType Φ Γ β (translateTm ρ t) A := by
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

end Isotope.LambdaSSA.Named.ToLocallyNameless
