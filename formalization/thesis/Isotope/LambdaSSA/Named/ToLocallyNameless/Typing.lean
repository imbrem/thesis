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

/-- Lookup-level alignment is convenient for simultaneous label binders: it
avoids exposing the associativity casts used by `Scope.pushAll`. -/
def LookupAligned [DecidableEq ν] (Γ : LambdaIter.Ctx ν τ)
    (ρ : Scope ν n) (β : LocallyNameless.BoundCtx τ n)
    (Δ : LambdaIter.Ctx ν τ) : Prop :=
  ∀ {x A}, LambdaIter.Ctx.lookup Δ x = some A →
    match ρ.resolve x with
    | .inl i => β.get i = A
    | .inr y => LambdaIter.Ctx.lookup Γ y = some A

namespace LookupAligned

theorem of_aligned [DecidableEq ν] (h : Aligned (ν := ν) Γ ρ β Δ) :
    LookupAligned Γ ρ β Δ := by
  intro x A hx
  split <;> rename_i e
  · exact h.lookup_bound hx e
  · exact h.lookup_free hx e

theorem push [DecidableEq ν] (h : LookupAligned Γ ρ β Δ)
    (q : Named.Binder ν) (A : τ) :
    LookupAligned Γ (.push q ρ) (.snoc β A) (.snoc Δ q A) := by
  intro x B hx
  cases q with
  | none =>
      simp only [LambdaIter.Ctx.lookup] at hx
      rw [LambdaIter.Named.ToLocallyNameless.Scope.resolve_push_none]
      cases e : ρ.resolve x with
      | inl i => simpa [e] using h hx
      | inr y => simpa [e] using h hx
  | some y =>
      by_cases e : x = y
      · subst x
        have hAB : A = B := by simpa [LambdaIter.Ctx.lookup] using hx
        simpa [LambdaIter.LocallyNameless.BoundCtx.get, hAB]
      · have hx' : LambdaIter.Ctx.lookup Δ x = some B := by
          simpa [LambdaIter.Ctx.lookup, e] using hx
        rw [LambdaIter.Named.ToLocallyNameless.Scope.resolve_push_ne _ e]
        cases er : ρ.resolve x with
        | inl i => simpa [er] using h hx'
        | inr z => simpa [er] using h hx'

theorem cast [DecidableEq ν] {n m : Nat} {ρ : Scope ν n}
    {β : LocallyNameless.BoundCtx τ n} (h : LookupAligned Γ ρ β Δ)
    (e : n = m) (β' : LocallyNameless.BoundCtx τ m)
    (hβ : ∀ i, β'.get (Fin.cast e i) = β.get i) :
    LookupAligned Γ (Scope.cast e ρ) β' Δ := by
  intro x A hx
  rw [Scope.resolve_cast]
  cases er : ρ.resolve x with
  | inl i =>
      simp only [er, Sum.map_inl]
      exact (hβ i).trans (by simpa [er] using h hx)
  | inr y => simpa [er] using h hx

theorem pushAll [DecidableEq ν] {arity k : Nat} {ρ : Scope ν k}
    {β : LocallyNameless.BoundCtx τ k} (h : LookupAligned Γ ρ β Δ)
    (labels : Fin arity → Named.Binder ν) (R : Fin arity → τ) :
    LookupAligned Γ (Scope.pushAll labels ρ)
      (LocallyNameless.extendLabelCtx β R)
      (Named.extendLabels Δ arity labels R) := by
  induction arity with
  | zero =>
      apply LookupAligned.cast h (Nat.zero_add _).symm
      intro i
      simp only [LocallyNameless.extendLabelCtx,
        LambdaIter.LocallyNameless.BoundCtx.get_ofFin]
      have hi : Fin.cast (Nat.zero_add _).symm i = Fin.natAdd 0 i := by
        apply Fin.ext
        simp
      rw [hi, Fin.addCases_right]
  | succ arity ih =>
      let labels' : Fin arity → Named.Binder ν := fun i => labels i.succ
      let R' : Fin arity → τ := fun i => R i.succ
      have ht : LookupAligned Γ
          (.push (labels 0) (Scope.pushAll labels' ρ))
          (.snoc (LocallyNameless.extendLabelCtx β R') (R 0))
          (.snoc (Named.extendLabels Δ arity labels' R') (labels 0) (R 0)) :=
        LookupAligned.push (ih labels' R') (labels 0) (R 0)
      let e : arity + k + 1 = arity + 1 + k := by omega
      simp only [Scope.pushAll, Named.extendLabels, List.ofFn_succ]
      dsimp only [labels', R'] at ht ⊢
      apply LookupAligned.cast ht e
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [LocallyNameless.extendLabelCtx,
          LambdaIter.LocallyNameless.BoundCtx.get_ofFin,
          LambdaIter.LocallyNameless.BoundCtx.get]
        have hzero : Fin.cast e (0 : Fin (arity + k + 1)) =
            (0 : Fin (arity + 1 + k)) := by
          apply Fin.ext
          simp
        rw [hzero]
        have hzadd : (0 : Fin (arity + 1 + k)) =
            Fin.castAdd k (0 : Fin (arity + 1)) := by
          apply Fin.ext
          simp
        rw [hzadd, Fin.addCases_left]
        rfl
      · simp only [LocallyNameless.extendLabelCtx,
          LambdaIter.LocallyNameless.BoundCtx.get_ofFin,
          LambdaIter.LocallyNameless.BoundCtx.get]
        simp only [Fin.cases_succ]
        cases j using Fin.addCases with
        | left q =>
          have hq : Fin.cast e (Fin.castAdd k q).succ =
              Fin.castAdd k q.succ := by apply Fin.ext; simp
          rw [hq, Fin.addCases_left, Fin.addCases_left]
        | right q =>
          have hq : Fin.cast e (Fin.natAdd arity q).succ =
              Fin.natAdd (arity + 1) q := by
            apply Fin.ext
            change arity + q.val + 1 = arity + 1 + q.val
            omega
          rw [hq, Fin.addCases_right, Fin.addCases_right]

end LookupAligned

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

noncomputable def translateRegion_hasType [DecidableEq ν] [DecidableEq κ]
    [LambdaIter.TypeFormers τ] [LambdaIter.HasTy Φ τ]
    {n l : Nat} {ρ : Scope ν n} {ls : Scope κ l}
    {β : LocallyNameless.BoundCtx τ n}
    {δ : LocallyNameless.BoundCtx τ l}
    {Γ Δ : LambdaIter.Ctx ν τ} {K L : LambdaIter.Ctx κ τ}
    {r : Named.Region ν κ Φ} (hρ : Aligned Γ ρ β Δ)
    (hls : LookupAligned K ls δ L) (h : Named.Region.HasType Δ r L) :
    LocallyNameless.Region.HasType Φ Γ K β δ (translateRegion ρ ls r) := by
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

end Isotope.LambdaSSA.Named.ToLocallyNameless
