import Isotope.LambdaIter.Subtyping.Semantics.Named
import Isotope.LambdaIter.Subtyping.Semantics.Denotation
import Isotope.LambdaIter.Subtyping.Named.ToLocallyNameless

/-! # Semantic agreement for named and locally nameless lambda-iter -/

namespace Isotope.LambdaIter.Subtyping.Semantics

open Isotope.Elgot Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Named.ToLocallyNameless

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m] [Iterate m]
variable [InstructionModel Φ τ ε m]

private theorem denote_bv_transport {Γ : Ctx ν τ} {n : Nat}
    {β : LocallyNameless.BoundCtx τ n} (i : Fin n) {A : τ}
    (e : β.get i = A) (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε)
        (e ▸ (LocallyNameless.HasType.bv (Φ := Φ) (Γ := Γ)
          (β := β) (ι := i))) γ ρ =
      (pure (e ▸ BoundDen.get ρ i) : m (TyDen A)) := by
  cases e
  simp [denote]

/-- A named environment and a split free/bound environment agree according
to the name-resolution scope.  `HEq` records the type equality supplied by
the proof-relevant typing translation without identifying its proof. -/
private def EnvAligned {Γ Δ : Ctx ν τ} (ρs : Scope ν n)
    (β : LocallyNameless.BoundCtx τ n)
    (γ : CtxDen Γ) (ρ : BoundDen β) (δ : CtxDen Δ) : Prop :=
  ∀ {x A} (hx : Δ.lookup x = some A),
    match hr : ρs.resolve x with
    | .inl i => HEq (CtxDen.lookup δ x hx) (BoundDen.get ρ i)
    | .inr y => ∃ hy : Γ.lookup y = some A,
        HEq (CtxDen.lookup δ x hx) (CtxDen.lookup γ y hy)

private theorem EnvAligned.nil (γ : CtxDen Γ) :
    EnvAligned (LambdaIter.Named.ToLocallyNameless.Scope.nil : Scope ν 0)
      LocallyNameless.BoundCtx.nil γ
      (show BoundDen (LocallyNameless.BoundCtx.nil : LocallyNameless.BoundCtx τ 0)
        from PUnit.unit) γ := by
  intro x A hx
  change ∃ hy : Γ.lookup x = some A,
    HEq (CtxDen.lookup γ x hx) (CtxDen.lookup γ x hy)
  refine ⟨hx, ?_⟩
  exact HEq.rfl

private theorem EnvAligned.push {Γ Δ : Ctx ν τ} {ρs : Scope ν n}
    {β : LocallyNameless.BoundCtx τ n} (hρ : Aligned Γ ρs β Δ)
    {γ : CtxDen Γ} {ρ : BoundDen β} {δ : CtxDen Δ}
    (hδ : EnvAligned ρs β γ ρ δ) (q : LambdaIter.Named.Binder ν)
    (A : τ) (a : TyDen A) :
    EnvAligned (Γ := Γ) (Δ := .snoc Δ q A) (.push q ρs) (.snoc β A)
      γ (ρ, a) (δ, a) := by
  intro x B hx
  cases q with
  | none =>
      have hx' : Δ.lookup x = some B := hx
      have ho := hδ hx
      cases hs : ρs.resolve x with
      | inl i =>
          rw [hs] at ho
          change HEq (CtxDen.lookup δ x hx') (BoundDen.get ρ i) at ho
          rw [LambdaIter.Named.ToLocallyNameless.Scope.resolve_push_none, hs]
          change HEq (CtxDen.lookup (δ, a) x hx)
            (BoundDen.get (show BoundDen (.snoc β A) from (ρ, a)) i.succ)
          exact ho
      | inr y =>
          rw [hs] at ho
          change ∃ hy : Γ.lookup y = some B,
            HEq (CtxDen.lookup δ x hx') (CtxDen.lookup γ y hy) at ho
          rw [LambdaIter.Named.ToLocallyNameless.Scope.resolve_push_none, hs]
          change ∃ hy : Γ.lookup y = some B,
            HEq (CtxDen.lookup (δ, a) x hx) (CtxDen.lookup γ y hy)
          exact ho
  | some y =>
      by_cases e : x = y
      · subst x
        have hAB : A = B := by simpa [Ctx.lookup] using hx
        subst B
        rw [LambdaIter.Named.ToLocallyNameless.Scope.resolve_push_self]
        simp [CtxDen.lookup, Ctx.lookup]
        exact HEq.rfl
      · have hx' : Δ.lookup x = some B := by simpa [Ctx.lookup, e] using hx
        have ho := hδ hx'
        cases hs : ρs.resolve x with
        | inl i =>
            rw [hs] at ho
            change HEq (CtxDen.lookup δ x hx') (BoundDen.get ρ i) at ho
            rw [LambdaIter.Named.ToLocallyNameless.Scope.resolve_push_ne _ e, hs]
            change HEq (CtxDen.lookup (δ, a) x hx)
              (BoundDen.get (show BoundDen (.snoc β A) from (ρ, a)) i.succ)
            simpa [CtxDen.lookup, Ctx.lookup, e] using ho
        | inr z =>
            rw [hs] at ho
            change ∃ hz : Γ.lookup z = some B,
              HEq (CtxDen.lookup δ x hx') (CtxDen.lookup γ z hz) at ho
            rw [LambdaIter.Named.ToLocallyNameless.Scope.resolve_push_ne _ e, hs]
            change ∃ hz : Γ.lookup z = some B,
              HEq (CtxDen.lookup (δ, a) x hx) (CtxDen.lookup γ z hz)
            rcases ho with ⟨hz, ho⟩
            exact ⟨hz, by simpa [CtxDen.lookup, Ctx.lookup, e] using ho⟩

private theorem denote_translateVarAt {Γ Δ : Ctx ν τ} {ρs : Scope ν n}
    {β : LocallyNameless.BoundCtx τ n} (hρ : Aligned Γ ρs β Δ)
    (x : ν) {A : τ} (hx : Δ.lookup x = some A)
    (o : Option (Fin n)) (hl : ρs.lookup x = o)
    (γ : CtxDen Γ) (ρ : BoundDen β) (δ : CtxDen Δ)
    (hδ : EnvAligned ρs β γ ρ δ) :
    denote (m := m) (ε := ε)
      (translateVarAt (Φ := Φ) hρ x hx o hl) γ ρ =
      pure (CtxDen.lookup δ x hx) := by
  cases o with
  | some i =>
      have ht := hρ hx
      have hv := hδ hx
      unfold LambdaIter.Named.ToLocallyNameless.Scope.resolve at ht hv
      rw [hl] at ht hv
      simp only at ht hv
      subst A
      simp [translateVarAt, denote]
      exact congrArg (fun z => (pure z : m _)) (eq_of_heq hv).symm
  | none =>
      have hv := hδ hx
      unfold LambdaIter.Named.ToLocallyNameless.Scope.resolve at hv
      rw [hl] at hv
      simp only at hv
      rcases hv with ⟨hy, hv⟩
      simp [translateVarAt, denote]
      exact congrArg (fun z => (pure z : m _)) (eq_of_heq hv).symm

private theorem denote_translateVar {Γ Δ : Ctx ν τ} {ρs : Scope ν n}
    {β : LocallyNameless.BoundCtx τ n} (hρ : Aligned Γ ρs β Δ)
    (x : ν) {A : τ} (hx : Δ.lookup x = some A)
    (γ : CtxDen Γ) (ρ : BoundDen β) (δ : CtxDen Δ)
    (hδ : EnvAligned ρs β γ ρ δ) :
    denote (m := m) (ε := ε) (translateVar (Φ := Φ) hρ x hx) γ ρ =
      pure (CtxDen.lookup δ x hx) := by
  unfold translateVar
  exact denote_translateVarAt hρ x hx _ rfl γ ρ δ hδ

/-- Named denotation agrees with typed locally nameless translation for every
aligned scope and environment.  In particular the `.sub` branch reuses the
same witness on both sides. -/
theorem denote_translateHasType {Γ Δ : Ctx ν τ} {ρs : Scope ν n}
    {β : LocallyNameless.BoundCtx τ n} (hρ : Aligned Γ ρs β Δ)
    {t : LambdaIter.Named.Tm ν Φ} {A : τ}
    (h : LambdaIter.Subtyping.Named.HasType Δ t A)
    (γ : CtxDen Γ) (ρ : BoundDen β) (δ : CtxDen Δ)
    (hδ : EnvAligned ρs β γ ρ δ) :
    denote (m := m) (ε := ε) (translateHasType hρ h) γ ρ =
      Named.denote (m := m) (ε := ε) h δ := by
  fun_induction translateHasType hρ h
  all_goals
    simp only [denote, Named.denote]
  case case1 =>
    rename_i Δ₀ n₀ scope₀ β₀ halign A₀ x₀ hx₀
    exact denote_translateVar (Φ := Φ) (m := m) (ε := ε)
      halign x₀ hx₀ γ ρ δ hδ
  case case2 =>
    rename_i Δ₀ n₀ scope₀ β₀ halign B₀ f₀ A₀ a₀ hf ha ih
    have ealign : (hρ : Aligned Γ scope₀ β₀ Δ₀) =
        (fun {x} {A} hx => halign hx) :=
      Subsingleton.elim _ _
    cases ealign
    simp [denote]
    unfold denote
    unfold denote
    rw [ih hρ ρ δ hδ]
    simp [LawfulMonad.bind_assoc]
  case case3 =>
    rename_i Δ₀ n₀ scope₀ β₀ halign B₀ a₀ A₀ x₀ b₀ ha hb iha ihb
    have ealign : (hρ : Aligned Γ scope₀ β₀ Δ₀) =
        (fun {x} {A} hx => halign hx) := Subsingleton.elim _ _
    cases ealign
    unfold denote
    rw [iha hρ ρ δ hδ]
    apply bind_congr
    intro a
    exact ihb (Aligned.push hρ x₀ A₀) (ρ, a) (δ, a)
      (EnvAligned.push hρ hδ x₀ A₀ a)
  case case4 =>
    rename_i Δ₀ n₀ scope₀ β₀ halign
    have ealign : (hρ : Aligned Γ scope₀ β₀ Δ₀) =
        (fun {x} {A} hx => halign hx) := Subsingleton.elim _ _
    cases ealign
    unfold denote
    rfl
  case case5 =>
    rename_i Δ₀ n₀ scope₀ β₀ halign a₀ A₀ b₀ B₀ ha hb iha ihb
    have ealign : (hρ : Aligned Γ scope₀ β₀ Δ₀) =
        (fun {x} {A} hx => halign hx) := Subsingleton.elim _ _
    cases ealign
    unfold denote
    rw [iha hρ ρ δ hδ, ihb hρ ρ δ hδ]
    rfl
  case case6 =>
    rename_i Δ₀ n₀ scope₀ β₀ halign C₀ a₀ A₀ B₀ x₀ y₀ c₀ ha hc iha ihc
    have ealign : (hρ : Aligned Γ scope₀ β₀ Δ₀) =
        (fun {x} {A} hx => halign hx) := Subsingleton.elim _ _
    cases ealign
    unfold denote
    rw [← iha hρ ρ δ hδ]
    apply bind_congr
    intro ab
    exact ihc (Aligned.push (Aligned.push hρ x₀ A₀) y₀ B₀) _ _
      (EnvAligned.push (Aligned.push hρ x₀ A₀)
        (EnvAligned.push hρ hδ x₀ A₀ _) y₀ B₀ _)
  case case7 =>
    rename_i Δ₀ n₀ scope₀ β₀ halign a₀ A₀ B₀ ha ih
    have ealign : (hρ : Aligned Γ scope₀ β₀ Δ₀) =
        (fun {x} {A} hx => halign hx) := Subsingleton.elim _ _
    cases ealign
    unfold denote
    rw [ih hρ ρ δ hδ]
    rfl
  case case8 =>
    rename_i Δ₀ n₀ scope₀ β₀ halign b₀ B₀ A₀ hb ih
    have ealign : (hρ : Aligned Γ scope₀ β₀ Δ₀) =
        (fun {x} {A} hx => halign hx) := Subsingleton.elim _ _
    cases ealign
    unfold denote
    rw [ih hρ ρ δ hδ]
    rfl
  case case9 =>
    rename_i Δ₀ n₀ scope₀ β₀ halign C₀ e₀ A₀ B₀ x₀ a₀ y₀ b₀ he hl hr ihe ihl ihr
    have ealign : (hρ : Aligned Γ scope₀ β₀ Δ₀) =
        (fun {x} {A} hx => halign hx) := Subsingleton.elim _ _
    cases ealign
    unfold denote
    rw [← ihe hρ ρ δ hδ]
    apply bind_congr
    intro e
    cases TypeModel.coprodEquiv A₀ B₀ e with
    | inl a =>
        exact ihl (Aligned.push hρ x₀ A₀) (ρ, a) (δ, a)
          (EnvAligned.push hρ hδ x₀ A₀ a)
    | inr b =>
        exact ihr (Aligned.push hρ y₀ B₀) (ρ, b) (δ, b)
          (EnvAligned.push hρ hδ y₀ B₀ b)
  case case10 =>
    rename_i Δ₀ n₀ scope₀ β₀ halign A₀ a₀ ha ih
    have ealign : (hρ : Aligned Γ scope₀ β₀ Δ₀) =
        (fun {x} {A} hx => halign hx) := Subsingleton.elim _ _
    cases ealign
    unfold denote
    rw [← ih hρ ρ δ hδ]
    rfl
  case case11 =>
    rename_i Δ₀ n₀ scope₀ β₀ halign B₀ a₀ A₀ x₀ b₀ ha hb iha ihb
    have ealign : (hρ : Aligned Γ scope₀ β₀ Δ₀) =
        (fun {x} {A} hx => halign hx) := Subsingleton.elim _ _
    cases ealign
    unfold denote
    rw [iha hρ ρ δ hδ]
    apply bind_congr
    intro a
    congr 1
    funext x
    rw [← ihb (Aligned.push hρ x₀ A₀) (ρ, x) (δ, x)
      (EnvAligned.push hρ hδ x₀ A₀ x)]
    rfl
  case case12 =>
    rename_i Δ₀ n₀ scope₀ β₀ halign B₀ t₀ A₀ ha hAB ih
    have ealign : (hρ : Aligned Γ scope₀ β₀ Δ₀) =
        (fun {x} {A} hx => halign hx) := Subsingleton.elim _ _
    cases ealign
    rw [← ih hρ ρ δ hδ]

/-- Closed named terms and their proof-relevant locally nameless translations
have identical monadic denotations. -/
theorem denote_translateHasTypeClosed
    {t : LambdaIter.Named.Tm ν Φ} {A : τ}
    (h : LambdaIter.Subtyping.Named.HasType (Ctx.nil : Ctx ν τ) t A) :
    denote (m := m) (ε := ε) (translateHasTypeClosed h) PUnit.unit PUnit.unit =
      Named.denote (m := m) (ε := ε) h PUnit.unit := by
  exact denote_translateHasType
    (Γ := (Ctx.nil : Ctx ν τ)) (Δ := (Ctx.nil : Ctx ν τ))
    (ρs := (LambdaIter.Named.ToLocallyNameless.Scope.nil : Scope ν 0))
    (β := (LocallyNameless.BoundCtx.nil : LocallyNameless.BoundCtx τ 0))
    (Aligned.nil (ν := ν) (Ctx.nil : Ctx ν τ)) h
    PUnit.unit PUnit.unit PUnit.unit
    (EnvAligned.nil (Γ := (Ctx.nil : Ctx ν τ)) PUnit.unit)

end Isotope.LambdaIter.Subtyping.Semantics
