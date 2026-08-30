import Isotope.LambdaIter.Semantics.Purity
import Isotope.LambdaIter.LocallyNameless.TypingSubst

/-! # Semantics of typed renaming and substitution -/

namespace Isotope.LambdaIter.Semantics

open Isotope.LambdaIter.LocallyNameless

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m] [Elgot.Iterate m]
variable [InstructionModel Φ τ ε m]

namespace BoundDen

/-- Reconstruct an environment from its newest-first dependent `Fin` view. -/
def ofFun : {n : Nat} → (β : BoundCtx τ n) →
    ((i : Fin n) → TyDen (β.get i)) → BoundDen β
  | 0, .nil, _ => PUnit.unit
  | _ + 1, .snoc β A, f =>
      (ofFun β (fun i => f i.succ), f 0)

@[simp] theorem get_ofFun {n : Nat} (β : BoundCtx τ n)
    (f : (i : Fin n) → TyDen (β.get i)) (i : Fin n) :
    get (ofFun β f) i = f i := by
  induction β with
  | nil => exact Fin.elim0 i
  | snoc β A ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact ih (fun k => f k.succ) j

/-- Pull a target environment back along a type-preserving index renaming. -/
def pull {n k : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ k}
    (r : TypedRenaming β β') (ρ : BoundDen β') : BoundDen β :=
  ofFun β fun i => r.typed i ▸ get ρ (r.toFun i)

@[simp] theorem get_pull {n k : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ k}
    (r : TypedRenaming β β') (ρ : BoundDen β') (i : Fin n) :
    get (pull r ρ) i = r.typed i ▸ get ρ (r.toFun i) :=
  get_ofFun β _ i

@[simp] theorem pull_up {n k : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ k}
    (r : TypedRenaming β β') (ρ : BoundDen β') (A : τ) (a : TyDen A) :
    pull (r.up A) (ρ, a) = (pull r ρ, a) := by
  apply Prod.ext
  · apply congrArg (ofFun β)
    funext i
    rfl
  · rfl

@[simp] theorem pull_succ {n : Nat} (β : BoundCtx τ n) (A : τ)
    (ρ : BoundDen β) (a : TyDen A) :
    pull (TypedRenaming.succ β A) (ρ, a) = ρ := by
  induction β with
  | nil => rfl
  | snoc β B ih =>
      apply Prod.ext
      · change pull (TypedRenaming.succ β A) (ρ.1, a) = ρ.1
        exact ih ρ.1
      · rfl

@[simp] theorem pull_underBinder {n : Nat} (β : BoundCtx τ n) (X Y : τ)
    (ρ : BoundDen β) (x : TyDen X) (y : TyDen Y) :
    pull (TypedRenaming.underBinder β X Y) ((ρ, x), y) = (ρ, y) := by
  apply Prod.ext
  · exact pull_succ β X ρ x
  · rfl

@[simp] theorem pull_underTwoBinders {n : Nat} (β : BoundCtx τ n) (X Y Z : τ)
    (ρ : BoundDen β) (x : TyDen X) (y : TyDen Y) (z : TyDen Z) :
    pull (TypedRenaming.underTwoBinders β X Y Z) (((ρ, x), y), z) = ((ρ, y), z) := by
  apply Prod.ext
  · apply Prod.ext
    · exact pull_succ β X ρ x
    · rfl
  · rfl

end BoundDen

private theorem denote_bv_transport {Γ : Ctx ν τ} {n : Nat}
    {β : BoundCtx τ n} (i : Fin n) {A : τ} (e : β.get i = A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε)
        (e ▸ (HasType.bv (Φ := Φ) (Γ := Γ) (β := β) (ι := i))) γ ρ =
      (pure (e ▸ BoundDen.get ρ i) : m (TyDen A)) := by
  cases e
  simp [denote]

@[simp] theorem denote_newest {Γ : Ctx ν τ} {n : Nat}
    {β : BoundCtx τ n} {A : τ} (γ : CtxDen Γ) (ρ : BoundDen β)
    (a : TyDen A) :
    denote (m := m) (ε := ε)
      (HasType.newest (Φ := Φ) (Γ := Γ) (β := β) (A := A)) γ (ρ, a) = pure a := by
  unfold HasType.newest
  exact denote_bv_transport (m := m) (ε := ε) (β := .snoc β A)
    (i := (0 : Fin (n + 1)))
    (e := rfl) γ (ρ, a)

@[simp] theorem denote_previous {Γ : Ctx ν τ} {n : Nat}
    {β : BoundCtx τ n} {A B : τ} (γ : CtxDen Γ) (ρ : BoundDen β)
    (a : TyDen A) (b : TyDen B) :
    denote (m := m) (ε := ε)
      (HasType.previous (Φ := Φ) (Γ := Γ) (β := β) (A := A) (B := B))
        γ ((ρ, a), b) = pure a := by
  unfold HasType.previous
  exact denote_bv_transport (m := m) (ε := ε) (β := .snoc (.snoc β A) B)
    (i := (1 : Fin (n + 2)))
    (e := rfl) γ ((ρ, a), b)

/-- Denotation is natural under every type-preserving bound-variable
renaming. -/
theorem denote_rename {Γ : Ctx ν τ} {n k : Nat}
    {β : BoundCtx τ n} {β' : BoundCtx τ k} {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β t A) (r : TypedRenaming β β')
    (γ : CtxDen Γ) (ρ : BoundDen β') :
    denote (m := m) (ε := ε) (h.rename r) γ ρ =
      denote (m := m) (ε := ε) h γ (BoundDen.pull r ρ) := by
  induction h generalizing k β' with
  | fv h =>
      simp only [HasType.rename]
      unfold denote
      change (pure (CtxDen.lookup γ _ h) : m _) = pure (CtxDen.lookup γ _ h)
      rfl
  | bv =>
      simp only [HasType.rename]
      refine (denote_bv_transport (m := m) (ε := ε)
        (i := r.toFun _) (e := r.typed _) γ ρ).trans ?_
      unfold denote
      congr 1
      exact (BoundDen.get_pull r ρ _).symm
  | op h ih =>
      simp only [HasType.rename]
      unfold denote
      change (denote (m := m) (ε := ε) (h.rename r) γ ρ >>= _) =
        (denote (m := m) (ε := ε) h γ (BoundDen.pull r ρ) >>= _)
      rw [ih]
  | let₁ ha hb iha ihb =>
      simp only [HasType.rename]
      unfold denote
      change (denote (m := m) (ε := ε) (ha.rename r) γ ρ >>= fun a =>
        denote (m := m) (ε := ε) (hb.rename (r.up _)) γ (ρ, a)) = _
      rw [iha]
      apply bind_congr
      intro a
      rw [ihb, BoundDen.pull_up]
  | unit =>
      simp only [HasType.rename]
      unfold denote
      change (pure (TypeModel.unitEquiv.symm ()) : m _) = pure _
      rfl
  | pair ha hb iha ihb =>
      simp only [HasType.rename]
      unfold denote
      change (denote (m := m) (ε := ε) (ha.rename r) γ ρ >>= fun a =>
        denote (m := m) (ε := ε) (hb.rename r) γ ρ >>= fun b => pure _) = _
      rw [iha, ihb]
  | let₂ ha hc iha ihc =>
      simp only [HasType.rename]
      unfold denote
      change (denote (m := m) (ε := ε) (ha.rename r) γ ρ >>= fun ab =>
        denote (m := m) (ε := ε) (hc.rename ((r.up _).up _)) γ
          ((ρ, (TypeModel.tensorEquiv _ _ ab).1),
            (TypeModel.tensorEquiv _ _ ab).2)) = _
      rw [iha]
      apply bind_congr
      intro ab
      rw [ihc, BoundDen.pull_up, BoundDen.pull_up]
  | inl h ih =>
      simp only [HasType.rename]
      unfold denote
      change (denote (m := m) (ε := ε) (h.rename r) γ ρ >>= fun a => pure _) = _
      rw [ih]
  | inr h ih =>
      simp only [HasType.rename]
      unfold denote
      change (denote (m := m) (ε := ε) (h.rename r) γ ρ >>= fun a => pure _) = _
      rw [ih]
  | abort h ih =>
      simp only [HasType.rename]
      unfold denote
      change (denote (m := m) (ε := ε) (h.rename r) γ ρ >>= fun z =>
        (TypeModel.emptyEquiv z).elim) = _
      rw [ih]
  | case he hl hr ihe ihl ihr =>
      simp only [HasType.rename]
      unfold denote
      change (denote (m := m) (ε := ε) (he.rename r) γ ρ >>= fun e =>
        match TypeModel.coprodEquiv _ _ e with
        | .inl a => denote (m := m) (ε := ε) (hl.rename (r.up _)) γ (ρ, a)
        | .inr b => denote (m := m) (ε := ε) (hr.rename (r.up _)) γ (ρ, b)) = _
      rw [ihe]
      apply bind_congr
      intro e
      cases hs : TypeModel.coprodEquiv _ _ e with
      | inl a => simp only; rw [ihl, BoundDen.pull_up]
      | inr b => simp only; rw [ihr, BoundDen.pull_up]
  | iter ha hb iha ihb =>
      simp only [HasType.rename]
      unfold denote
      change (denote (m := m) (ε := ε) (ha.rename r) γ ρ >>= Elgot.iter fun a =>
        denote (m := m) (ε := ε) (hb.rename (r.up _)) γ (ρ, a) >>= fun s =>
          pure (TypeModel.coprodEquiv _ _ s)) = _
      rw [iha]
      apply bind_congr
      intro a
      congr 1
      funext x
      rw [ihb, BoundDen.pull_up]
  | sub h d ih =>
      simp only [HasType.rename]
      unfold denote
      change (denote (m := m) (ε := ε) (h.rename r) γ ρ >>= fun a =>
        pure (coeSub d a)) = _
      rw [ih]

/-- A typed substitution denotes precisely the values stored in its source
environment.  This purity premise is necessary: unrestricted substitution
would duplicate arbitrary effects at repeated variable occurrences. -/
def SubstDen {Γ : Ctx ν τ} {n k : Nat}
    {β : BoundCtx τ n} {β' : BoundCtx τ k} {σ : Fin n → Tm ν Φ k}
    (s : TypedSubst (Γ := Γ) β β' σ) (γ : CtxDen Γ)
    (ρ' : BoundDen β') (ρ : BoundDen β) : Prop :=
  ∀ i, denote (m := m) (ε := ε) (s i) γ ρ' = pure (BoundDen.get ρ i)

theorem SubstDen.up {Γ : Ctx ν τ} {n k : Nat}
    {β : BoundCtx τ n} {β' : BoundCtx τ k} {σ : Fin n → Tm ν Φ k}
    {s : TypedSubst (Γ := Γ) β β' σ} {γ : CtxDen Γ}
    {ρ' : BoundDen β'} {ρ : BoundDen β}
    (hs : SubstDen (m := m) (ε := ε) s γ ρ' ρ)
    (A : τ) (a : TyDen A) :
    SubstDen (m := m) (ε := ε) (s.up A) γ (ρ', a) (ρ, a) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [TypedSubst.up, Fin.cases_zero]
    unfold denote
    change (pure a : m _) = pure a
    rfl
  · simp only [TypedSubst.up, Fin.cases_succ, HasType.lift]
    change denote (m := m) (ε := ε)
      (HasType.rename (TypedRenaming.succ β' A) (s j)) γ (ρ', a) =
        pure (BoundDen.get ρ j)
    have hr := denote_rename (m := m) (ε := ε) (s j)
      (TypedRenaming.succ β' A) γ (ρ', a)
    calc
      _ = denote (m := m) (ε := ε) (s j) γ
          (BoundDen.pull (TypedRenaming.succ β' A) (ρ', a)) := hr
      _ = denote (m := m) (ε := ε) (s j) γ ρ' := by
        rw [BoundDen.pull_succ]
      _ = pure (BoundDen.get ρ j) := hs j

/-- Semantic substitution for value-respecting simultaneous substitutions. -/
theorem denote_bsubst {Γ : Ctx ν τ} {n k : Nat}
    {β : BoundCtx τ n} {β' : BoundCtx τ k} {σ : Fin n → Tm ν Φ k}
    (s : TypedSubst (Γ := Γ) β β' σ) {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β t A) (γ : CtxDen Γ)
    (ρ' : BoundDen β') (ρ : BoundDen β)
    (hs : SubstDen (m := m) (ε := ε) s γ ρ' ρ) :
    denote (m := m) (ε := ε) (h.bsubst s) γ ρ' =
      denote (m := m) (ε := ε) h γ ρ := by
  induction h generalizing k β' with
  | fv h => simp only [HasType.bsubst]; unfold denote; rfl
  | bv => simpa only [HasType.bsubst, denote] using hs _
  | op h ih => simp only [HasType.bsubst]; unfold denote; rw [ih s ρ' ρ hs]
  | let₁ ha hb iha ihb =>
      simp only [HasType.bsubst]; unfold denote
      rw [iha s ρ' ρ hs]
      apply bind_congr
      intro a
      exact ihb (s := s.up _) (ρ' := (ρ', a)) (ρ := (ρ, a)) (hs.up _ a)
  | unit => simp only [HasType.bsubst]; unfold denote; rfl
  | pair ha hb iha ihb =>
      simp only [HasType.bsubst]; unfold denote
      rw [iha s ρ' ρ hs, ihb s ρ' ρ hs]
  | let₂ ha hc iha ihc =>
      simp only [HasType.bsubst]; unfold denote
      rw [iha s ρ' ρ hs]
      apply bind_congr
      intro ab
      exact ihc (s := (s.up _).up _)
        (ρ' := ((ρ', (TypeModel.tensorEquiv _ _ ab).1),
          (TypeModel.tensorEquiv _ _ ab).2))
        (ρ := ((ρ, (TypeModel.tensorEquiv _ _ ab).1),
          (TypeModel.tensorEquiv _ _ ab).2))
        ((hs.up _ _).up _ _)
  | inl h ih => simp only [HasType.bsubst]; unfold denote; rw [ih s ρ' ρ hs]
  | inr h ih => simp only [HasType.bsubst]; unfold denote; rw [ih s ρ' ρ hs]
  | abort h ih => simp only [HasType.bsubst]; unfold denote; rw [ih s ρ' ρ hs]
  | case he hl hr ihe ihl ihr =>
      simp only [HasType.bsubst]; unfold denote
      rw [ihe s ρ' ρ hs]
      apply bind_congr
      intro e
      cases TypeModel.coprodEquiv _ _ e with
      | inl a => exact ihl (s := s.up _) (ρ' := (ρ', a)) (ρ := (ρ, a)) (hs.up _ a)
      | inr b => exact ihr (s := s.up _) (ρ' := (ρ', b)) (ρ := (ρ, b)) (hs.up _ b)
  | iter ha hb iha ihb =>
      simp only [HasType.bsubst]; unfold denote
      rw [iha s ρ' ρ hs]
      apply bind_congr
      intro a
      congr 1
      funext x
      exact congrArg (fun z => z >>= fun s => pure (TypeModel.coprodEquiv _ _ s))
        (ihb (s.up _) (ρ', x) (ρ, x) (hs.up _ x))
  | sub h d ih =>
      simp only [HasType.bsubst]; unfold denote; rw [ih s ρ' ρ hs]

/-- Opening a binder by a pure computation agrees with extending its
semantic environment by the resulting value. -/
theorem denote_instantiate {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (hb : HasType Φ Γ (.snoc β A) b B) (ha : HasType Φ Γ β a A)
    (γ : CtxDen Γ) (ρ : BoundDen β) (x : TyDen A)
    (hx : denote (m := m) (ε := ε) ha γ ρ = pure x) :
    denote (m := m) (ε := ε) (hb.instantiate ha) γ ρ =
      denote (m := m) (ε := ε) hb γ (ρ, x) := by
  unfold HasType.instantiate
  let ss : TypedSubst (Γ := Γ) (.snoc β A) β
      (Fin.cases a fun i => .bv i) := Fin.cases ha fun _ => .bv
  change denote (m := m) (ε := ε) (hb.bsubst ss) γ ρ = _
  apply denote_bsubst ss hb γ ρ (ρ, x)
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hx
  · change denote (m := m) (ε := ε) (ss (Fin.succ j)) γ ρ =
      pure (BoundDen.get ρ j)
    change denote (m := m) (ε := ε) (HasType.bv (ι := j)) γ ρ = _
    unfold denote
    rfl

@[simp] theorem denote_lift {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A X : τ} (h : HasType Φ Γ β t A)
    (γ : CtxDen Γ) (ρ : BoundDen β) (x : TyDen X) :
    denote (m := m) (ε := ε) (h.lift (B := X)) γ (ρ, x) =
      denote (m := m) (ε := ε) h γ ρ := by
  unfold HasType.lift
  calc
    _ = denote (m := m) (ε := ε) h γ
        (BoundDen.pull (TypedRenaming.succ β X) (ρ, x)) :=
      denote_rename (m := m) (ε := ε) h _ γ _
    _ = _ := by rw [BoundDen.pull_succ]

@[simp] theorem denote_underBinder {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ (n + 1)} {A X Y : τ}
    (h : HasType Φ Γ (.snoc β Y) t A)
    (γ : CtxDen Γ) (ρ : BoundDen β) (x : TyDen X) (y : TyDen Y) :
    denote (m := m) (ε := ε) (h.underBinder (X := X)) γ ((ρ, x), y) =
      denote (m := m) (ε := ε) h γ (ρ, y) := by
  unfold HasType.underBinder
  calc
    _ = denote (m := m) (ε := ε) h γ
        (BoundDen.pull (TypedRenaming.underBinder β X Y) ((ρ, x), y)) :=
      denote_rename (m := m) (ε := ε) h _ γ _
    _ = _ := by rw [BoundDen.pull_underBinder]

@[simp] theorem denote_underTwoBinders {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ (n + 2)} {A X Y Z : τ}
    (h : HasType Φ Γ (.snoc (.snoc β Y) Z) t A)
    (γ : CtxDen Γ) (ρ : BoundDen β) (x : TyDen X) (y : TyDen Y) (z : TyDen Z) :
    denote (m := m) (ε := ε) (h.underTwoBinders (X := X)) γ (((ρ, x), y), z) =
      denote (m := m) (ε := ε) h γ ((ρ, y), z) := by
  unfold HasType.underTwoBinders
  calc
    _ = denote (m := m) (ε := ε) h γ
        (BoundDen.pull (TypedRenaming.underTwoBinders β X Y Z) (((ρ, x), y), z)) :=
      denote_rename (m := m) (ε := ε) h _ γ _
    _ = _ := by
      rw [BoundDen.pull_underTwoBinders]
      exact rfl

end Isotope.LambdaIter.Semantics
