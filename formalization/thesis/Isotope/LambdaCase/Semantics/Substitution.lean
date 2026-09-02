import Isotope.LambdaCase.Semantics
import Isotope.LambdaCase.TypingSubst

/-! # Semantics of lambda-case renaming and substitution -/

namespace Isotope.LambdaCase.Semantics

open Isotope.LambdaCase.LocallyNameless

universe u v w q r

variable {τ : Type u} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
  [LambdaIter.Subtyping.Semantics.TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [LambdaIter.HasTy Φ τ]
variable {ε : Type r} [LambdaIter.HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [LambdaIter.Subtyping.Semantics.InstructionModel Φ τ ε m]

namespace BoundDen

def ofFun : {n : Nat} → (β : BoundCtx τ n) →
    ((i : Fin n) → TyDen (β.get i)) → BoundDen β
  | 0, .nil, _ => PUnit.unit
  | _ + 1, .snoc β A, f => (ofFun β (fun i => f i.succ), f 0)

@[simp] theorem get_ofFun {n : Nat} (β : BoundCtx τ n)
    (f : (i : Fin n) → TyDen (β.get i)) (i : Fin n) :
    LambdaIter.Subtyping.Semantics.BoundDen.get (ofFun β f) i = f i := by
  induction β with
  | nil => exact Fin.elim0 i
  | snoc β A ih =>
      refine Fin.cases rfl (fun j => ?_) i
      exact ih (fun k => f k.succ) j

def pull {n k : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ k}
    (r : TypedRenaming β β') (ρ : BoundDen β') : BoundDen β :=
  ofFun β fun i => r.typed i ▸ LambdaIter.Subtyping.Semantics.BoundDen.get ρ (r.toFun i)

@[simp] theorem get_pull {n k : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ k}
    (r : TypedRenaming β β') (ρ : BoundDen β') (i : Fin n) :
    LambdaIter.Subtyping.Semantics.BoundDen.get (pull r ρ) i =
      r.typed i ▸ LambdaIter.Subtyping.Semantics.BoundDen.get ρ (r.toFun i) :=
  get_ofFun β _ i

@[simp] theorem pull_up {n k : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ k}
    (r : TypedRenaming β β') (ρ : BoundDen β') (A : τ) (a : TyDen A) :
    pull (r.up A) (ρ, a) = (pull r ρ, a) := by
  apply Prod.ext
  · apply congrArg (ofFun β); funext i; rfl
  · rfl

@[simp] theorem pull_succ {n : Nat} (β : BoundCtx τ n) (A : τ)
    (ρ : BoundDen β) (a : TyDen A) :
    pull (LambdaIter.LocallyNameless.TypedRenaming.succ β A) (ρ, a) = ρ := by
  induction β with
  | nil => rfl
  | snoc β B ih =>
      apply Prod.ext
      · exact ih ρ.1
      · rfl

@[simp] theorem pull_underBinder {n : Nat} (β : BoundCtx τ n) (X Y : τ)
    (ρ : BoundDen β) (x : TyDen X) (y : TyDen Y) :
    pull (LambdaIter.LocallyNameless.TypedRenaming.underBinder β X Y) ((ρ, x), y) = (ρ, y) := by
  apply Prod.ext
  · exact pull_succ β X ρ x
  · rfl

@[simp] theorem pull_underTwoBinders {n : Nat} (β : BoundCtx τ n) (X Y Z : τ)
    (ρ : BoundDen β) (x : TyDen X) (y : TyDen Y) (z : TyDen Z) :
    pull (LambdaIter.LocallyNameless.TypedRenaming.underTwoBinders β X Y Z)
      (((ρ, x), y), z) = ((ρ, y), z) := by
  apply Prod.ext
  · apply Prod.ext
    · exact pull_succ β X ρ x
    · rfl
  · rfl

end BoundDen

private theorem denote_bv_transport {Γ : Ctx ν τ} {n : Nat}
    {β : BoundCtx τ n} (i : Fin n) {A : τ} (e : β.get i = A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (e ▸ (HasType.bv (Φ := Φ) (Γ := Γ) (β := β) (i := i))) γ ρ =
      (pure (e ▸ LambdaIter.Subtyping.Semantics.BoundDen.get ρ i) : m (TyDen A)) := by
  cases e
  simp [denote]

theorem denote_rename {Γ : Ctx ν τ} {n k : Nat}
    {β : BoundCtx τ n} {β' : BoundCtx τ k} {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β t A) (r : TypedRenaming β β')
    (γ : CtxDen Γ) (ρ : BoundDen β') :
    denote (m := m) (ε := ε) (h.rename r) γ ρ =
      denote (m := m) (ε := ε) h γ (BoundDen.pull r ρ) := by
  induction h generalizing k β' with
  | fv h => simp only [HasType.rename]; unfold denote; rfl
  | bv =>
      refine (denote_bv_transport (m := m) (ε := ε) (i := r.toFun _) (e := r.typed _) γ ρ).trans ?_
      unfold denote
      congr 1
      exact (BoundDen.get_pull r ρ _).symm
  | op h ih => simp only [HasType.rename]; unfold denote; rw [ih]
  | let₁ ha hb iha ihb =>
      simp only [HasType.rename]; unfold denote
      rw [iha]
      apply bind_congr; intro a
      calc
        _ = denote (m := m) (ε := ε) hb γ (BoundDen.pull (r.up _) (ρ, a)) :=
          ihb (r.up _) (ρ, a)
        _ = _ := by rw [BoundDen.pull_up]
  | unit => simp only [HasType.rename]; unfold denote; rfl
  | pair ha hb iha ihb => simp only [HasType.rename]; unfold denote; rw [iha, ihb]
  | let₂ ha hb iha ihb =>
      simp only [HasType.rename]; unfold denote
      rw [iha]
      apply bind_congr; intro ab
      let p := LambdaIter.Subtyping.Semantics.TypeModel.tensorEquiv _ _ ab
      calc
        _ = denote (m := m) (ε := ε) hb γ
            (BoundDen.pull ((r.up _).up _) ((ρ, p.1), p.2)) :=
          ihb ((r.up _).up _) ((ρ, p.1), p.2)
        _ = _ := by rw [BoundDen.pull_up, BoundDen.pull_up]
  | inl h ih => simp only [HasType.rename]; unfold denote; rw [ih]
  | inr h ih => simp only [HasType.rename]; unfold denote; rw [ih]
  | abort h ih => simp only [HasType.rename]; unfold denote; rw [ih]
  | case he hl hr ihe ihl ihr =>
      simp only [HasType.rename]; unfold denote
      rw [ihe]
      apply bind_congr; intro e
      cases LambdaIter.Subtyping.Semantics.TypeModel.coprodEquiv _ _ e with
      | inl a =>
          simp only
          calc
            _ = denote (m := m) (ε := ε) hl γ (BoundDen.pull (r.up _) (ρ, a)) :=
              ihl (r.up _) (ρ, a)
            _ = _ := by rw [BoundDen.pull_up]
      | inr b =>
          simp only
          calc
            _ = denote (m := m) (ε := ε) hr γ (BoundDen.pull (r.up _) (ρ, b)) :=
              ihr (r.up _) (ρ, b)
            _ = _ := by rw [BoundDen.pull_up]

def SubstDen {Γ : Ctx ν τ} {n k : Nat}
    {β : BoundCtx τ n} {β' : BoundCtx τ k} {σ : Fin n → Tm ν Φ k}
    (s : TypedSubst (Γ := Γ) β β' σ) (γ : CtxDen Γ)
    (ρ' : BoundDen β') (ρ : BoundDen β) : Prop :=
  ∀ i, denote (m := m) (ε := ε) (s i) γ ρ' =
    pure (LambdaIter.Subtyping.Semantics.BoundDen.get ρ i)

theorem SubstDen.up {Γ : Ctx ν τ} {n k : Nat}
    {β : BoundCtx τ n} {β' : BoundCtx τ k} {σ : Fin n → Tm ν Φ k}
    {s : TypedSubst (Γ := Γ) β β' σ} {γ : CtxDen Γ}
    {ρ' : BoundDen β'} {ρ : BoundDen β}
    (hs : SubstDen (m := m) (ε := ε) s γ ρ' ρ)
    (A : τ) (a : TyDen A) :
    SubstDen (m := m) (ε := ε) (s.up A) γ (ρ', a) (ρ, a) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [TypedSubst.up, Fin.cases_zero]; unfold denote; rfl
  · simp only [TypedSubst.up, Fin.cases_succ]
    change denote (m := m) (ε := ε)
      (HasType.rename (LambdaIter.LocallyNameless.TypedRenaming.succ β' A) (s j))
        γ (ρ', a) = _
    calc
      _ = denote (m := m) (ε := ε) (s j) γ
          (BoundDen.pull (LambdaIter.LocallyNameless.TypedRenaming.succ β' A) (ρ', a)) :=
        denote_rename (m := m) (ε := ε) (s j) _ γ _
      _ = denote (m := m) (ε := ε) (s j) γ ρ' := by rw [BoundDen.pull_succ]
      _ = _ := hs j

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
      apply bind_congr; intro a
      exact ihb (s := s.up _) (ρ' := (ρ', a)) (ρ := (ρ, a)) (hs.up _ a)
  | unit => simp only [HasType.bsubst]; unfold denote; rfl
  | pair ha hb iha ihb => simp only [HasType.bsubst]; unfold denote; rw [iha s ρ' ρ hs, ihb s ρ' ρ hs]
  | let₂ ha hb iha ihb =>
      simp only [HasType.bsubst]; unfold denote
      rw [iha s ρ' ρ hs]
      apply bind_congr; intro ab
      exact ihb (s := (s.up _).up _)
        (ρ' := ((ρ', (LambdaIter.Subtyping.Semantics.TypeModel.tensorEquiv _ _ ab).1),
          (LambdaIter.Subtyping.Semantics.TypeModel.tensorEquiv _ _ ab).2))
        (ρ := ((ρ, (LambdaIter.Subtyping.Semantics.TypeModel.tensorEquiv _ _ ab).1),
          (LambdaIter.Subtyping.Semantics.TypeModel.tensorEquiv _ _ ab).2))
        ((hs.up _ _).up _ _)
  | inl h ih => simp only [HasType.bsubst]; unfold denote; rw [ih s ρ' ρ hs]
  | inr h ih => simp only [HasType.bsubst]; unfold denote; rw [ih s ρ' ρ hs]
  | abort h ih => simp only [HasType.bsubst]; unfold denote; rw [ih s ρ' ρ hs]
  | case he hl hr ihe ihl ihr =>
      simp only [HasType.bsubst]; unfold denote
      rw [ihe s ρ' ρ hs]
      apply bind_congr; intro e
      cases LambdaIter.Subtyping.Semantics.TypeModel.coprodEquiv _ _ e with
      | inl a => exact ihl (s := s.up _) (ρ' := (ρ', a)) (ρ := (ρ, a)) (hs.up _ a)
      | inr b => exact ihr (s := s.up _) (ρ' := (ρ', b)) (ρ := (ρ, b)) (hs.up _ b)

theorem denote_instantiate {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (hb : HasType Φ Γ (.snoc β A) b B) (ha : HasType Φ Γ β a A)
    (γ : CtxDen Γ) (ρ : BoundDen β) (x : TyDen A)
    (hx : denote (m := m) (ε := ε) ha γ ρ = pure x) :
    denote (m := m) (ε := ε) (hb.instantiate ha) γ ρ =
      denote (m := m) (ε := ε) hb γ (ρ, x) := by
  unfold HasType.instantiate
  let ss : TypedSubst (Γ := Γ) (.snoc β A) β (Fin.cases a fun i => .bv i) :=
    Fin.cases ha fun _ => .bv
  change denote (m := m) (ε := ε) (hb.bsubst ss) γ ρ = _
  apply denote_bsubst ss hb γ ρ (ρ, x)
  intro i
  refine Fin.cases hx (fun j => ?_) i
  change denote (m := m) (ε := ε) (HasType.bv (i := j)) γ ρ = _
  unfold denote
  congr 1

@[simp] theorem denote_lift {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A X : τ} (h : HasType Φ Γ β t A)
    (γ : CtxDen Γ) (ρ : BoundDen β) (x : TyDen X) :
    denote (m := m) (ε := ε) (h.lift (B := X)) γ (ρ, x) =
      denote (m := m) (ε := ε) h γ ρ := by
  unfold HasType.lift
  exact (denote_rename (m := m) (ε := ε) h _ γ _).trans (by rw [BoundDen.pull_succ])

@[simp] theorem denote_underBinder {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ (n + 1)} {A X Y : τ}
    (h : HasType Φ Γ (.snoc β Y) t A)
    (γ : CtxDen Γ) (ρ : BoundDen β) (x : TyDen X) (y : TyDen Y) :
    denote (m := m) (ε := ε) (h.underBinder (X := X)) γ ((ρ, x), y) =
      denote (m := m) (ε := ε) h γ (ρ, y) := by
  unfold HasType.underBinder
  exact (denote_rename (m := m) (ε := ε) h _ γ _).trans
    (by rw [BoundDen.pull_underBinder])

@[simp] theorem denote_underTwoBinders {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ (n + 2)} {A X Y Z : τ}
    (h : HasType Φ Γ (.snoc (.snoc β Y) Z) t A)
    (γ : CtxDen Γ) (ρ : BoundDen β) (x : TyDen X) (y : TyDen Y) (z : TyDen Z) :
    denote (m := m) (ε := ε) (h.underTwoBinders (X := X)) γ (((ρ, x), y), z) =
      denote (m := m) (ε := ε) h γ ((ρ, y), z) := by
  unfold HasType.underTwoBinders
  let r := LambdaIter.LocallyNameless.TypedRenaming.underTwoBinders β X Y Z
  have hr := denote_rename (m := m) (ε := ε) h r γ (((ρ, x), y), z)
  rw [BoundDen.pull_underTwoBinders] at hr
  exact hr

end Isotope.LambdaCase.Semantics
