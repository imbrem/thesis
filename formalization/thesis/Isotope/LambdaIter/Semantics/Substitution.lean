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

end BoundDen

private theorem denote_bv_transport {Γ : Ctx ν τ} {n : Nat}
    {β : BoundCtx τ n} (i : Fin n) {A : τ} (e : β.get i = A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε)
        (e ▸ (HasType.bv (Φ := Φ) (Γ := Γ) (β := β) (ι := i))) γ ρ =
      (pure (e ▸ BoundDen.get ρ i) : m (TyDen A)) := by
  cases e
  simp [denote]

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

end Isotope.LambdaIter.Semantics
