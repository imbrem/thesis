import Isotope.LambdaSSA.Subtyping.Typing
import Isotope.LambdaSSA.Semantics.Monadic.Model
import Isotope.LambdaIter.Subtyping.Semantics.Instruction

/-! # Direct proof-relevant monadic semantics of subtyped SSA terms -/

namespace Isotope.LambdaSSA.Subtyping.Semantics.Monadic
set_option autoImplicit true
set_option relaxedAutoImplicit true

open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics

universe u v q r

variable {τ : Type u} [TypeFormers τ] [LambdaIter.Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m] [InstructionModel Φ τ ε m]

abbrev Env {τ : Type u} [TypeFormers τ] [LambdaIter.Subtyping τ]
    [TypeModel.{u, v} τ] (Γ : VCtx τ) : Type v :=
  @LambdaSSA.Semantics.Monadic.Env τ _ _ _ Γ

/-- Direct call-by-value semantics.  The `.sub` equation applies the coercion
selected by that particular subtype witness, so the definition does not
silently assume proof irrelevance. -/
def denote : {Γ : VCtx τ} → {t : LambdaSSA.Tm Φ} → {A : τ} →
    Tm.HasType Γ t A → Env Γ → m (TyDen A)
  | _, _, _, .var h, ρ => pure (LambdaSSA.Semantics.Monadic.Env.get ρ _ h)
  | _, _, _, .op h, ρ => denote h ρ >>=
      InstructionModel.denote (Φ := Φ) (τ := τ) (ε := ε) (m := m) _
  | _, _, _, .let₁ ha hb, ρ => denote ha ρ >>= fun a => denote hb (ρ, a)
  | _, _, _, .pair ha hb, ρ =>
      denote ha ρ >>= fun a => denote hb ρ >>= fun b =>
        pure ((TypeModel.tensorEquiv _ _).symm (a, b))
  | _, _, _, .unit, _ => pure (TypeModel.unitEquiv.symm ())
  | _, _, _, .let₂ ha hb, ρ => denote ha ρ >>= fun ab =>
      let p := TypeModel.tensorEquiv _ _ ab
      denote hb ((ρ, p.1), p.2)
  | _, _, _, .inl ha, ρ => denote ha ρ >>= fun a =>
      pure ((TypeModel.coprodEquiv _ _).symm (.inl a))
  | _, _, _, .inr hb, ρ => denote hb ρ >>= fun b =>
      pure ((TypeModel.coprodEquiv _ _).symm (.inr b))
  | _, _, _, .case he hl hr, ρ => denote he ρ >>= fun e =>
      match TypeModel.coprodEquiv _ _ e with
      | .inl a => denote hl (ρ, a)
      | .inr b => denote hr (ρ, b)
  | _, _, _, .abort ha, ρ => denote ha ρ >>= fun z =>
      Empty.elim (TypeModel.emptyEquiv z)
  | _, _, _, .sub ha d, ρ => denote ha ρ >>= fun a => pure (coeSub d a)

/-- Graph of the direct proof-relevant term denotation. -/
inductive Denotes (ε : Type r) [HasEff Φ ε] [Bot ε] [InstructionModel Φ τ ε m] :
    {Γ : VCtx τ} → {t : LambdaSSA.Tm Φ} → {A : τ} →
    Tm.HasType Γ t A → (Env Γ → m (TyDen A)) → Prop where
  | var (h : At Γ i A) : Denotes ε (.var h) (fun ρ => pure
      (LambdaSSA.Semantics.Monadic.Env.get ρ i h))
  | op (h : Denotes ε ha fa) : Denotes ε (.op ha) (fun ρ => fa ρ >>=
      InstructionModel.denote (Φ := Φ) (τ := τ) (ε := ε) (m := m) _)
  | let₁ (ha : Denotes ε h₁ f) (hb : Denotes ε h₂ g) :
      Denotes ε (.let₁ h₁ h₂) (fun ρ => f ρ >>= fun a => g (ρ, a))
  | pair (ha : Denotes ε h₁ f) (hb : Denotes ε h₂ g) :
      Denotes ε (.pair h₁ h₂) (fun ρ => f ρ >>= fun a => g ρ >>= fun b =>
        pure ((TypeModel.tensorEquiv _ _).symm (a, b)))
  | unit : Denotes ε (.unit (Γ := Γ)) (fun _ => pure (TypeModel.unitEquiv.symm ()))
  | let₂ (ha : Denotes ε h₁ f) (hb : Denotes ε h₂ g) :
      Denotes ε (.let₂ h₁ h₂) (fun ρ => f ρ >>= fun ab =>
        let p := TypeModel.tensorEquiv _ _ ab; g ((ρ, p.1), p.2))
  | inl (h : Denotes ε ha f) : Denotes ε (.inl (B := B) ha) (fun ρ =>
      f ρ >>= fun a => pure ((TypeModel.coprodEquiv _ _).symm (.inl a)))
  | inr (h : Denotes ε hb f) : Denotes ε (.inr (A := A) hb) (fun ρ =>
      f ρ >>= fun b => pure ((TypeModel.coprodEquiv _ _).symm (.inr b)))
  | case {A B C : τ} {h : Tm.HasType Γ e (coprod A B)}
      {h₁ : Tm.HasType (A :: Γ) left C} {h₂ : Tm.HasType (B :: Γ) right C}
      {f : Env Γ → m (TyDen (coprod A B))}
      {l : Env (A :: Γ) → m (TyDen C)} {r : Env (B :: Γ) → m (TyDen C)}
      (he : Denotes ε h f) (hl : Denotes ε h₁ l) (hr : Denotes ε h₂ r) :
      Denotes ε (.case h h₁ h₂) (fun ρ => f ρ >>= fun value =>
        match TypeModel.coprodEquiv A B value with
        | .inl a => l (ρ, a) | .inr b => r (ρ, b))
  | abort (h : Denotes ε ha f) : Denotes ε (.abort (A := A) ha) (fun ρ =>
      f ρ >>= fun z => Empty.elim (TypeModel.emptyEquiv z))
  | sub {A B : τ} {ha : Tm.HasType Γ a A} {f : Env Γ → m (TyDen A)}
      (h : Denotes ε ha f) (d : Subty A B) : Denotes ε (.sub ha d) (fun ρ =>
        f ρ >>= fun value => pure (coeSub d value))

theorem denote_spec {Γ : VCtx τ} {t : LambdaSSA.Tm Φ} {A : τ}
    (h : Tm.HasType Γ t A) :
    Denotes ε h (denote (ε := ε) (m := m) h) := by
  induction h with
  | var h => exact .var h
  | op _ ih => exact .op ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | pair _ _ iha ihb => exact .pair iha ihb
  | unit => exact .unit
  | let₂ _ _ iha ihb => exact .let₂ iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ihe ihl ihr => exact .case ihe ihl ihr
  | abort _ ih => exact .abort ih
  | sub _ d ih => exact .sub ih d

@[simp] theorem denote_sub {Γ : VCtx τ} {t : LambdaSSA.Tm Φ} {A B : τ}
    (h : Tm.HasType Γ t A) (d : Subty A B) (ρ : Env Γ) :
    denote (ε := ε) (m := m) (.sub h d) ρ =
      (denote (ε := ε) (m := m) h ρ >>= fun a => pure (coeSub d a)) := rfl

end Isotope.LambdaSSA.Subtyping.Semantics.Monadic
