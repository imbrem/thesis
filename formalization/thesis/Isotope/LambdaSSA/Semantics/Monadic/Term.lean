import Isotope.LambdaSSA.Semantics.Monadic.Model
import Isotope.LambdaIter.Subtyping.Semantics.Instruction

namespace Isotope.LambdaSSA.Semantics.Monadic
set_option autoImplicit true
set_option relaxedAutoImplicit true
open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics
universe u v q r
variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m] [InstructionModel Φ τ ε m]

/-- Graph of the direct left-to-right monadic term denotation. -/
inductive Denotes (ε : Type r) [HasEff Φ ε] [Bot ε] [InstructionModel Φ τ ε m] :
    {Γ : VCtx τ} → {t : Tm Φ} → {A : τ} →
    Tm.HasType Γ t A → (Env Γ → m (TyDen A)) → Prop where
  | var (h : At Γ i A) : Denotes ε (.var h) (fun ρ => pure (Env.get ρ i h))
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
  | case {A B C : τ} {Γ : VCtx τ} {e left right : Tm Φ}
      {h : Tm.HasType Γ e (LambdaIter.coprod A B)}
      {h₁ : Tm.HasType (A :: Γ) left C} {h₂ : Tm.HasType (B :: Γ) right C}
      {f : Env Γ → m (TyDen (LambdaIter.coprod A B))}
      {l : Env (A :: Γ) → m (TyDen C)} {r : Env (B :: Γ) → m (TyDen C)}
      (he : Denotes ε h f) (hl : Denotes ε h₁ l) (hr : Denotes ε h₂ r) :
      Denotes ε (.case h h₁ h₂) (fun ρ => f ρ >>= fun e =>
        match TypeModel.coprodEquiv _ _ e with
        | .inl a => l (ρ, a) | .inr b => r (ρ, b))
  | abort (h : Denotes ε ha f) : Denotes ε (.abort (A := A) ha) (fun ρ =>
      f ρ >>= fun z => Empty.elim (TypeModel.emptyEquiv z))

private theorem exists_denotation {Γ : VCtx τ} {t : Tm Φ} {A : τ}
    (h : Tm.HasType Γ t A) : ∃ f, Denotes (m := m) ε h f := by
  induction h with
  | var h => exact ⟨_, .var h⟩
  | op _ ih => rcases ih with ⟨_, h⟩; exact ⟨_, .op h⟩
  | let₁ _ _ ia ib => rcases ia with ⟨_, a⟩; rcases ib with ⟨_, b⟩; exact ⟨_, .let₁ a b⟩
  | pair _ _ ia ib => rcases ia with ⟨_, a⟩; rcases ib with ⟨_, b⟩; exact ⟨_, .pair a b⟩
  | unit => exact ⟨_, .unit⟩
  | let₂ _ _ ia ib => rcases ia with ⟨_, a⟩; rcases ib with ⟨_, b⟩; exact ⟨_, .let₂ a b⟩
  | inl _ ih => rcases ih with ⟨_, h⟩; exact ⟨_, .inl h⟩
  | inr _ ih => rcases ih with ⟨_, h⟩; exact ⟨_, .inr h⟩
  | case _ _ _ ie il ir =>
      rcases ie with ⟨_, e⟩; rcases il with ⟨_, l⟩; rcases ir with ⟨_, r⟩
      exact ⟨_, .case e l r⟩
  | abort _ ih => rcases ih with ⟨_, h⟩; exact ⟨_, .abort h⟩

noncomputable def denote (ε : Type r) [HasEff Φ ε] [Bot ε]
    [InstructionModel Φ τ ε m] {Γ : VCtx τ} {t : Tm Φ} {A : τ}
    (h : Tm.HasType Γ t A) : Env Γ → m (TyDen A) :=
  (exists_denotation (ε := ε) (m := m) h).choose

theorem denote_spec {Γ : VCtx τ} {t : Tm Φ} {A : τ} (h : Tm.HasType Γ t A) :
    Denotes (m := m) ε h (denote (m := m) ε h) :=
  (exists_denotation (ε := ε) (m := m) h).choose_spec

end Isotope.LambdaSSA.Semantics.Monadic
