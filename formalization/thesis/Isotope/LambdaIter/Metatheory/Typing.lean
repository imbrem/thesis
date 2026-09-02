import Isotope.LambdaIter.Typing

namespace Isotope.LambdaIter.LocallyNameless

universe u v w
variable {τ : Type u} [TypeFormers τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ν : Type w} [DecidableEq ν]

private def up (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => Fin.succ (ρ i))

private theorem get_up {β : BoundCtx τ n} {β' : BoundCtx τ m} {X : τ}
    (ρ : Fin n → Fin m) (hρ : ∀ i, β'.get (ρ i) = β.get i) (i : Fin (n + 1)) :
    (β'.snoc X).get (up ρ i) = (β.snoc X).get i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact hρ j

/-- Exact typing is stable under any bound-variable renaming that preserves
the type stored at every renamed index. -/
def HasType.rename {Γ : Ctx ν τ} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {t : Tm ν Φ n} {A : τ} (ρ : Fin n → Fin m)
    (hρ : ∀ i, β'.get (ρ i) = β.get i) :
    HasType Φ Γ β t A → HasType Φ Γ β' (t.rename ρ) A
  | .fv h => .fv h
  | .bv => (hρ _).symm ▸ .bv
  | .op h => .op (h.rename ρ hρ)
  | .let₁ ha hb => .let₁ (ha.rename ρ hρ)
      (hb.rename (up ρ) (get_up ρ hρ))
  | .unit => .unit
  | .pair ha hb => .pair (ha.rename ρ hρ) (hb.rename ρ hρ)
  | .let₂ ha hb => .let₂ (ha.rename ρ hρ)
      (hb.rename (up (up ρ)) (get_up (up ρ) (get_up ρ hρ)))
  | .inl h => .inl (h.rename ρ hρ)
  | .inr h => .inr (h.rename ρ hρ)
  | .case he hl hr => .case (he.rename ρ hρ)
      (hl.rename (up ρ) (get_up ρ hρ))
      (hr.rename (up ρ) (get_up ρ hρ))
  | .abort h => .abort (h.rename ρ hρ)
  | .iter ha hb => .iter (ha.rename ρ hρ)
      (hb.rename (up ρ) (get_up ρ hρ))

/-- Insert a new ambient binder immediately below the newest binder. -/
def HasType.underBinder {Γ : Ctx ν τ} {β : BoundCtx τ n} {X Y A : τ}
    {t : Tm ν Φ (n + 1)}
    (h : HasType Φ Γ (.snoc β Y) t A) :
    HasType Φ Γ (.snoc (.snoc β X) Y) t.underBinder A :=
  h.rename (Fin.cases 0 (fun i => Fin.succ (Fin.succ i))) (by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl)

end Isotope.LambdaIter.LocallyNameless
