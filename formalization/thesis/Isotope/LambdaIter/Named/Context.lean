import Isotope.LambdaIter.Named.Defs

/-! # Shadowing contexts for named lambda-iter -/

namespace Isotope.LambdaIter.Named

abbrev Ctx (ι : Type u) (τ : Type v) := List (Option ι × τ)

namespace Ctx

/-- Named contexts permit shadowing, so every sequence of (optional) names and
types is well formed. Keeping the judgment explicit makes that policy visible. -/
inductive WellFormed : Ctx ι τ → Prop where
  | nil : WellFormed []
  | cons (h : WellFormed Γ) : WellFormed ((x, A) :: Γ)

theorem wellFormed (Γ : Ctx ι τ) : WellFormed Γ := by
  induction Γ with
  | nil => exact .nil
  | cons _ _ ih => exact .cons ih

variable [DecidableEq ι]

/-- First-match lookup: the head of the list is the most recent binder. -/
def lookup (Γ : Ctx ι τ) (x : ι) : Option τ :=
  match Γ with
  | [] => none
  | (none, _) :: Γ => lookup Γ x
  | (some y, A) :: Γ => if x = y then some A else lookup Γ x

@[simp] theorem lookup_nil (x : ι) : lookup ([] : Ctx ι τ) x = none := rfl
@[simp] theorem lookup_anon (Γ : Ctx ι τ) (A : τ) (x : ι) :
    lookup ((none, A) :: Γ) x = lookup Γ x := rfl
@[simp] theorem lookup_here (Γ : Ctx ι τ) (A : τ) (x : ι) :
    lookup ((some x, A) :: Γ) x = some A := by simp [lookup]
@[simp] theorem lookup_there (Γ : Ctx ι τ) (A : τ) {x y : ι} (h : x ≠ y) :
    lookup ((some y, A) :: Γ) x = lookup Γ x := by simp [lookup, h]

/-- A shadowing-safe context change preserves every currently visible binding. -/
def Preserves (Γ Δ : Ctx ι τ) : Prop :=
  ∀ x A, lookup Γ x = some A → lookup Δ x = some A

@[refl] theorem Preserves.refl (Γ : Ctx ι τ) : Preserves Γ Γ := fun _ _ => id
@[trans] theorem Preserves.trans {Γ Δ Ξ : Ctx ι τ} :
    Preserves Γ Δ → Preserves Δ Ξ → Preserves Γ Ξ :=
  fun h k x A hx => k x A (h x A hx)

theorem preserves_anon (Γ : Ctx ι τ) (A : τ) : Preserves Γ ((none, A) :: Γ) :=
  fun _ _ h => h

theorem Preserves.cons (x : Option ι) (A : τ) {Γ Δ : Ctx ι τ}
    (h : Preserves Γ Δ) : Preserves ((x, A) :: Γ) ((x, A) :: Δ) := by
  intro y B hy
  cases x with
  | none => exact h y B hy
  | some x =>
    by_cases e : y = x
    · subst e; simpa using hy
    · simpa [lookup, e] using h y B (by simpa [lookup, e] using hy)

/-- Removing an entry is strengthening exactly when all visible lookups remain. -/
def CanErase (Γ : Ctx ι τ) (b : Option ι × τ) : Prop :=
  Preserves (b :: Γ) Γ

end Ctx
end Isotope.LambdaIter.Named
