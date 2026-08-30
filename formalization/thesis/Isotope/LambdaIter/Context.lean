import Isotope.LambdaIter.Ty

/-!
# Snoc contexts for lambda-iter

Anonymous entries retain their position and type but cannot be looked up.
Normalization preserves the full context shape while replacing older shadowed
names by anonymous entries.
-/

namespace Isotope.LambdaIter

/-- A snoc context of optional names and types. -/
inductive Ctx (ν : Type u) (τ : Type v) : Type (max u v) where
  | nil
  | snoc (Γ : Ctx ν τ) (name : Option ν) (ty : τ)
  deriving Repr, DecidableEq

namespace Ctx

/-- Number of entries, including anonymous entries. -/
def length : Ctx ν τ → Nat
  | .nil => 0
  | .snoc Γ _ _ => Γ.length + 1

/-- Types in oldest-to-newest order. -/
def types : Ctx ν τ → List τ
  | .nil => []
  | .snoc Γ _ A => Γ.types ++ [A]

/-- Lookup the newest visible binding of a name. -/
def lookup [DecidableEq ν] : Ctx ν τ → ν → Option τ
  | .nil, _ => none
  | .snoc Γ none _, x => Γ.lookup x
  | .snoc Γ (some y) A, x => if x = y then some A else Γ.lookup x

/-- Replace every occurrence of `x` by an anonymous entry. -/
def mask [DecidableEq ν] (x : ν) : Ctx ν τ → Ctx ν τ
  | .nil => .nil
  | .snoc Γ none A => .snoc (mask x Γ) none A
  | .snoc Γ (some y) A =>
      .snoc (mask x Γ) (if x = y then none else some y) A

/-- Remove shadowing without removing entries, scanning newest-to-oldest. -/
def normalize [DecidableEq ν] : Ctx ν τ → Ctx ν τ
  | .nil => .nil
  | .snoc Γ none A => .snoc (normalize Γ) none A
  | .snoc Γ (some x) A => .snoc (mask x (normalize Γ)) (some x) A

@[simp] theorem length_mask [DecidableEq ν] (x : ν) (Γ : Ctx ν τ) :
    (mask x Γ).length = Γ.length := by
  induction Γ with
  | nil => rfl
  | snoc Γ n A ih => cases n <;> simp [mask, length, ih]

@[simp] theorem types_mask [DecidableEq ν] (x : ν) (Γ : Ctx ν τ) :
    (mask x Γ).types = Γ.types := by
  induction Γ with
  | nil => rfl
  | snoc Γ n A ih => cases n <;> simp [mask, types, ih]

@[simp] theorem length_normalize [DecidableEq ν] (Γ : Ctx ν τ) :
    (normalize Γ).length = Γ.length := by
  induction Γ with
  | nil => rfl
  | snoc Γ n A ih => cases n <;> simp [normalize, length, ih]

@[simp] theorem types_normalize [DecidableEq ν] (Γ : Ctx ν τ) :
    (normalize Γ).types = Γ.types := by
  induction Γ with
  | nil => rfl
  | snoc Γ n A ih => cases n <;> simp [normalize, types, ih]

@[simp] theorem lookup_mask_self [DecidableEq ν] (x : ν) (Γ : Ctx ν τ) :
    (mask x Γ).lookup x = none := by
  induction Γ with
  | nil => rfl
  | snoc Γ n A ih =>
      cases n with
      | none => simpa [mask, lookup] using ih
      | some y =>
          by_cases h : x = y
          · subst y
            simp [mask, lookup, ih]
          · simp [mask, lookup, h, ih]

theorem lookup_mask_of_ne [DecidableEq ν] {x y : ν} (h : y ≠ x) (Γ : Ctx ν τ) :
    (mask x Γ).lookup y = Γ.lookup y := by
  induction Γ with
  | nil => rfl
  | snoc Γ n A ih =>
      cases n with
      | none => simpa [mask, lookup] using ih
      | some z => by_cases hx : x = z <;> by_cases hy : y = z <;>
        simp_all [mask, lookup]

@[simp] theorem lookup_normalize [DecidableEq ν] (Γ : Ctx ν τ) (x : ν) :
    (normalize Γ).lookup x = Γ.lookup x := by
  induction Γ with
  | nil => rfl
  | snoc Γ n A ih =>
      cases n with
      | none => simpa [normalize, lookup] using ih
      | some y =>
          by_cases h : x = y
          · subst x
            simp [normalize, lookup]
          · simp [normalize, lookup, h, lookup_mask_of_ne h, ih]

/-- Contexts in which each visible name occurs at most once. -/
inductive ShadowFree [DecidableEq ν] : Ctx ν τ → Prop where
  | nil : ShadowFree .nil
  | snoc_none {Γ : Ctx ν τ} {A : τ} : ShadowFree Γ → ShadowFree (.snoc Γ none A)
  | snoc_some {Γ : Ctx ν τ} {x : ν} {A : τ} :
      ShadowFree Γ → Γ.lookup x = none → ShadowFree (.snoc Γ (some x) A)

theorem ShadowFree.mask [DecidableEq ν] {Γ : Ctx ν τ} (hΓ : ShadowFree Γ) (z : ν) :
    ShadowFree (mask z Γ) := by
  induction hΓ with
  | nil => exact .nil
  | snoc_none _ ih => exact .snoc_none ih
  | @snoc_some Γ x A _ hx ih =>
      by_cases hzx : z = x
      · rw [Ctx.mask, if_pos hzx]
        exact ShadowFree.snoc_none ih
      · rw [Ctx.mask, if_neg hzx]
        exact ShadowFree.snoc_some ih (lookup_mask_of_ne (Ne.symm hzx) Γ ▸ hx)

theorem shadowFree_normalize [DecidableEq ν] (Γ : Ctx ν τ) : ShadowFree (normalize Γ) := by
  induction Γ with
  | nil => exact .nil
  | snoc Γ n A ih =>
      cases n with
      | none => exact .snoc_none ih
      | some x => exact .snoc_some (ih.mask x) (lookup_mask_self x _)

theorem mask_eq_self_of_lookup_eq_none [DecidableEq ν] {Γ : Ctx ν τ} {x : ν}
    (h : Γ.lookup x = none) : mask x Γ = Γ := by
  induction Γ with
  | nil => rfl
  | snoc Γ n A ih =>
      cases n with
      | none => simp [mask, ih h]
      | some y =>
          by_cases hxy : x = y
          · simp [lookup, hxy] at h
          · simp [mask, hxy, ih (by simpa [lookup, hxy] using h)]

theorem ShadowFree.normalize_eq [DecidableEq ν] {Γ : Ctx ν τ} (hΓ : ShadowFree Γ) :
    normalize Γ = Γ := by
  induction hΓ with
  | nil => rfl
  | snoc_none _ ih => simp [normalize, ih]
  | @snoc_some Γ x A _ hx ih => simp [normalize, ih, mask_eq_self_of_lookup_eq_none hx]

@[simp] theorem normalize_idem [DecidableEq ν] (Γ : Ctx ν τ) :
    normalize (normalize Γ) = normalize Γ :=
  (shadowFree_normalize Γ).normalize_eq

theorem normalize_eq_self_iff [DecidableEq ν] {Γ : Ctx ν τ} :
    normalize Γ = Γ ↔ ShadowFree Γ := by
  constructor
  · intro h
    rw [← h]
    exact shadowFree_normalize Γ
  · exact ShadowFree.normalize_eq

end Ctx

end Isotope.LambdaIter
