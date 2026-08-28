import Isotope.LambdaIter.Context.Derivation

/-!
# Shadow-only name edits

`ShadowEdit Γ Δ` is oriented from the source context `Γ` to the edited context
`Δ`. Unlike broad `NameChange`, an atomic edit is checked position-by-position:
each changed named source and target slot carries evidence of a same-named slot
at a strictly newer index. Anonymous slots need no source witness; introducing
a name requires the corresponding target witness. Types and slots are fixed.
-/

namespace Isotope.LambdaIter.Ctx

/-- Optional names, indexed newest first. -/
def namesNewest : Ctx ν τ → List (Option ν)
  | .nil => []
  | .snoc Γ n _ => n :: namesNewest Γ

/-- The optional name at a newest-first index. -/
def nameAt (Γ : Ctx ν τ) (i : Nat) : Option (Option ν) := Γ.namesNewest[i]?

/-- Evidence that `x` at index `i` is shadowed by a strictly newer slot. -/
def ShadowedAt (Γ : Ctx ν τ) (i : Nat) (x : ν) : Prop :=
  ∃ j, j < i ∧ Γ.nameAt j = some (some x)

/-- One checked, simultaneous edit of shadowed names. -/
structure ShadowAtom [DecidableEq ν] (Γ Δ : Ctx ν τ) : Type _ where
  length_eq : Γ.length = Δ.length
  types_eq : Γ.types = Δ.types
  source_shadowed : ∀ i x,
    Γ.nameAt i = some (some x) → Δ.nameAt i ≠ some (some x) → ShadowedAt Γ i x
  target_shadowed : ∀ i x,
    Δ.nameAt i = some (some x) → Γ.nameAt i ≠ some (some x) → ShadowedAt Δ i x
  shadowed_iff : ∀ i x, ShadowedAt Γ i x ↔ ShadowedAt Δ i x
  lookup_eq : ∀ x, Γ.lookup x = Δ.lookup x

/-- Proof-relevant reflexive/transitive closure of checked shadow-only edits. -/
inductive ShadowEdit [DecidableEq ν] : Ctx ν τ → Ctx ν τ → Type _ where
  | refl (Γ : Ctx ν τ) : ShadowEdit Γ Γ
  | atom {Γ Δ : Ctx ν τ} : ShadowAtom Γ Δ → ShadowEdit Γ Δ
  | trans {Γ Δ Θ : Ctx ν τ} : ShadowEdit Γ Δ → ShadowEdit Δ Θ → ShadowEdit Γ Θ

namespace ShadowEdit

/-- Shadow-only edits preserve all visible lookup results. -/
theorem lookup_eq {ν : Type u} {τ : Type v} [DecidableEq ν] {Γ Δ : Ctx ν τ}
    (d : ShadowEdit Γ Δ) (x : ν) :
    Γ.lookup x = Δ.lookup x := by
  induction d with
  | refl => rfl
  | atom d => exact d.lookup_eq x
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem length_eq {ν : Type u} {τ : Type v} [DecidableEq ν] {Γ Δ : Ctx ν τ}
    (d : ShadowEdit Γ Δ) : Γ.length = Δ.length := by
  induction d with
  | refl => rfl
  | atom d => exact d.length_eq
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem types_eq {ν : Type u} {τ : Type v} [DecidableEq ν] {Γ Δ : Ctx ν τ}
    (d : ShadowEdit Γ Δ) : Γ.types = Δ.types := by
  induction d with
  | refl => rfl
  | atom d => exact d.types_eq
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Inject a fully checked normalization step. -/
def normalizeOfAtom [DecidableEq ν] {Γ : Ctx ν τ}
    (d : ShadowAtom Γ (Ctx.normalize Γ)) : ShadowEdit Γ (Ctx.normalize Γ) := .atom d

/-- A context already in normal form has a reflexive normalization edit. -/
def normalizeOfShadowFree [DecidableEq ν] {Γ : Ctx ν τ} (hΓ : ShadowFree Γ) :
    ShadowEdit Γ (Ctx.normalize Γ) := by
  rw [hΓ.normalize_eq]
  exact .refl Γ

end ShadowEdit

/-- Proposition-valued reachability, deliberately forgetting edit evidence. -/
abbrev ShadowReachable [DecidableEq ν] (Γ Δ : Ctx ν τ) : Prop :=
  Nonempty (ShadowEdit Γ Δ)

end Isotope.LambdaIter.Ctx
