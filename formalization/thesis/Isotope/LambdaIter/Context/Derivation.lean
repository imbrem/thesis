import Isotope.LambdaIter.Context
import Isotope.LambdaIter.Subtyping

/-!
# Proof-relevant context derivations

The raw judgments in this file live in `Type`, retaining the choices made by
each derivation. `Nonempty` supplies a proposition-valued reachability view.
`NameQuotient` quotients contexts by mutual name-change reachability; it does
not quotient derivation evidence.
-/

namespace Isotope.LambdaIter.Ctx

/-- Pointwise subtyping, preserving both context length and names. -/
inductive PointwiseSubty [TypeFormers τ] [Subtyping τ] : Ctx ν τ → Ctx ν τ → Type _ where
  | nil : PointwiseSubty .nil .nil
  | snoc {Γ Δ : Ctx ν τ} {n : Option ν} {A B : τ} :
      PointwiseSubty Γ Δ → Subty A B → PointwiseSubty (.snoc Γ n A) (.snoc Δ n B)

/-- Evidence for changing one optional name while retaining its slot. -/
inductive NameEdit : Option ν → Option ν → Type _ where
  | keep (n : Option ν) : NameEdit n n
  | introduce (x : ν) : NameEdit none (some x)
  | erase (x : ν) : NameEdit (some x) none

/-- Pointwise name changes with an unchanged type spine. -/
inductive NameChange : Ctx ν τ → Ctx ν τ → Type _ where
  | refl (Γ : Ctx ν τ) : NameChange Γ Γ
  | trans {Γ Δ Θ : Ctx ν τ} : NameChange Γ Δ → NameChange Δ Θ → NameChange Γ Θ
  | symm {Γ Δ : Ctx ν τ} : NameChange Γ Δ → NameChange Δ Γ
  | snoc {Γ Δ : Ctx ν τ} {n m : Option ν} {A : τ} :
      NameChange Γ Δ → NameEdit n m → NameChange (.snoc Γ n A) (.snoc Δ m A)

/-- Directed name erasure. The orientation is source-to-more-anonymous. -/
inductive NameErase : Ctx ν τ → Ctx ν τ → Type _ where
  | refl (Γ : Ctx ν τ) : NameErase Γ Γ
  | trans {Γ Δ Θ : Ctx ν τ} : NameErase Γ Δ → NameErase Δ Θ → NameErase Γ Θ
  | snoc_keep {Γ Δ : Ctx ν τ} {n : Option ν} {A : τ} :
      NameErase Γ Δ → NameErase (.snoc Γ n A) (.snoc Δ n A)
  | snoc_erase {Γ Δ : Ctx ν τ} {x : ν} {A : τ} :
      NameErase Γ Δ → NameErase (.snoc Γ (some x) A) (.snoc Δ none A)

namespace NameErase

def toNameChange : NameErase Γ Δ → NameChange Γ Δ
  | .refl Γ => .refl Γ
  | .trans f g => .trans f.toNameChange g.toNameChange
  | .snoc_keep f => .snoc f.toNameChange (.keep _)
  | .snoc_erase f => .snoc f.toNameChange (.erase _)

def mask [DecidableEq ν] (x : ν) : (Γ : Ctx ν τ) → NameErase Γ (Ctx.mask x Γ)
  | .nil => .refl .nil
  | .snoc Γ none A => .snoc_keep (mask x Γ)
  | .snoc Γ (some y) A => if h : x = y then by
      subst y
      rw [Ctx.mask, if_pos rfl]
      exact .snoc_erase (mask x Γ)
    else by
      rw [Ctx.mask, if_neg h]
      exact .snoc_keep (mask x Γ)

/-- Normalization erases exactly the older occurrences shadowed from the right. -/
def normalize [DecidableEq ν] : (Γ : Ctx ν τ) → NameErase Γ (Ctx.normalize Γ)
  | .nil => .refl .nil
  | .snoc Γ none _A => .snoc_keep (normalize Γ)
  | .snoc Γ (some x) _A =>
      .trans (.snoc_keep (normalize Γ)) (.snoc_keep (mask x (Ctx.normalize Γ)))

end NameErase

/-- Proposition-valued name-change reachability, forgetting derivation data. -/
abbrev NameReachable (Γ Δ : Ctx ν τ) : Prop := Nonempty (NameChange Γ Δ)

/-- Mutual reachability of contexts, distinct from equality of derivations. -/
def NameEquivalent (Γ Δ : Ctx ν τ) : Prop :=
  NameReachable Γ Δ ∧ NameReachable Δ Γ

theorem nameEquivalent_equivalence : Equivalence (@NameEquivalent ν τ) where
  refl Γ := ⟨⟨.refl Γ⟩, ⟨.refl Γ⟩⟩
  symm h := h.symm
  trans h₁ h₂ :=
    ⟨h₁.1.elim fun f => h₂.1.elim fun g => ⟨.trans f g⟩,
     h₂.2.elim fun f => h₁.2.elim fun g => ⟨.trans f g⟩⟩

/-- Setoid of contexts under mutual pointwise name-change reachability. -/
def NameChange.setoid (ν : Type u) (τ : Type v) : Setoid (Ctx ν τ) :=
  ⟨NameEquivalent, nameEquivalent_equivalence⟩

/-- Context equivalence classes; raw `NameChange` derivations are not quotiented. -/
abbrev NameQuotient (ν : Type u) (τ : Type v) := Quotient (NameChange.setoid ν τ)

end Isotope.LambdaIter.Ctx
