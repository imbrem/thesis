import Isotope.LambdaIter.Named.Context

/-! # Structural subtyping for named lambda-iter -/

namespace Isotope.LambdaIter.Named

open TypeFormers

/-- The subtyping structure needed by the thesis rules. It is deliberately a
separate class from `TypeFormers`: an arbitrary semantic type universe can
choose its own preorder, while `Ty` receives the freely generated one below. -/
class Subtyping (τ : Type u) [TypeFormers τ] where
  subty : τ → τ → Prop
  refl (A : τ) : subty A A
  trans {A B C : τ} : subty A B → subty B C → subty A C
  tensor {A A' B B' : τ} :
    subty A A' → subty B B' → subty (TypeFormers.tensor A B) (TypeFormers.tensor A' B')
  coprod {A A' B B' : τ} :
    subty A A' → subty B B' → subty (TypeFormers.coprod A B) (TypeFormers.coprod A' B')
  empty (A : τ) : subty TypeFormers.empty A
  unit (A : τ) : subty A TypeFormers.unit

def Subty [TypeFormers τ] [Subtyping τ] (A B : τ) : Prop :=
  Subtyping.subty A B

namespace Subty

variable [TypeFormers τ] [Subtyping τ]

@[refl] theorem refl (A : τ) : Subty A A := Subtyping.refl A
@[trans] theorem trans {A B C : τ} : Subty A B → Subty B C → Subty A C :=
  Subtyping.trans

theorem tensor {A A' B B' : τ} : Subty A A' → Subty B B' →
    Subty (TypeFormers.tensor A B) (TypeFormers.tensor A' B') := Subtyping.tensor

theorem coprod {A A' B B' : τ} : Subty A A' → Subty B B' →
    Subty (TypeFormers.coprod A B) (TypeFormers.coprod A' B') := Subtyping.coprod

theorem empty (A : τ) : Subty TypeFormers.empty A := Subtyping.empty A
theorem unit (A : τ) : Subty A TypeFormers.unit := Subtyping.unit A

end Subty

/-- Structural subtyping on freely generated simple types. -/
inductive Ty.Subty : Ty α → Ty α → Prop where
  | refl (A) : Ty.Subty A A
  | trans : Ty.Subty A B → Ty.Subty B C → Ty.Subty A C
  | tensor : Ty.Subty A A' → Ty.Subty B B' →
      Ty.Subty (.tensor A B) (.tensor A' B')
  | coprod : Ty.Subty A A' → Ty.Subty B B' →
      Ty.Subty (.coprod A B) (.coprod A' B')
  | empty (A) : Ty.Subty .empty A
  | unit (A) : Ty.Subty A .unit

instance : Subtyping (Ty α) where
  subty := Ty.Subty
  refl := Ty.Subty.refl
  trans := Ty.Subty.trans
  tensor := Ty.Subty.tensor
  coprod := Ty.Subty.coprod
  empty := Ty.Subty.empty
  unit := Ty.Subty.unit

/-- Thesis instruction typing: accepted inputs vary contravariantly from the
declared source and returned results vary covariantly from the declared target. -/
structure InstTy [TypeFormers τ] [Subtyping τ] (S : Signature τ)
    (f : S.Op) (A B : τ) : Prop where
  input : Subty A (S.src f)
  output : Subty (S.trg f) B

namespace Ctx

variable [DecidableEq ι] [TypeFormers τ] [Subtyping τ]

/-- Thesis context weakening, oriented from the old context to the new one.
Every old visible binding has a visible subtype in the new context. Because it
is stated through first-match lookup, inserting a shadowing binder is accepted
only when the shadowing type is an appropriate subtype. -/
def Weakens (Γ Δ : Ctx ι τ) : Prop :=
  ∀ x A, lookup Γ x = some A → ∃ B, lookup Δ x = some B ∧ Subty B A

@[refl] theorem Weakens.refl (Γ : Ctx ι τ) : Weakens Γ Γ :=
  fun _ A h => ⟨A, h, Subty.refl A⟩

@[trans] theorem Weakens.trans {Γ Δ Ξ : Ctx ι τ} :
    Weakens Γ Δ → Weakens Δ Ξ → Weakens Γ Ξ := by
  intro h k x A hx
  obtain ⟨B, hB, hBA⟩ := h x A hx
  obtain ⟨C, hC, hCB⟩ := k x B hB
  exact ⟨C, hC, hCB.trans hBA⟩

theorem Weakens.cons (x : Option ι) (A : τ) {Γ Δ : Ctx ι τ}
    (h : Weakens Γ Δ) : Weakens ((x, A) :: Γ) ((x, A) :: Δ) := by
  intro y B hy
  cases x with
  | none => exact h y B hy
  | some x =>
    by_cases e : y = x
    · subst e
      have hAB : A = B := by simpa [lookup] using hy
      subst B
      exact ⟨A, by simp [lookup], Subty.refl A⟩
    · obtain ⟨C, hC, hCB⟩ := h y B (by simpa [lookup, e] using hy)
      exact ⟨C, by simpa [lookup, e] using hC, hCB⟩

end Ctx

end Isotope.LambdaIter.Named
