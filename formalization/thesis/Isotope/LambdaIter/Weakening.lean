import Isotope.LambdaIter.Context.Derivation

/-!
# Context weakening

`SlotWk` retains every index. `Wk` may remove only the newest slot at a step;
named removal carries explicit lookup evidence that this occurrence is visible
at that step. Consequently a shadowed occurrence cannot be silently dropped:
its shadow must first be removed, or its name explicitly erased while its slot
is retained.
-/

namespace Isotope.LambdaIter.Ctx

/-- Index-preserving weakening: pointwise name edits and subtyping. -/
inductive SlotWk [TypeFormers τ] [Subtyping τ] : Ctx ν τ → Ctx ν τ → Type _ where
  | nil : SlotWk .nil .nil
  | snoc {Γ Δ : Ctx ν τ} {n m : Option ν} {A B : τ} :
      SlotWk Γ Δ → NameEdit n m → Subty A B → SlotWk (.snoc Γ n A) (.snoc Δ m B)

/-- The structural shape of a weakening, forgetting type and name evidence. -/
inductive ShapeWk : Ctx ν τ → Ctx ν τ → Type _ where
  | refl (Γ : Ctx ν τ) : ShapeWk Γ Γ
  | trans {Γ Δ Θ : Ctx ν τ} : ShapeWk Γ Δ → ShapeWk Δ Θ → ShapeWk Γ Θ
  | keep {Γ Δ : Ctx ν τ} {n m : Option ν} {A B : τ} :
      ShapeWk Γ Δ → ShapeWk (.snoc Γ n A) (.snoc Δ m B)
  | drop {Γ Δ : Ctx ν τ} {n : Option ν} {A : τ} :
      ShapeWk Γ Δ → ShapeWk (.snoc Γ n A) Δ

/-- Ordinary weakening without subtyping. -/
inductive Wk [DecidableEq ν] : Ctx ν τ → Ctx ν τ → Type _ where
  | refl (Γ : Ctx ν τ) : Wk Γ Γ
  | trans {Γ Δ Θ : Ctx ν τ} : Wk Γ Δ → Wk Δ Θ → Wk Γ Θ
  | keep {Γ Δ : Ctx ν τ} {n m : Option ν} {A : τ} :
      Wk Γ Δ → NameEdit n m → Wk (.snoc Γ n A) (.snoc Δ m A)
  | drop_none {Γ Δ : Ctx ν τ} {A : τ} : Wk Γ Δ → Wk (.snoc Γ none A) Δ
  | drop_visible {Γ Δ : Ctx ν τ} {x : ν} {A : τ} :
      Wk Γ Δ → (Ctx.snoc Γ (some x) A).lookup x = some A → Wk (.snoc Γ (some x) A) Δ

/-- Weakening with pointwise subtyping on retained slots. -/
inductive SubtypeWk [DecidableEq ν] [TypeFormers τ] [Subtyping τ] :
    Ctx ν τ → Ctx ν τ → Type _ where
  | refl (Γ : Ctx ν τ) : SubtypeWk Γ Γ
  | trans {Γ Δ Θ : Ctx ν τ} : SubtypeWk Γ Δ → SubtypeWk Δ Θ → SubtypeWk Γ Θ
  | keep {Γ Δ : Ctx ν τ} {n m : Option ν} {A B : τ} :
      SubtypeWk Γ Δ → NameEdit n m → Subty A B →
      SubtypeWk (.snoc Γ n A) (.snoc Δ m B)
  | drop_none {Γ Δ : Ctx ν τ} {A : τ} : SubtypeWk Γ Δ → SubtypeWk (.snoc Γ none A) Δ
  | drop_visible {Γ Δ : Ctx ν τ} {x : ν} {A : τ} :
      SubtypeWk Γ Δ → (Ctx.snoc Γ (some x) A).lookup x = some A →
      SubtypeWk (.snoc Γ (some x) A) Δ

namespace Wk

def toSubtypeWk {ν : Type u} {τ : Type v} [DecidableEq ν] [TypeFormers τ] [Subtyping τ]
    {Γ Δ : Ctx ν τ} :
    Wk Γ Δ → SubtypeWk Γ Δ
  | .refl Γ => .refl Γ
  | .trans f g => .trans f.toSubtypeWk g.toSubtypeWk
  | .keep f e => .keep f.toSubtypeWk e (Subty.refl _)
  | .drop_none f => .drop_none f.toSubtypeWk
  | .drop_visible f h => .drop_visible f.toSubtypeWk h

def toShape {ν : Type u} {τ : Type v} [DecidableEq ν] {Γ Δ : Ctx ν τ} :
    Wk Γ Δ → ShapeWk Γ Δ
  | .refl Γ => .refl Γ
  | .trans f g => .trans f.toShape g.toShape
  | .keep f _ => .keep f.toShape
  | .drop_none f => .drop f.toShape
  | .drop_visible f _ => .drop f.toShape

end Wk

namespace SubtypeWk

/-- Forget subtyping and name evidence while preserving structural choices. -/
def toShape {ν : Type u} {τ : Type v} [DecidableEq ν] [TypeFormers τ] [Subtyping τ]
    {Γ Δ : Ctx ν τ} : SubtypeWk Γ Δ → ShapeWk Γ Δ
  | .refl Γ => .refl Γ
  | .trans f g => .trans f.toShape g.toShape
  | .keep f _ _ => .keep f.toShape
  | .drop_none f => .drop f.toShape
  | .drop_visible f _ => .drop f.toShape

end SubtypeWk

end Isotope.LambdaIter.Ctx
