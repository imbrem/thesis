import Isotope.LambdaIter.Context.Derivation

/-!
# Context weakening

`SlotWk` retains every index. `StrictWk` preserves retained types exactly;
ordinary `Wk` permits pointwise subtyping. Both structural judgments may
remove only the newest slot at a step, and named removal carries explicit
lookup evidence that this occurrence is visible at that step.
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

/-- Strict weakening, preserving the type of every retained slot. -/
inductive StrictWk [DecidableEq ν] : Ctx ν τ → Ctx ν τ → Type _ where
  | refl (Γ : Ctx ν τ) : StrictWk Γ Γ
  | trans {Γ Δ Θ : Ctx ν τ} : StrictWk Γ Δ → StrictWk Δ Θ → StrictWk Γ Θ
  | keep {Γ Δ : Ctx ν τ} {n m : Option ν} {A : τ} :
      StrictWk Γ Δ → NameEdit n m → StrictWk (.snoc Γ n A) (.snoc Δ m A)
  | drop_none {Γ Δ : Ctx ν τ} {A : τ} : StrictWk Γ Δ → StrictWk (.snoc Γ none A) Δ
  | drop_visible {Γ Δ : Ctx ν τ} {x : ν} {A : τ} :
      StrictWk Γ Δ → (Ctx.snoc Γ (some x) A).lookup x = some A →
      StrictWk (.snoc Γ (some x) A) Δ

/-- Ordinary weakening, with pointwise subtyping on retained slots. -/
inductive Wk [DecidableEq ν] [TypeFormers τ] [Subtyping τ] :
    Ctx ν τ → Ctx ν τ → Type _ where
  | refl (Γ : Ctx ν τ) : Wk Γ Γ
  | trans {Γ Δ Θ : Ctx ν τ} : Wk Γ Δ → Wk Δ Θ → Wk Γ Θ
  | keep {Γ Δ : Ctx ν τ} {n m : Option ν} {A B : τ} :
      Wk Γ Δ → NameEdit n m → Subty A B → Wk (.snoc Γ n A) (.snoc Δ m B)
  | drop_none {Γ Δ : Ctx ν τ} {A : τ} : Wk Γ Δ → Wk (.snoc Γ none A) Δ
  | drop_visible {Γ Δ : Ctx ν τ} {x : ν} {A : τ} :
      Wk Γ Δ → (Ctx.snoc Γ (some x) A).lookup x = some A →
      Wk (.snoc Γ (some x) A) Δ

namespace StrictWk

def toWk {ν : Type u} {τ : Type v} [DecidableEq ν] [TypeFormers τ] [Subtyping τ]
    {Γ Δ : Ctx ν τ} :
    StrictWk Γ Δ → Wk Γ Δ
  | .refl Γ => .refl Γ
  | .trans f g => .trans f.toWk g.toWk
  | .keep f e => .keep f.toWk e (Subty.refl _)
  | .drop_none f => .drop_none f.toWk
  | .drop_visible f h => .drop_visible f.toWk h

def toShape {ν : Type u} {τ : Type v} [DecidableEq ν] {Γ Δ : Ctx ν τ} :
    StrictWk Γ Δ → ShapeWk Γ Δ
  | .refl Γ => .refl Γ
  | .trans f g => .trans f.toShape g.toShape
  | .keep f _ => .keep f.toShape
  | .drop_none f => .drop f.toShape
  | .drop_visible f _ => .drop f.toShape

end StrictWk

namespace Wk

/-- Forget subtyping and name evidence while preserving structural choices. -/
def toShape {ν : Type u} {τ : Type v} [DecidableEq ν] [TypeFormers τ] [Subtyping τ]
    {Γ Δ : Ctx ν τ} : Wk Γ Δ → ShapeWk Γ Δ
  | .refl Γ => .refl Γ
  | .trans f g => .trans f.toShape g.toShape
  | .keep f _ _ => .keep f.toShape
  | .drop_none f => .drop f.toShape
  | .drop_visible f _ => .drop f.toShape

end Wk

end Isotope.LambdaIter.Ctx
