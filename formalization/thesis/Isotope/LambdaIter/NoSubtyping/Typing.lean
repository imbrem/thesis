import Isotope.LambdaIter.LocallyNameless.Context
import Isotope.LambdaIter.Named.Alpha

/-!
# A syntax-directed lambda-iter experiment without subtyping

This namespace is deliberately parallel to the existing development.  It
reuses raw terms and contexts, but its typing derivations have no coercion
constructor and require no `Subtyping` instance.
-/

namespace Isotope.LambdaIter.NoSubtyping

namespace LocallyNameless

abbrev Tm := Isotope.LambdaIter.LocallyNameless.Tm
abbrev BoundCtx := Isotope.LambdaIter.LocallyNameless.BoundCtx

variable {τ : Type u} [TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]

/-- Exact, syntax-directed typing.  In particular, an instruction has exactly
its declared source and target, and there is no `sub` constructor. -/
inductive HasType (Φ : Type q) [HasTy Φ τ] (Γ : LambdaIter.Ctx ν τ) :
    {n : Nat} → BoundCtx τ n → Tm ν Φ n → τ → Type (max u q w) where
  | fv (h : Γ.lookup x = some A) : HasType Φ Γ β (.fv x) A
  | bv : HasType Φ Γ β (.bv ι) (β.get ι)
  | op (ha : HasType Φ Γ β a (instrSrc f)) : HasType Φ Γ β (.op f a) (instrTrg f)
  | let₁ (ha : HasType Φ Γ β a A)
      (hb : HasType Φ Γ (.snoc β A) b B) : HasType Φ Γ β (.let₁ a b) B
  | unit : HasType Φ Γ β .unit LambdaIter.unit
  | pair (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B) :
      HasType Φ Γ β (.pair a b) (LambdaIter.tensor A B)
  | let₂ (ha : HasType Φ Γ β a (LambdaIter.tensor A B))
      (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C) : HasType Φ Γ β (.let₂ a c) C
  | inl (ha : HasType Φ Γ β a A) : HasType Φ Γ β (.inl a) (LambdaIter.coprod A B)
  | inr (hb : HasType Φ Γ β b B) : HasType Φ Γ β (.inr b) (LambdaIter.coprod A B)
  | case (he : HasType Φ Γ β e (LambdaIter.coprod A B))
      (hl : HasType Φ Γ (.snoc β A) l C)
      (hr : HasType Φ Γ (.snoc β B) r C) : HasType Φ Γ β (.case e l r) C
  | abort (ha : HasType Φ Γ β a LambdaIter.empty) : HasType Φ Γ β (.abort a) C
  | iter (ha : HasType Φ Γ β a A)
      (hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A)) :
      HasType Φ Γ β (.iter a b) B

namespace HasType

variable {Φ : Type q} [HasTy Φ τ] {Γ Γ' : LambdaIter.Ctx ν τ}
  {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}

/-- Type-preserving free weakening and exact bound-context transport.  The
free context may gain or lose invisible/shadowed slots, but every lookup used
by the old derivation must still return the same type. -/
def weaken (hΓ : ∀ x A, Γ.lookup x = some A → Γ'.lookup x = some A) :
    {n : Nat} → {β : BoundCtx τ n} → {t : Tm ν Φ n} → {A : τ} →
      HasType Φ Γ β t A → HasType Φ Γ' β t A
  | _, _, _, _, .fv h => .fv (hΓ _ _ h)
  | _, _, _, _, .bv => .bv
  | _, _, _, _, .op h => .op (weaken hΓ h)
  | _, _, _, _, .let₁ ha hb => .let₁ (weaken hΓ ha) (weaken hΓ hb)
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .pair ha hb => .pair (weaken hΓ ha) (weaken hΓ hb)
  | _, _, _, _, .let₂ ha hc => .let₂ (weaken hΓ ha) (weaken hΓ hc)
  | _, _, _, _, .inl h => .inl (weaken hΓ h)
  | _, _, _, _, .inr h => .inr (weaken hΓ h)
  | _, _, _, _, .case he hl hr => .case (weaken hΓ he) (weaken hΓ hl) (weaken hΓ hr)
  | _, _, _, _, .abort h => .abort (weaken hΓ h)
  | _, _, _, _, .iter ha hb => .iter (weaken hΓ ha) (weaken hΓ hb)

end HasType
end LocallyNameless

namespace Named

abbrev Tm := Isotope.LambdaIter.Named.Tm
abbrev Ctx := LambdaIter.Ctx
variable {ν : Type w} [DecidableEq ν]
variable {τ : Type u} [TypeFormers τ]

/-- Exact named typing, without instruction variance or result coercions. -/
inductive HasType (Φ : Type q) [HasTy Φ τ] : Ctx ν τ → Tm ν Φ → τ → Prop where
  | var (h : Ctx.lookup Γ x = some A) : HasType Φ Γ (.var x) A
  | op (ha : HasType Φ Γ a (instrSrc f)) : HasType Φ Γ (.op f a) (instrTrg f)
  | let₁ (ha : HasType Φ Γ a A) (hb : HasType Φ (.snoc Γ x A) b B) :
      HasType Φ Γ (.let₁ x a b) B
  | unit : HasType Φ Γ .unit LambdaIter.unit
  | pair (ha : HasType Φ Γ a A) (hb : HasType Φ Γ b B) :
      HasType Φ Γ (.pair a b) (LambdaIter.tensor A B)
  | let₂ (ha : HasType Φ Γ a (LambdaIter.tensor A B))
      (hc : HasType Φ (.snoc (.snoc Γ x A) y B) c C) : HasType Φ Γ (.let₂ x y a c) C
  | inl (ha : HasType Φ Γ a A) : HasType Φ Γ (.inl a) (LambdaIter.coprod A B)
  | inr (hb : HasType Φ Γ b B) : HasType Φ Γ (.inr b) (LambdaIter.coprod A B)
  | case (he : HasType Φ Γ e (LambdaIter.coprod A B))
      (ha : HasType Φ (.snoc Γ x A) a C) (hb : HasType Φ (.snoc Γ y B) b C) :
      HasType Φ Γ (.case e x a y b) C
  | abort (ha : HasType Φ Γ a LambdaIter.empty) : HasType Φ Γ (.abort a) C
  | iter (ha : HasType Φ Γ a A)
      (hb : HasType Φ (.snoc Γ x A) b (LambdaIter.coprod B A)) :
      HasType Φ Γ (.iter a x b) B

namespace HasType

variable {Φ : Type q} [HasTy Φ τ] {Γ Γ' : Ctx ν τ} {t : Tm ν Φ} {A : τ}

private theorem lookupSnoc
    (h : ∀ x A, Γ.lookup x = some A → Γ'.lookup x = some A)
    (name : Option ν) (T : τ) :
    ∀ x A, (Ctx.snoc Γ name T).lookup x = some A →
      (Ctx.snoc Γ' name T).lookup x = some A := by
  intro x A hx
  cases name with
  | none => exact h x A hx
  | some y =>
      by_cases e : x = y
      · simpa [Ctx.lookup, e] using hx
      · simpa [Ctx.lookup, e] using h x A (by simpa [Ctx.lookup, e] using hx)

/-- Type-preserving weakening. New or removed shadowed slots are harmless;
visible variables used by the derivation retain exactly their types. -/
theorem weaken (h : HasType Φ Γ t A)
    (hw : ∀ x A, Γ.lookup x = some A → Γ'.lookup x = some A) :
    HasType Φ Γ' t A := by
  induction h generalizing Γ' with
  | var hx => exact .var (hw _ _ hx)
  | op _ ih => exact .op (ih hw)
  | let₁ _ _ iha ihb => exact .let₁ (iha hw) (ihb (lookupSnoc hw _ _))
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair (iha hw) (ihb hw)
  | let₂ _ _ iha ihc =>
      exact .let₂ (iha hw) (ihc (lookupSnoc (lookupSnoc hw _ _) _ _))
  | inl _ ih => exact .inl (ih hw)
  | inr _ ih => exact .inr (ih hw)
  | case _ _ _ ihe iha ihb =>
      exact .case (ihe hw) (iha (lookupSnoc hw _ _)) (ihb (lookupSnoc hw _ _))
  | abort _ ih => exact .abort (ih hw)
  | iter _ _ iha ihb => exact .iter (iha hw) (ihb (lookupSnoc hw _ _))

end HasType
end Named

end Isotope.LambdaIter.NoSubtyping
