import Isotope.LambdaCase.Models.Alg
import Isotope.LambdaCase.Metatheory

/-!
# The syntactic setoid of lambda-case

The equational theory `Equiv` of the exact (subtyping-free) lambda-case
judgment is a `Setoid` on *typable* terms, and this file constructs it.

## Why an equivalence relation at all

`Equiv` has `symm` and `trans` as constructors but **no** `refl`: reflexivity
holds only at the three leaves `var`, `bvar` and `unit`.  Reflexivity at a
general typable term is `Equiv.refl` of `Isotope/LambdaCase/Metatheory.lean`,
proved by recursion on the typing derivation.  That lemma is the sole
prerequisite of everything below.

## Why the carrier is a subtype

Reflexivity is available only at typable terms, so there is no setoid on raw
`Tm`, and the carrier is forced to be

```
{a : Tm Empty S.Instr n // Nonempty (HasType S.Instr Ctx.nil β a A)}
```

Truncating the derivation with `Nonempty` keeps the carrier in `Type u` and
makes two elements with the same underlying term *definitionally* equal, which
is what lets `Alg.coh` hold for the syntactic model by `rfl`.  Reflexivity of
the setoid needs no choice: `Nonempty.elim` into the `Prop`-valued `Equiv`
suffices.  Choice enters only in `Models/Initial.lean`, where an actual
derivation must be extracted to interpret a class in another model.

## Fixed syntax parameters

Free variables are fixed at `ν := Empty` and the free context at `Ctx.nil`,
matching `Isotope.LambdaCase.Alg`.
-/

namespace Isotope.LambdaCase

open LocallyNameless

open Isotope.LambdaIter (Sig)

universe u v₁ v₂ v₃ v₄

namespace Syn

variable {S : Sig.{u}}

/-- A term of type `A` in bound context `β` together with the (truncated)
evidence that it is typable.  This is the carrier of the syntactic setoid. -/
def Carrier (S : Sig.{u}) {n : Nat} (β : BoundCtx S.Ty n) (A : S.Ty) : Type u :=
  {a : Tm Empty S.Instr n //
    Nonempty (HasType S.Instr LambdaIter.Ctx.nil β a A)}

/-- The underlying raw term of a typable term. -/
@[reducible] def Carrier.tm {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty}
    (a : Carrier S β A) : Tm Empty S.Instr n := a.1

/-- Two typable terms with the same underlying raw term are equal: the typing
evidence is `Nonempty`-truncated, hence proof irrelevant. -/
theorem Carrier.ext {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty}
    {a b : Carrier S β A} (h : a.1 = b.1) : a = b := Subtype.ext h

/-- The syntactic setoid: typable terms of type `A` in bound context `β`,
related by the lambda-case equational theory at the signature's pure effect.

Reflexivity uses `Nonempty.elim`, which lands in a `Prop`, so this definition
is choice-free. -/
instance setoid (S : Sig.{u}) {n : Nat} (β : BoundCtx S.Ty n) (A : S.Ty) :
    Setoid (Carrier S β A) where
  r a b := Equiv (Φ := S.Instr) S.pureEff LambdaIter.Ctx.nil β a.1 b.1 A
  iseqv := ⟨fun a => a.2.elim LocallyNameless.Equiv.refl, LocallyNameless.Equiv.symm,
    LocallyNameless.Equiv.trans⟩

theorem setoid_r_iff {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty}
    {a b : Carrier S β A} :
    a ≈ b ↔
      Equiv (Φ := S.Instr) S.pureEff LambdaIter.Ctx.nil β a.1 b.1 A := Iff.rfl

/-- The carrier of the syntactic model: typable terms of type `A` in bound
context `β`, modulo the equational theory. -/
def El (S : Sig.{u}) {n : Nat} (β : BoundCtx S.Ty n) (A : S.Ty) : Type u :=
  Quotient (setoid S β A)

/-- The equivalence class of a typing derivation. -/
def mk {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty} {t : Tm Empty S.Instr n}
    (h : HasType S.Instr LambdaIter.Ctx.nil β t A) : El S β A :=
  Quotient.mk _ ⟨t, ⟨h⟩⟩

/-- The class of a term depends only on the term, not on the derivation. -/
theorem mk_congr {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty}
    {t : Tm Empty S.Instr n}
    (h k : HasType S.Instr LambdaIter.Ctx.nil β t A) : mk h = mk k := rfl

/-- Equal terms have equal classes. -/
theorem mk_eq_mk {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty}
    {t t' : Tm Empty S.Instr n}
    (h : HasType S.Instr LambdaIter.Ctx.nil β t A)
    (h' : HasType S.Instr LambdaIter.Ctx.nil β t' A)
    (e : Equiv (Φ := S.Instr) S.pureEff LambdaIter.Ctx.nil β t t' A) :
    mk h = mk h' := Quotient.sound e

/-- Conversely, classes are equal only for equal terms: this is the exactness
half of the quotient, and the source of equational completeness. -/
theorem equiv_of_mk_eq {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty}
    {t t' : Tm Empty S.Instr n}
    {h : HasType S.Instr LambdaIter.Ctx.nil β t A}
    {h' : HasType S.Instr LambdaIter.Ctx.nil β t' A} (e : mk h = mk h') :
    Equiv (Φ := S.Instr) S.pureEff LambdaIter.Ctx.nil β t t' A :=
  Quotient.exact e

/-- Every class is the class of some derivation. -/
theorem ind {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty}
    {motive : El S β A → Prop}
    (H : ∀ (t : Tm Empty S.Instr n)
      (h : HasType S.Instr LambdaIter.Ctx.nil β t A), motive (mk h))
    (x : El S β A) : motive x := by
  induction x using Quotient.ind with
  | _ a => exact (a.2).elim (fun h => H a.1 h)

/-- A three-argument quotient map.  The library has `Quotient.map` and
`Quotient.map₂` but no `map₃`, and the `case` operation of lambda-case needs
one (at three *different* setoids).

This is a generic fact about quotients, stated here in the `LambdaCase`
namespace only to avoid colliding with the identical
`Isotope.LambdaIter.Syn.map₃` developed concurrently for lambda-iter; a later
merge should collapse the two into a single root-namespace lemma. -/
def map₃ {α : Type v₁} {β : Type v₂} {γ : Type v₃} {δ : Type v₄}
    {s₁ : Setoid α} {s₂ : Setoid β} {s₃ : Setoid γ} {s₄ : Setoid δ}
    (f : α → β → γ → δ)
    (hf : ∀ a a', a ≈ a' → ∀ b b', b ≈ b' → ∀ c c', c ≈ c' →
      f a b c ≈ f a' b' c')
    (x : Quotient s₁) (y : Quotient s₂) (z : Quotient s₃) : Quotient s₄ :=
  Quotient.liftOn₂ x y
    (fun a b => Quotient.map (f a b)
      (fun c c' hc => hf a a (Setoid.refl a) b b (Setoid.refl b) c c' hc) z)
    (fun a b a' b' ha hb => by
      induction z using Quotient.ind with
      | _ c => exact Quotient.sound (hf a a' ha b b' hb c c (Setoid.refl c)))

@[simp] theorem map₃_mk {α : Type v₁} {β : Type v₂} {γ : Type v₃} {δ : Type v₄}
    {s₁ : Setoid α} {s₂ : Setoid β} {s₃ : Setoid γ} {s₄ : Setoid δ}
    (f : α → β → γ → δ) (hf) (a : α) (b : β) (c : γ) :
    map₃ (s₄ := s₄) f hf (Quotient.mk s₁ a) (Quotient.mk s₂ b)
      (Quotient.mk s₃ c) = Quotient.mk s₄ (f a b c) := rfl

end Syn

end Isotope.LambdaCase
