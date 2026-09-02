import Isotope.LambdaSeq.Models.Alg
import Isotope.LambdaSeq.Metatheory

/-!
# The syntactic setoid of lambda-seq

The equational theory `Equiv` of the exact (subtyping-free) lambda-seq judgment
is a `Setoid` on *typable* terms, and this file constructs it.

`Equiv` has `symm` and `trans` as constructors but no `refl`; reflexivity at a
general typable term is `Equiv.refl` of `Isotope/LambdaSeq/Metatheory.lean`.
Since reflexivity is available only at typable terms, there is no setoid on raw
`Tm`, and the carrier is a subtype carrying `Nonempty`-truncated typing
evidence.  Truncation keeps the carrier in `Type u` and makes two elements with
the same underlying term *definitionally* equal, which is what lets `Alg.coh`
hold for the syntactic model by `rfl`.  Choice enters only in
`Models/Initial.lean`.
-/

namespace Isotope.LambdaSeq

open LocallyNameless

open Isotope.LambdaIter (Sig)

universe u

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
related by the lambda-seq equational theory at the signature's pure effect.
Choice-free: reflexivity uses `Nonempty.elim` into a `Prop`. -/
instance setoid (S : Sig.{u}) {n : Nat} (β : BoundCtx S.Ty n) (A : S.Ty) :
    Setoid (Carrier S β A) where
  r a b := Equiv (Φ := S.Instr) S.pureEff LambdaIter.Ctx.nil β a.1 b.1 A
  iseqv := ⟨fun a => a.2.elim LocallyNameless.Equiv.refl,
    LocallyNameless.Equiv.symm, LocallyNameless.Equiv.trans⟩

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

/-- Conversely, classes are equal only for equal terms: the exactness half of
the quotient, and the source of equational completeness. -/
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

end Syn

end Isotope.LambdaSeq
