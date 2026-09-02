import Isotope.LambdaSeq.Models.Setoid

/-!
# The syntactic model of lambda-seq

`Syn S` is the quotient of the typable lambda-seq terms over the signature `S`
by the equational theory `Equiv`, organized as an object of `Alg S`.

Both non-variable operations are `Quotient` lifts of the corresponding term
former, well defined because `Equiv` has a congruence constructor for each.
The two propositional fields of `Alg` hold **by construction**: `coh` because a
`Quotient` class depends only on the underlying term and the typing evidence is
`Nonempty`-truncated, and `sound` because it is literally `Quotient.sound`.

The content of this file is `Syn.denote_mk`: the interpretation of a typing
derivation in `Syn S` is the class of that derivation.
-/

namespace Isotope.LambdaSeq

open LocallyNameless

open Isotope.LambdaIter (Sig instrSrc instrTrg)

universe u

namespace Syn

variable {S : Sig.{u}}

section Carriers

variable {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}

/-- Instruction application on typable terms. -/
def Carrier.op (f : S.Instr) (a : Carrier S β (instrSrc f)) :
    Carrier S β (instrTrg f) :=
  ⟨.op f a.1, a.2.elim fun h => ⟨.op h⟩⟩

/-- Sequencing on typable terms. -/
def Carrier.let₁ (a : Carrier S β A) (b : Carrier S (β.snoc A) B) :
    Carrier S β B :=
  ⟨.let₁ a.1 b.1, a.2.elim fun ha => b.2.elim fun hb => ⟨.let₁ ha hb⟩⟩

end Carriers

/-- The operations of the syntactic model: every term former, lifted to the
quotient by the corresponding congruence rule of `Equiv`. -/
def ops (S : Sig.{u}) : Alg.Ops.{u, u} S where
  El β A := El S β A
  var i := mk (HasType.bv (i := i))
  op f := Quotient.map (Carrier.op f) (fun _ _ h => LocallyNameless.Equiv.op h)
  let₁ := Quotient.map₂ Carrier.let₁
    (fun _ _ ha _ _ hb => LocallyNameless.Equiv.let₁ ha hb)

/-- The interpretation of a typing derivation in the syntactic model is the
equivalence class of that derivation. -/
theorem ops_denote_eq_mk {n : Nat} {β : BoundCtx S.Ty n}
    {t : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr LambdaIter.Ctx.nil β t A) :
    (ops S).denote h = mk h := by
  induction h with
  | fv h => exact absurd h (by simp [LambdaIter.Ctx.lookup])
  | bv => rfl
  | op _ ih => rw [Alg.Ops.denote_op, ih]; rfl
  | let₁ _ _ iha ihb => rw [Alg.Ops.denote_let₁, iha, ihb]; rfl

end Syn

/-- **The syntactic model of lambda-seq.**  Typable terms over the signature
`S`, modulo the equational theory `Equiv`, with every term former acting by its
congruence rule.  `coh` and `sound` hold by construction; the theorem about
lambda-seq is `Syn.ops_denote_eq_mk`, and through it `Syn.isInitial`. -/
def Syn (S : Sig.{u}) : Alg.{u, u} S where
  toOps := Syn.ops S
  coh h k := by
    rw [Syn.ops_denote_eq_mk, Syn.ops_denote_eq_mk]; exact Syn.mk_congr h k
  sound h k e := by
    rw [Syn.ops_denote_eq_mk, Syn.ops_denote_eq_mk]
    exact Quotient.sound e

namespace Syn

variable {S : Sig.{u}}

/-- The carrier of the syntactic model is the quotient of typable terms. -/
@[simp] theorem El_eq (S : Sig.{u}) {n : Nat} (β : BoundCtx S.Ty n) (A : S.Ty) :
    (Syn S).El β A = El S β A := rfl

/-- The interpretation of a typing derivation in the syntactic model is its
equivalence class. -/
@[simp] theorem denote_mk {n : Nat} {β : BoundCtx S.Ty n}
    {t : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr LambdaIter.Ctx.nil β t A) : (Syn S).denote h = mk h :=
  ops_denote_eq_mk h

@[simp] theorem var_eq {n : Nat} {β : BoundCtx S.Ty n} (i : Fin n) :
    (Syn S).var (β := β) i = mk (HasType.bv (i := i)) := rfl

@[simp] theorem op_mk {n : Nat} {β : BoundCtx S.Ty n} {f : S.Instr}
    {a : Tm Empty S.Instr n}
    (ha : HasType S.Instr LambdaIter.Ctx.nil β a (instrSrc f)) :
    (Syn S).op f (mk ha) = mk (HasType.op ha) := rfl

@[simp] theorem let₁_mk {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    {a : Tm Empty S.Instr n} {b : Tm Empty S.Instr (n + 1)}
    (ha : HasType S.Instr LambdaIter.Ctx.nil β a A)
    (hb : HasType S.Instr LambdaIter.Ctx.nil (β.snoc A) b B) :
    (Syn S).let₁ (mk ha) (mk hb) = mk (HasType.let₁ ha hb) := rfl

end Syn

end Isotope.LambdaSeq
