import Isotope.LambdaIter.Models.Setoid

/-!
# The syntactic model of lambda-iter

`Syn S` is the quotient of the typable terms over the signature `S` by the
equational theory `Eqv`, organized as an object of `Alg S` — an algebra of the
equational presentation.

Every operation is a `Quotient` lift of the corresponding term former; each is
well defined because `Eqv` has a congruence constructor for that former.  In
particular `iter` is no harder than the others: `Eqv.iter` is a plain
congruence rule and `Pure` has no `iter` constructor, so no purity side
condition intrudes.

The two propositional fields of `Alg` are cheap here, and that is a fact about
the design rather than a theorem about the syntax:

* `coh` holds because a `Quotient` class depends only on the underlying term,
  and the typing evidence stored in the carrier is `Nonempty`-truncated;
* `sound` is literally `Quotient.sound`.

The content of this file is therefore `Syn.denote_mk`: the interpretation of a
typing derivation in `Syn S` is the class of that derivation.  Everything in
`Models/Initial.lean` rests on it.

## Honest boundary

This file gives `Syn S` as an *algebra of the presentation*.  It does **not**
build a premonoidal, distributive, or Elgot Freyd category out of the
quotient; see `Models/SynCategory.lean`, which delivers exactly the three
category laws and no more.
-/

namespace Isotope.LambdaIter

open LocallyNameless

universe u

namespace Syn

variable {S : Sig.{u}}

section Carriers

variable {n : Nat} {β : BoundCtx S.Ty n} {A B C : S.Ty}

/-- Instruction application on typable terms. -/
def Carrier.op (f : S.Instr) (a : Carrier S β (instrSrc f)) :
    Carrier S β (instrTrg f) :=
  ⟨.op f a.1, a.2.elim fun h => ⟨.op h⟩⟩

/-- Sequencing on typable terms. -/
def Carrier.let₁ (a : Carrier S β A) (b : Carrier S (β.snoc A) B) :
    Carrier S β B :=
  ⟨.let₁ a.1 b.1, a.2.elim fun ha => b.2.elim fun hb => ⟨.let₁ ha hb⟩⟩

/-- The unit value as a typable term. -/
def Carrier.unit (S : Sig.{u}) {n : Nat} (β : BoundCtx S.Ty n) :
    Carrier S β LambdaIter.unit := ⟨.unit, ⟨.unit⟩⟩

/-- Pairing on typable terms. -/
def Carrier.pair (a : Carrier S β A) (b : Carrier S β B) :
    Carrier S β (LambdaIter.tensor A B) :=
  ⟨.pair a.1 b.1, a.2.elim fun ha => b.2.elim fun hb => ⟨.pair ha hb⟩⟩

/-- Pair elimination on typable terms. -/
def Carrier.let₂ (a : Carrier S β (LambdaIter.tensor A B))
    (c : Carrier S ((β.snoc A).snoc B) C) : Carrier S β C :=
  ⟨.let₂ a.1 c.1, a.2.elim fun ha => c.2.elim fun hc => ⟨.let₂ ha hc⟩⟩

/-- Left injection on typable terms. -/
def Carrier.inl (a : Carrier S β A) : Carrier S β (LambdaIter.coprod A B) :=
  ⟨.inl a.1, a.2.elim fun ha => ⟨.inl ha⟩⟩

/-- Right injection on typable terms. -/
def Carrier.inr (b : Carrier S β B) : Carrier S β (LambdaIter.coprod A B) :=
  ⟨.inr b.1, b.2.elim fun hb => ⟨.inr hb⟩⟩

/-- Case analysis on typable terms. -/
def Carrier.case (e : Carrier S β (LambdaIter.coprod A B))
    (l : Carrier S (β.snoc A) C) (r : Carrier S (β.snoc B) C) :
    Carrier S β C :=
  ⟨.case e.1 l.1 r.1,
    e.2.elim fun he => l.2.elim fun hl => r.2.elim fun hr => ⟨.case he hl hr⟩⟩

/-- Empty elimination on typable terms. -/
def Carrier.abort (a : Carrier S β LambdaIter.empty) : Carrier S β C :=
  ⟨.abort a.1, a.2.elim fun ha => ⟨.abort ha⟩⟩

/-- Iteration on typable terms. -/
def Carrier.iter (a : Carrier S β A)
    (b : Carrier S (β.snoc A) (LambdaIter.coprod B A)) : Carrier S β B :=
  ⟨.iter a.1 b.1, a.2.elim fun ha => b.2.elim fun hb => ⟨.iter ha hb⟩⟩

end Carriers

/-- The operations of the syntactic model: every term former, lifted to the
quotient by the corresponding congruence rule of `Eqv`. -/
def ops (S : Sig.{u}) : Alg.Ops.{u, u} S where
  El β A := El S β A
  var i := mk (HasType.bv (ι := i))
  op f := Quotient.map (Carrier.op f) (fun _ _ h => Eqv.op h)
  let₁ := Quotient.map₂ Carrier.let₁ (fun _ _ ha _ _ hb => Eqv.let₁ ha hb)
  unit := mk HasType.unit
  pair := Quotient.map₂ Carrier.pair (fun _ _ ha _ _ hb => Eqv.pair ha hb)
  let₂ := Quotient.map₂ Carrier.let₂ (fun _ _ ha _ _ hc => Eqv.let₂ ha hc)
  inl := Quotient.map Carrier.inl (fun _ _ h => Eqv.inl h)
  inr := Quotient.map Carrier.inr (fun _ _ h => Eqv.inr h)
  case := map₃ Carrier.case
    (fun _ _ he _ _ hl _ _ hr => Eqv.case he hl hr)
  abort := Quotient.map Carrier.abort (fun _ _ h => Eqv.abort h)
  iter := Quotient.map₂ Carrier.iter (fun _ _ ha _ _ hb => Eqv.iter ha hb)

/-- The interpretation of a typing derivation in the syntactic model is the
equivalence class of that derivation.  This is the computation rule the whole
initiality argument rests on. -/
theorem ops_denote_eq_mk {n : Nat} {β : BoundCtx S.Ty n}
    {t : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr Ctx.nil β t A) : (ops S).denote h = mk h := by
  induction h with
  | fv h => exact absurd h (by simp [Ctx.lookup])
  | bv => rfl
  | op _ ih => rw [Alg.Ops.denote_op, ih]; rfl
  | let₁ _ _ iha ihb => rw [Alg.Ops.denote_let₁, iha, ihb]; rfl
  | unit => rfl
  | pair _ _ iha ihb => rw [Alg.Ops.denote_pair, iha, ihb]; rfl
  | let₂ _ _ iha ihc => rw [Alg.Ops.denote_let₂, iha, ihc]; rfl
  | inl _ ih => rw [Alg.Ops.denote_inl, ih]; rfl
  | inr _ ih => rw [Alg.Ops.denote_inr, ih]; rfl
  | case _ _ _ ihe ihl ihr => rw [Alg.Ops.denote_case, ihe, ihl, ihr]; rfl
  | abort _ ih => rw [Alg.Ops.denote_abort, ih]; rfl
  | iter _ _ iha ihb => rw [Alg.Ops.denote_iter, iha, ihb]; rfl

end Syn

/-- **The syntactic model.**  Typable terms over the signature `S`, modulo the
equational theory `Eqv`, with every term former acting by its congruence rule.

`coh` and `sound` are fields of `Alg`, and for `Syn` they hold for structural
reasons (proof irrelevance and `Quotient.sound` respectively) rather than as
theorems about lambda-iter.  The theorem about lambda-iter is
`Syn.ops_denote_eq_mk`, and through it `Syn.isInitial`. -/
def Syn (S : Sig.{u}) : Alg.{u, u} S where
  toOps := Syn.ops S
  coh h k := by
    rw [Syn.ops_denote_eq_mk, Syn.ops_denote_eq_mk]; exact Syn.mk_congr h k
  sound h k e := by rw [Syn.ops_denote_eq_mk, Syn.ops_denote_eq_mk]
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
    (h : HasType S.Instr Ctx.nil β t A) : (Syn S).denote h = mk h :=
  ops_denote_eq_mk h

/-! ### Computation rules

Each operation of `Syn S` computes on classes of derivations.  All of these
hold by `rfl`: they are the computation rules of `Quotient.map`. -/

@[simp] theorem var_eq {n : Nat} {β : BoundCtx S.Ty n} (i : Fin n) :
    (Syn S).var (β := β) i = mk (HasType.bv (ι := i)) := rfl

@[simp] theorem op_mk {n : Nat} {β : BoundCtx S.Ty n} {f : S.Instr}
    {a : Tm Empty S.Instr n} (ha : HasType S.Instr Ctx.nil β a (instrSrc f)) :
    (Syn S).op f (mk ha) = mk (HasType.op ha) := rfl

@[simp] theorem let₁_mk {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    {a : Tm Empty S.Instr n} {b : Tm Empty S.Instr (n + 1)}
    (ha : HasType S.Instr Ctx.nil β a A)
    (hb : HasType S.Instr Ctx.nil (β.snoc A) b B) :
    (Syn S).let₁ (mk ha) (mk hb) = mk (HasType.let₁ ha hb) := rfl

@[simp] theorem unit_eq {n : Nat} {β : BoundCtx S.Ty n} :
    (Syn S).unit (β := β) = mk HasType.unit := rfl

@[simp] theorem pair_mk {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    {a b : Tm Empty S.Instr n}
    (ha : HasType S.Instr Ctx.nil β a A) (hb : HasType S.Instr Ctx.nil β b B) :
    (Syn S).pair (mk ha) (mk hb) = mk (HasType.pair ha hb) := rfl

@[simp] theorem let₂_mk {n : Nat} {β : BoundCtx S.Ty n} {A B C : S.Ty}
    {a : Tm Empty S.Instr n} {c : Tm Empty S.Instr (n + 2)}
    (ha : HasType S.Instr Ctx.nil β a (LambdaIter.tensor A B))
    (hc : HasType S.Instr Ctx.nil ((β.snoc A).snoc B) c C) :
    (Syn S).let₂ (mk ha) (mk hc) = mk (HasType.let₂ ha hc) := rfl

@[simp] theorem inl_mk {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    {a : Tm Empty S.Instr n} (ha : HasType S.Instr Ctx.nil β a A) :
    (Syn S).inl (B := B) (mk ha) = mk (HasType.inl (B := B) ha) := rfl

@[simp] theorem inr_mk {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    {b : Tm Empty S.Instr n} (hb : HasType S.Instr Ctx.nil β b B) :
    (Syn S).inr (A := A) (mk hb) = mk (HasType.inr (A := A) hb) := rfl

@[simp] theorem case_mk {n : Nat} {β : BoundCtx S.Ty n} {A B C : S.Ty}
    {e : Tm Empty S.Instr n} {l r : Tm Empty S.Instr (n + 1)}
    (he : HasType S.Instr Ctx.nil β e (LambdaIter.coprod A B))
    (hl : HasType S.Instr Ctx.nil (β.snoc A) l C)
    (hr : HasType S.Instr Ctx.nil (β.snoc B) r C) :
    (Syn S).case (mk he) (mk hl) (mk hr) = mk (HasType.case he hl hr) := rfl

@[simp] theorem abort_mk {n : Nat} {β : BoundCtx S.Ty n} {C : S.Ty}
    {a : Tm Empty S.Instr n}
    (ha : HasType S.Instr Ctx.nil β a LambdaIter.empty) :
    (Syn S).abort (C := C) (mk ha) = mk (HasType.abort (C := C) ha) := rfl

@[simp] theorem iter_mk {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    {a : Tm Empty S.Instr n} {b : Tm Empty S.Instr (n + 1)}
    (ha : HasType S.Instr Ctx.nil β a A)
    (hb : HasType S.Instr Ctx.nil (β.snoc A) b (LambdaIter.coprod B A)) :
    (Syn S).iter (mk ha) (mk hb) = mk (HasType.iter ha hb) := rfl

end Syn


end Isotope.LambdaIter
