import Isotope.LambdaIter.Subtyping.Semantics.Models.Brookes
import Isotope.Elgot.Brookes.SeqCst.Op

/-!
# Compiling lambda-iter into Brookes's shared-variable parallel language

`Models/Brookes.lean` gives the *fine-grained* shared-memory signature — `read`
and `write` as separate instructions — and records, as an honest boundary, that
it is finer-grained than `Com`'s atomic assignment.  This file exhibits a
concrete separating pair, and then ships the signature for which a correct
compiler does exist.

## The granularity gap, as a theorem

`den_assign_le_readWrite` and `not_readWrite_le_den_assign` bracket the two
denotations:

* `den (x := y) ≤ read y >>= write x` — mumbling contracts the two steps of the
  composite into the one step of the atom;
* `read y >>= write x ≰ den (x := y)` — the composite contains the trace
  `[(μ, μ), (σ, [x ↦ μ y] σ)]` with `σ ≠ μ`, in which the environment replaced
  the whole store between the read and the write, so the value written is stale.

The separation is Brookes's own soundness invariant: every rely-guarantee pair
produced by an assignment lies in the preorder `UpdRel x y`, and stuttering and
mumbling preserve any preorder (`SeqCst.refines_compat`), whereas the witness
trace steps outside it.  Two distinct values suffice; `x` and `y` may coincide.
So `readWrite_ne_den_assign`.  Note precisely what this is and is not: it
separates *one* pair — the composite `read y >>= write x` against
`den (Com.assign x y)` — assuming `Val` has two distinct elements.  It is not
quantified over source terms, over target commands, or over compilers, and no
such general statement is proved here.  It is enough to motivate the coarse
signature below, and no more.

## The coarse signature

`CInstr` therefore takes whole commands as instructions: `skip`, `assign l e`,
and `test b`, the last valued in `1 + 1`.  All three are atoms of the trace
model, all three are impure, and the resulting `InstructionModel` is the second
effectful one in the development.

## The compilable fragment

`Compilable` is an inductive family over *typing derivations*, not over terms:
its five constructors carve out a fragment that compiles (maximality is not claimed).  Three
restrictions are load-bearing.

* **Result and binder types are all `unit`.**  No value is ever observed, which
  is what makes the target language — whose commands return nothing — adequate.
* **A control value of type `1 + 1` is never `let`-bound.**  The only scrutinee
  of a `case` is `test b` applied to `unit`, so the branch decision cannot be
  stored, duplicated or delayed; `denote_case_test` is exactly the point where
  this pays off, turning a `case` into Brookes's binary guarded choice.
* **Bare `unit` is not compilable.**  Its denotation is `pure ()`, whose traces
  include the empty one, while no command denotation does
  (`SeqCst.nil_not_mem_den`); `denote_unit_ne_den` states this as a theorem.
  `unit` still appears *inside* compilable derivations — as the argument of every
  instruction, as the seed of every loop, and in both injections of a loop body —
  where it is always composed with something that emits a step.

`Com.par` and `Com.await` are outside the image by construction, and
`exists_compilable`/`sequential_compile` show the image is *exactly* Brookes's
sequential sublanguage.

## The results

`den_compile` is preservation: `SeqCst.den (compile c) = denote h`, on the nose,
with no transport — `TyDen unit` is definitionally the `PUnit` of
`SeqCst.Comp Loc Val PUnit`.  The `while` clause is `SeqCst.iter_eq_star` of
`Brookes/SeqCst/Iter.lean`: the loop body assembled by `Compilable.wh` denotes
`SeqCst.whileBody` on the nose, so Brookes's Kleene star and the lambda-iter
`Elgot.iter` agree without any fixed-point reasoning here.

`lambdaIter_fullAbstraction` is the payoff, stated against the *operational*
contextual preorder of `Brookes/SeqCst/Op/`:

    denote h ≤ denote h'  ↔  Op.OpCtxLe (compile c) (compile c')

The right-hand side quantifies over *every* program context, including
`[−] ∥ C` and `await b then [−]`.  The source language is sequential; the
contexts are concurrent.  That is what makes the statement informative: an
Elgot-monad denotational semantics that never mentions interference already
decides everything a concurrent environment can observe about a sequential
program.

## Honest boundary

* **The fragment is narrow, deliberately.**  It has no free variables, no values
  of any type but `unit` and `1 + 1`, and no `let`-bound sums.  Widening it is
  not a matter of more proof: the granularity theorem above shows that any
  fragment whose instructions are finer than whole commands falls outside the
  reach of an *equality* with `SeqCst.den`.
* **Only the loop-free SSA leg is closed.**  `Models/Brookes/SSA.lean` proves it;  The bridge from lambda-iter to `LambdaSSA`
  regions is typing-only; see the closing note of this file.
* **Divergence is `⊥`.**  `den_wh_tt_skip` records that Brookes's model is
  partial-correctness: `while true do skip` denotes the empty set of traces, so
  the equational theory identifies it with every other diverging program.
-/

namespace Isotope.LambdaIter.Subtyping.Semantics

namespace BrookesModel

open Isotope.Elgot
open Isotope.Elgot.Brookes
open Isotope.LambdaIter (Ctx)
open Isotope.LambdaIter.LocallyNameless (Tm BoundCtx)
open Isotope.LambdaIter.Subtyping.LocallyNameless

universe u w

variable {Loc Val : Type u}

/-! ## Unfolding the denotation function -/

section Unfolding

variable {ν : Type w} [DecidableEq ν] {Φ : Type u}
  [LambdaIter.HasTy Φ (MemTy Loc Val)] [LambdaIter.HasEff Φ Eff]
  [InstructionModel Φ (MemTy Loc Val) Eff (SeqCst.Comp Loc Val)]
  {Γ : Ctx ν (MemTy Loc Val)} {n : Nat} {β : BoundCtx (MemTy Loc Val) n}

/-- `unit` denotes the trivial computation. -/
theorem denote_unit (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := SeqCst.Comp Loc Val) (ε := Eff)
        (HasType.unit (Φ := Φ) (Γ := Γ) (β := β)) γ ρ
      = (pure PUnit.unit
          : SeqCst.Comp Loc Val (TyDen (LambdaIter.unit : MemTy Loc Val))) := by
  simp only [denote]
  rfl

/-- `let` denotes a bind. -/
theorem denote_let₁ {a b : Tm ν Φ _} {A B : MemTy Loc Val}
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ (.snoc β A) b B)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := SeqCst.Comp Loc Val) (ε := Eff) (HasType.let₁ ha hb) γ ρ
      = denote (m := SeqCst.Comp Loc Val) (ε := Eff) ha γ ρ >>= fun x =>
          denote (m := SeqCst.Comp Loc Val) (ε := Eff) hb γ (ρ, x) := by
  simp only [denote]

/-- The coproduct comparison of the free type model is the identity. -/
@[simp] theorem coprodEquiv_apply {A B : MemTy Loc Val}
    (s : TyDen (LambdaIter.coprod A B)) : TypeModel.coprodEquiv A B s = s := rfl

/-- The unit comparison of the free type model is the identity. -/
@[simp] theorem unitEquiv_symm_apply (x : Unit) :
    (TypeModel.unitEquiv (τ := MemTy Loc Val)).symm x = PUnit.unit := rfl

/-- `iter` denotes an Elgot iterate of its body. -/
theorem denote_iter {a b : Tm ν Φ _} {A B : MemTy Loc Val}
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A))
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := SeqCst.Comp Loc Val) (ε := Eff) (HasType.iter ha hb) γ ρ
      = denote (m := SeqCst.Comp Loc Val) (ε := Eff) ha γ ρ >>= Elgot.iter (fun x =>
          denote (m := SeqCst.Comp Loc Val) (ε := Eff) hb γ (ρ, x) >>= fun s =>
            pure (TypeModel.coprodEquiv B A s)) := by
  simp only [denote]

/-- The coproduct comparison of the free type model is the identity, so the
final `pure` of an `iter` body is a no-op. -/
theorem bind_pure_coprodEquiv {A B : MemTy Loc Val}
    (x : SeqCst.Comp Loc Val (TyDen (LambdaIter.coprod A B))) :
    (x >>= fun s => pure (TypeModel.coprodEquiv A B s)) = x :=
  bind_pure_eq x

/-- `inl unit` denotes the left injection. -/
theorem denote_inl_unit {B : MemTy Loc Val} (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := SeqCst.Comp Loc Val) (ε := Eff)
        (HasType.inl (Φ := Φ) (Γ := Γ) (β := β) (B := B) HasType.unit) γ ρ
      = (pure (Sum.inl PUnit.unit) : SeqCst.Comp Loc Val
          (TyDen (LambdaIter.coprod (LambdaIter.unit : MemTy Loc Val) B))) := by
  simp only [denote]
  rw [pure_bind_eq]
  rfl

/-- `inr unit` denotes the right injection. -/
theorem denote_inr_unit {A : MemTy Loc Val} (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := SeqCst.Comp Loc Val) (ε := Eff)
        (HasType.inr (Φ := Φ) (Γ := Γ) (β := β) (A := A) HasType.unit) γ ρ
      = (pure (Sum.inr PUnit.unit) : SeqCst.Comp Loc Val
          (TyDen (LambdaIter.coprod A (LambdaIter.unit : MemTy Loc Val)))) := by
  simp only [denote]
  rw [pure_bind_eq]
  rfl

end Unfolding

/-! ## The coarse-atom signature -/

/-- The coarse instruction signature: whole assignments and whole tests. -/
inductive CInstr (Loc Val : Type u) : Type u where
  /-- Do nothing. -/
  | skip
  /-- Assign an expression to a location, atomically. -/
  | assign (l : Loc) (e : SeqCst.Exp Loc Val)
  /-- Test a boolean expression, atomically. -/
  | test (b : SeqCst.BExp Loc Val)

instance : LambdaIter.HasTy (CInstr Loc Val) (MemTy Loc Val) where
  src _ := .unit
  trg
    | .skip => .unit
    | .assign _ _ => .unit
    | .test _ => .coprod .unit .unit

/-- Every coarse instruction is impure. -/
instance : LambdaIter.HasEff (CInstr Loc Val) Eff where
  eff _ := Eff.impure

@[simp] theorem ceff_eq (f : CInstr Loc Val) :
    (LambdaIter.instrEff f : Eff) = Eff.impure := rfl

theorem ceff_ne_bot (f : CInstr Loc Val) : (LambdaIter.instrEff f : Eff) ≠ (⊥ : Eff) := by
  simp

/-- Every coarse instruction takes `unit` as its source. -/
theorem csrc_eq (f : CInstr Loc Val) :
    (LambdaIter.instrSrc f : MemTy Loc Val) = LambdaIter.unit := rfl

/-- The coarse denotations: `skip` and `assign` are Brookes atoms, and `test`
is his two-branch conditional guard, valued in `1 + 1`. -/
def cinstrDenote [DecidableEq Loc] [DecidableEq Val] : (f : CInstr Loc Val) →
    Free.interp (baseInterp (Loc := Loc) (Val := Val)) (LambdaIter.instrSrc f) →
      SeqCst.Comp Loc Val
        (Free.interp (baseInterp (Loc := Loc) (Val := Val)) (LambdaIter.instrTrg f))
  | .skip, _ => SeqCst.test (fun _ => true)
  | .assign l e, _ => SeqCst.atom (fun μ σ => σ = Function.update μ l (e.eval μ))
  | .test b, _ =>
      SeqCst.union2'
        (SeqCst.test b.eval >>= fun _ => pure (Sum.inl PUnit.unit))
        (SeqCst.test (SeqCst.BExp.neg b).eval >>= fun _ => pure (Sum.inr PUnit.unit))

/-- **The Brookes trace monad models the coarse signature.** -/
instance cinstructionModel [DecidableEq Loc] [DecidableEq Val] :
    InstructionModel (CInstr Loc Val) (MemTy Loc Val) Eff (SeqCst.Comp Loc Val) where
  denote f := cinstrDenote f
  denotePure f hf := absurd hf (ceff_ne_bot f)
  denote_pure f hf := absurd hf (ceff_ne_bot f)

section CDenote

variable [DecidableEq Loc] [DecidableEq Val]

@[simp] theorem cinstructionModel_denote (f : CInstr Loc Val) :
    InstructionModel.denote (Φ := CInstr Loc Val) (τ := MemTy Loc Val)
      (m := SeqCst.Comp Loc Val) Eff f = cinstrDenote f := rfl

/-- `denote_unit`, restated at the index `instrSrc f` in which it occurs inside
an instruction application. -/
theorem denote_unit_src (f : CInstr Loc Val) {n : Nat}
    {β : BoundCtx (MemTy Loc Val) n} (ρ : BoundDen β) :
    denote (m := SeqCst.Comp Loc Val) (ε := Eff) (A := LambdaIter.instrSrc f)
        (HasType.unit (Φ := CInstr Loc Val) (Γ := (.nil : Ctx Empty (MemTy Loc Val)))
          (β := β))
        PUnit.unit ρ
      = (pure PUnit.unit
          : SeqCst.Comp Loc Val (TyDen (LambdaIter.instrSrc f))) :=
  denote_unit _ _

/-- An instruction applied to `unit` denotes that instruction. -/
theorem denote_cop (f : CInstr Loc Val) {n : Nat}
    {β : BoundCtx (MemTy Loc Val) n} (ρ : BoundDen β) :
    denote (m := SeqCst.Comp Loc Val) (ε := Eff)
        (HasType.op (Φ := CInstr Loc Val) (Γ := (.nil : Ctx Empty (MemTy Loc Val)))
          (β := β) (f := f) HasType.unit) PUnit.unit ρ
      = cinstrDenote f PUnit.unit := by
  simp only [denote]
  rw [denote_unit_src f ρ]
  exact pure_bind_eq _ _

/-- `skip` applied to `unit`, at the result index in which it occurs. -/
theorem denote_cskip {n : Nat} {β : BoundCtx (MemTy Loc Val) n} (ρ : BoundDen β) :
    denote (m := SeqCst.Comp Loc Val) (ε := Eff) (A := LambdaIter.unit)
        (HasType.op (Φ := CInstr Loc Val) (Γ := (.nil : Ctx Empty (MemTy Loc Val)))
          (β := β) (f := CInstr.skip) HasType.unit) PUnit.unit ρ
      = (SeqCst.test (fun _ => true) : SeqCst.Comp Loc Val PUnit) :=
  denote_cop CInstr.skip ρ

/-- `assign` applied to `unit`, at the result index in which it occurs. -/
theorem denote_cassign (l : Loc) (e : SeqCst.Exp Loc Val) {n : Nat}
    {β : BoundCtx (MemTy Loc Val) n} (ρ : BoundDen β) :
    denote (m := SeqCst.Comp Loc Val) (ε := Eff) (A := LambdaIter.unit)
        (HasType.op (Φ := CInstr Loc Val) (Γ := (.nil : Ctx Empty (MemTy Loc Val)))
          (β := β) (f := CInstr.assign l e) HasType.unit) PUnit.unit ρ
      = (SeqCst.atom (fun μ σ => σ = Function.update μ l (e.eval μ))
          : SeqCst.Comp Loc Val PUnit) :=
  denote_cop (CInstr.assign l e) ρ

/-- `test` applied to `unit`, at the result index in which it occurs. -/
theorem denote_ctest (b : SeqCst.BExp Loc Val) {n : Nat}
    {β : BoundCtx (MemTy Loc Val) n} (ρ : BoundDen β) :
    denote (m := SeqCst.Comp Loc Val) (ε := Eff)
        (A := LambdaIter.coprod LambdaIter.unit LambdaIter.unit)
        (HasType.op (Φ := CInstr Loc Val) (Γ := (.nil : Ctx Empty (MemTy Loc Val)))
          (β := β) (f := CInstr.test b) HasType.unit) PUnit.unit ρ
      = SeqCst.union2'
          (A := TyDen (LambdaIter.coprod (LambdaIter.unit : MemTy Loc Val) LambdaIter.unit))
          (SeqCst.test b.eval >>= fun _ => pure (Sum.inl PUnit.unit))
          (SeqCst.test (SeqCst.BExp.neg b).eval >>= fun _ => pure (Sum.inr PUnit.unit)) :=
  denote_cop (CInstr.test b) ρ

/-- **The conditional clause.**  A `case` whose scrutinee is a coarse `test`
applied to `unit` denotes Brookes's binary guarded choice.  This is where the
coarse signature pays off: the scrutinee never becomes a value that could be
let-bound, so the two branches are guarded by complementary atomic tests. -/
theorem denote_case_test (b : SeqCst.BExp Loc Val) {n : Nat}
    {β : BoundCtx (MemTy Loc Val) n} {C : MemTy Loc Val}
    {l r : Tm Empty (CInstr Loc Val) (n + 1)}
    (hl : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val))
      (.snoc β LambdaIter.unit) l C)
    (hr : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val))
      (.snoc β LambdaIter.unit) r C)
    (ρ : BoundDen β) :
    denote (m := SeqCst.Comp Loc Val) (ε := Eff)
        (HasType.case (A := LambdaIter.unit) (B := LambdaIter.unit)
          (HasType.op (f := CInstr.test b) HasType.unit) hl hr) PUnit.unit ρ
      = SeqCst.union2'
          (SeqCst.test b.eval >>= fun _ =>
            denote (m := SeqCst.Comp Loc Val) (ε := Eff) hl PUnit.unit (ρ, PUnit.unit))
          (SeqCst.test (SeqCst.BExp.neg b).eval >>= fun _ =>
            denote (m := SeqCst.Comp Loc Val) (ε := Eff) hr PUnit.unit (ρ, PUnit.unit)) := by
  rw [denote, denote_ctest]
  simp only [SeqCst.union2'_bind, bind_assoc_eq, pure_bind_eq, coprodEquiv_apply]

end CDenote

/-! ## The compilable fragment -/

/-- **The compilable fragment.**  A derivation is compilable when it is built
from exactly five shapes: an atomic `skip` or `assign`; a `let` (sequential
composition); a `case` on a coarse `test` (conditional); and an `iter` whose
seed is `unit` and whose body is a `case` on a coarse `test` that either runs a
compilable body and asks to go round again, or stops (a `while` loop).

Three restrictions are load-bearing.  Every slot is `unit`, so no value is ever
observed.  A control value of type `1 + 1` is never `let`-bound: the only
scrutinee of a `case` is a `test` applied to `unit`, so the branch decision
cannot be stored and re-used.  And the bare term `unit` is *not* compilable: its
denotation is `pure ()`, whose only trace is the empty one, and no command
denotation contains the empty trace (`SeqCst.nil_not_mem_den`). -/
inductive Compilable : {n : Nat} → {β : BoundCtx (MemTy Loc Val) n} →
    {t : Tm Empty (CInstr Loc Val) n} →
    HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β t LambdaIter.unit → Type u
  /-- `skip`. -/
  | skip {n : Nat} {β : BoundCtx (MemTy Loc Val) n} :
      Compilable (HasType.op (Φ := CInstr Loc Val)
        (Γ := (.nil : Ctx Empty (MemTy Loc Val))) (β := β) (f := CInstr.skip) HasType.unit)
  /-- `l := e`. -/
  | assign {n : Nat} {β : BoundCtx (MemTy Loc Val) n} (l : Loc) (e : SeqCst.Exp Loc Val) :
      Compilable (HasType.op (Φ := CInstr Loc Val)
        (Γ := (.nil : Ctx Empty (MemTy Loc Val))) (β := β)
        (f := CInstr.assign l e) HasType.unit)
  /-- `C₁ ; C₂`, as a `let`. -/
  | seq {n : Nat} {β : BoundCtx (MemTy Loc Val) n}
      {a : Tm Empty (CInstr Loc Val) n} {b : Tm Empty (CInstr Loc Val) (n + 1)}
      {ha : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β a LambdaIter.unit}
      {hb : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val))
        (.snoc β LambdaIter.unit) b LambdaIter.unit}
      (ca : Compilable ha) (cb : Compilable hb) :
      Compilable (HasType.let₁ (A := LambdaIter.unit) (B := LambdaIter.unit) ha hb)
  /-- `if b then C₁ else C₂`, as a `case` on a coarse test. -/
  | ite {n : Nat} {β : BoundCtx (MemTy Loc Val) n} (b : SeqCst.BExp Loc Val)
      {l r : Tm Empty (CInstr Loc Val) (n + 1)}
      {hl : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val))
        (.snoc β LambdaIter.unit) l LambdaIter.unit}
      {hr : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val))
        (.snoc β LambdaIter.unit) r LambdaIter.unit}
      (cl : Compilable hl) (cr : Compilable hr) :
      Compilable (HasType.case (A := LambdaIter.unit) (B := LambdaIter.unit)
        (C := LambdaIter.unit)
        (HasType.op (Φ := CInstr Loc Val) (Γ := (.nil : Ctx Empty (MemTy Loc Val)))
          (β := β) (f := CInstr.test b) HasType.unit) hl hr)
  /-- `while b do C`, as an `iter` on a coarse test. -/
  | wh {n : Nat} {β : BoundCtx (MemTy Loc Val) n} (b : SeqCst.BExp Loc Val)
      {body : Tm Empty (CInstr Loc Val) (n + 2)}
      {hbody : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val))
        (.snoc (.snoc β LambdaIter.unit) LambdaIter.unit) body LambdaIter.unit}
      (cb : Compilable hbody) :
      Compilable (β := β)
        (HasType.iter (A := LambdaIter.unit) (B := LambdaIter.unit) HasType.unit
          (HasType.case (A := LambdaIter.unit) (B := LambdaIter.unit)
            (C := LambdaIter.coprod LambdaIter.unit LambdaIter.unit)
            (HasType.op (Φ := CInstr Loc Val) (Γ := (.nil : Ctx Empty (MemTy Loc Val)))
              (β := .snoc β LambdaIter.unit) (f := CInstr.test b) HasType.unit)
            (HasType.let₁ (A := LambdaIter.unit)
              (B := LambdaIter.coprod LambdaIter.unit LambdaIter.unit)
              hbody (HasType.inr (A := LambdaIter.unit) HasType.unit))
            (HasType.inl (B := LambdaIter.unit) HasType.unit)))

/-- **The compiler.** -/
def compile : {n : Nat} → {β : BoundCtx (MemTy Loc Val) n} →
    {t : Tm Empty (CInstr Loc Val) n} →
    {h : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β t LambdaIter.unit} →
    Compilable h → SeqCst.Com Loc Val
  | _, _, _, _, .skip => .skip
  | _, _, _, _, .assign l e => .assign l e
  | _, _, _, _, .seq ca cb => .seq (compile ca) (compile cb)
  | _, _, _, _, .ite b cl cr => .ite b (compile cl) (compile cr)
  | _, _, _, _, .wh b cb => .wh b (compile cb)

@[simp] theorem compile_skip {n : Nat} {β : BoundCtx (MemTy Loc Val) n} :
    compile (Compilable.skip (β := β)) = SeqCst.Com.skip := rfl

@[simp] theorem compile_assign {n : Nat} {β : BoundCtx (MemTy Loc Val) n}
    (l : Loc) (e : SeqCst.Exp Loc Val) :
    compile (Compilable.assign (β := β) l e) = SeqCst.Com.assign l e := rfl

@[simp] theorem compile_seq {n : Nat} {β : BoundCtx (MemTy Loc Val) n}
    {a : Tm Empty (CInstr Loc Val) n} {b : Tm Empty (CInstr Loc Val) (n + 1)}
    {ha : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β a LambdaIter.unit}
    {hb : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val))
      (.snoc β LambdaIter.unit) b LambdaIter.unit}
    (ca : Compilable ha) (cb : Compilable hb) :
    compile (Compilable.seq ca cb) = SeqCst.Com.seq (compile ca) (compile cb) := rfl

@[simp] theorem compile_ite {n : Nat} {β : BoundCtx (MemTy Loc Val) n}
    (b : SeqCst.BExp Loc Val) {l r : Tm Empty (CInstr Loc Val) (n + 1)}
    {hl : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val))
      (.snoc β LambdaIter.unit) l LambdaIter.unit}
    {hr : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val))
      (.snoc β LambdaIter.unit) r LambdaIter.unit}
    (cl : Compilable hl) (cr : Compilable hr) :
    compile (Compilable.ite b cl cr) = SeqCst.Com.ite b (compile cl) (compile cr) := rfl

@[simp] theorem compile_wh {n : Nat} {β : BoundCtx (MemTy Loc Val) n}
    (b : SeqCst.BExp Loc Val) {body : Tm Empty (CInstr Loc Val) (n + 2)}
    {hbody : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val))
      (.snoc (.snoc β LambdaIter.unit) LambdaIter.unit) body LambdaIter.unit}
    (cb : Compilable hbody) :
    compile (Compilable.wh b cb) = SeqCst.Com.wh b (compile cb) := rfl

/-- `union2'` at the interpretation of `unit` is `union2`. -/
theorem union2'_unit (x y : SeqCst.Comp Loc Val (TyDen (LambdaIter.unit : MemTy Loc Val))) :
    SeqCst.union2' x y = SeqCst.union2 x y := rfl

/-! ## Preservation -/

section Preservation

variable [DecidableEq Loc] [DecidableEq Val]

/-- **Preservation.**  The Brookes trace denotation of the compiled command is
the lambda-iter denotation of the source derivation, on the nose. -/
theorem den_compile : {n : Nat} → {β : BoundCtx (MemTy Loc Val) n} →
    {t : Tm Empty (CInstr Loc Val) n} →
    {h : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β t LambdaIter.unit} →
    (c : Compilable h) → (ρ : BoundDen β) →
    SeqCst.den (compile c)
      = denote (m := SeqCst.Comp Loc Val) (ε := Eff) h PUnit.unit ρ := by
  intro n β t h c
  induction c with
  | skip =>
    intro ρ
    rw [compile_skip, SeqCst.den_skip, denote_cskip]
  | assign l e =>
    intro ρ
    rw [compile_assign, SeqCst.den_assign, denote_cassign]
  | seq ca cb iha ihb =>
    intro ρ
    rw [compile_seq, SeqCst.den_seq, denote_let₁, iha ρ]
    simp only [← ihb]
    rfl
  | ite b cl cr ihl ihr =>
    intro ρ
    rw [compile_ite, SeqCst.den_ite, denote_case_test, union2'_unit]
    simp only [← ihl, ← ihr]
    rfl
  | wh b cb ihb =>
    intro ρ
    rw [compile_wh, SeqCst.den_wh_eq_iter, denote_iter, denote_unit]
    simp only [pure_bind_eq]
    congr 1
    funext x
    rw [bind_pure_coprodEquiv, denote_case_test, denote_let₁]
    simp only [denote_inr_unit, denote_inl_unit, ← ihb, ← bind_assoc_eq]
    rfl

/-- **Bare `unit` is not compilable, and cannot be.**  Its denotation is
`pure ()`, whose traces include the empty one, and no command denotation
contains the empty trace. -/
theorem denote_unit_ne_den {n : Nat} {β : BoundCtx (MemTy Loc Val) n}
    (ρ : BoundDen β) (C : SeqCst.Com Loc Val) :
    denote (m := SeqCst.Comp Loc Val) (ε := Eff)
        (HasType.unit (Φ := CInstr Loc Val) (Γ := (.nil : Ctx Empty (MemTy Loc Val)))
          (β := β)) PUnit.unit ρ ≠ SeqCst.den C := by
  intro h
  refine SeqCst.nil_not_mem_den C PUnit.unit ?_
  rw [← h, denote_unit]
  exact mem_pure _

/-- A diverging loop denotes the empty set of traces: Brookes's model is
partial-correctness, and `⊥` is divergence. -/
theorem den_wh_tt_skip :
    SeqCst.den (SeqCst.Com.wh SeqCst.BExp.tt SeqCst.Com.skip : SeqCst.Com Loc Val) = ⊥ := by
  have hff : (SeqCst.test (SeqCst.BExp.neg SeqCst.BExp.tt).eval
      : SeqCst.Comp Loc Val PUnit) = ⊥ := by
    rw [eq_bot_iff_forall]
    intro t a ht
    rw [SeqCst.test, SeqCst.mem_atom_iff] at ht
    obtain ⟨μ, σ, hR, _⟩ := ht
    exact absurd hR.1 (by simp [SeqCst.BExp.eval])
  rw [SeqCst.den_wh, hff, bind_bot]

end Preservation

/-! ## The image of the compiler -/

/-- The sequential sublanguage of Brookes's command syntax: no `∥`, no
`await`.  Concurrency lives in the *contexts*, not in the source language. -/
inductive Sequential : SeqCst.Com Loc Val → Prop
  /-- `skip` is sequential. -/
  | skip : Sequential .skip
  /-- Assignments are sequential. -/
  | assign (l : Loc) (e : SeqCst.Exp Loc Val) : Sequential (.assign l e)
  /-- Sequential composition of sequential commands. -/
  | seq {C₁ C₂ : SeqCst.Com Loc Val} :
      Sequential C₁ → Sequential C₂ → Sequential (.seq C₁ C₂)
  /-- Conditionals with sequential branches. -/
  | ite {b : SeqCst.BExp Loc Val} {C₁ C₂ : SeqCst.Com Loc Val} :
      Sequential C₁ → Sequential C₂ → Sequential (.ite b C₁ C₂)
  /-- Loops with a sequential body. -/
  | wh {b : SeqCst.BExp Loc Val} {C : SeqCst.Com Loc Val} :
      Sequential C → Sequential (.wh b C)

/-- **The compilable fragment covers Brookes's whole sequential sublanguage.**
Every `∥`-free, `await`-free command is the compilation of a lambda-iter
derivation, in every bound context. -/
theorem exists_compilable {C : SeqCst.Com Loc Val} (hC : Sequential C) :
    ∀ {n : Nat} (β : BoundCtx (MemTy Loc Val) n),
      ∃ (t : Tm Empty (CInstr Loc Val) n)
        (h : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β t LambdaIter.unit)
        (c : Compilable h), compile c = C := by
  induction hC with
  | skip => exact fun β => ⟨_, _, Compilable.skip (β := β), rfl⟩
  | assign l e => exact fun β => ⟨_, _, Compilable.assign (β := β) l e, rfl⟩
  | seq _ _ ih₁ ih₂ =>
    intro n β
    obtain ⟨_, _, c₁, h₁⟩ := ih₁ β
    obtain ⟨_, _, c₂, h₂⟩ := ih₂ (.snoc β LambdaIter.unit)
    exact ⟨_, _, Compilable.seq c₁ c₂, by rw [compile_seq, h₁, h₂]⟩
  | ite _ _ ih₁ ih₂ =>
    intro n β
    obtain ⟨_, _, c₁, h₁⟩ := ih₁ (.snoc β LambdaIter.unit)
    obtain ⟨_, _, c₂, h₂⟩ := ih₂ (.snoc β LambdaIter.unit)
    exact ⟨_, _, Compilable.ite _ c₁ c₂, by rw [compile_ite, h₁, h₂]⟩
  | wh _ ih =>
    intro n β
    obtain ⟨_, _, c, h⟩ := ih (.snoc (.snoc β LambdaIter.unit) LambdaIter.unit)
    exact ⟨_, _, Compilable.wh _ c, by rw [compile_wh, h]⟩

/-- Conversely, every compiled command is sequential. -/
theorem sequential_compile : {n : Nat} → {β : BoundCtx (MemTy Loc Val) n} →
    {t : Tm Empty (CInstr Loc Val) n} →
    {h : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β t LambdaIter.unit} →
    (c : Compilable h) → Sequential (compile c) := by
  intro n β t h c
  induction c with
  | skip => exact .skip
  | assign l e => exact .assign l e
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ite _ _ _ ih₁ ih₂ => exact .ite ih₁ ih₂
  | wh _ _ ih => exact .wh ih

/-! ## Full abstraction for the compilable fragment -/

section FullAbstraction

variable [DecidableEq Loc] [DecidableEq Val]

/-- **Adequacy for the compilable fragment.**  The stores related by the source
denotation are exactly those related by terminating executions of the small-step
machine on the compiled command. -/
theorem opObs_compile {n : Nat} {β : BoundCtx (MemTy Loc Val) n}
    {t : Tm Empty (CInstr Loc Val) n}
    {h : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β t LambdaIter.unit}
    (c : Compilable h) (ρ : BoundDen β) (μ σ : SeqCst.Store Loc Val) :
    SeqCst.Op.opObs (compile c) μ σ
      ↔ SeqCst.obs (denote (m := SeqCst.Comp Loc Val) (ε := Eff) h PUnit.unit ρ) μ σ := by
  rw [← den_compile c ρ]
  exact (SeqCst.Op.obs_iff_opObs (compile c) μ σ).symm

/- `Fintype Loc` does not appear in the statements below, only in the proof of
the completeness half they inherit from `SeqCst.fullAbstraction`, where it is
what makes the separating contexts definable. -/
set_option linter.unusedFintypeInType false

/-- **The payoff.**  For the compilable fragment, trace inclusion of lambda-iter
denotations is *exactly* Brookes's substitutive preorder on the compiled
commands, stated operationally: `compile c` may be replaced by `compile c'` in
every program context — including concurrent ones, with `∥` and `await` — without
adding terminating executions of the small-step machine.

The source language is sequential; the contexts are concurrent.  That is what
makes the equivalence informative.  The interference structure is supplied
entirely by the monad and the instruction model -- `SeqCst.Comp` is
stutter/mumble-closed rely-guarantee trace sets, and every `CInstr` denotes a
`SeqCst.atom` or `SeqCst.test`; the *term* semantics `denote` contributes no
construct that mentions interference, and the theorem says that suffices. -/
theorem lambdaIter_fullAbstraction [Fintype Loc] {n : Nat}
    {β : BoundCtx (MemTy Loc Val) n} {t t' : Tm Empty (CInstr Loc Val) n}
    {h : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β t LambdaIter.unit}
    {h' : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β t' LambdaIter.unit}
    (c : Compilable h) (c' : Compilable h') (ρ : BoundDen β) :
    denote (m := SeqCst.Comp Loc Val) (ε := Eff) h PUnit.unit ρ
        ≤ denote (m := SeqCst.Comp Loc Val) (ε := Eff) h' PUnit.unit ρ
      ↔ SeqCst.Op.OpCtxLe (compile c) (compile c') := by
  rw [← den_compile c ρ, ← den_compile c' ρ,
    ← SeqCst.Op.opDen_eq_den (compile c), ← SeqCst.Op.opDen_eq_den (compile c')]
  exact SeqCst.Op.opFullAbstraction

/-- **The payoff, equationally.** -/
theorem lambdaIter_fullAbstraction_eq [Fintype Loc] {n : Nat}
    {β : BoundCtx (MemTy Loc Val) n} {t t' : Tm Empty (CInstr Loc Val) n}
    {h : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β t LambdaIter.unit}
    {h' : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β t' LambdaIter.unit}
    (c : Compilable h) (c' : Compilable h') (ρ : BoundDen β) :
    denote (m := SeqCst.Comp Loc Val) (ε := Eff) h PUnit.unit ρ
        = denote (m := SeqCst.Comp Loc Val) (ε := Eff) h' PUnit.unit ρ
      ↔ SeqCst.Op.OpCtxEq (compile c) (compile c') := by
  rw [← den_compile c ρ, ← den_compile c' ρ,
    ← SeqCst.Op.opDen_eq_den (compile c), ← SeqCst.Op.opDen_eq_den (compile c')]
  exact SeqCst.Op.opFullAbstraction_eq

end FullAbstraction

/-! ## The granularity gap -/

section Granularity

variable [DecidableEq Loc]

/-- The preorder that separates a two-step read-then-write from an atomic
assignment: a state may be left alone, or updated at `x` with the value it
currently holds at `y`. -/
def UpdRel (x y : Loc) : SeqCst.Store Loc Val → SeqCst.Store Loc Val → Prop :=
  fun a b => b = a ∨ b = Function.update a x (a y)

theorem updRel_refl (x y : Loc) (a : SeqCst.Store Loc Val) : UpdRel x y a a := Or.inl rfl

/-- Reading `y` and writing it to `x` is idempotent, so `UpdRel` is transitive.
This holds whether or not `x = y`. -/
theorem updRel_trans (x y : Loc) (a b d : SeqCst.Store Loc Val)
    (h₁ : UpdRel x y a b) (h₂ : UpdRel x y b d) : UpdRel x y a d := by
  have key : Function.update a x (a y) y = a y := by
    simp [Function.update_apply]
  rcases h₁ with rfl | rfl
  · exact h₂
  · rcases h₂ with rfl | rfl
    · exact Or.inr rfl
    · refine Or.inr ?_
      rw [key, Function.update_idem]

/-- **The atomic assignment refines the read-then-write composite.**  Mumbling
contracts the two steps into one. -/
theorem den_assign_le_readWrite [DecidableEq Val] (x y : Loc) :
    SeqCst.den (SeqCst.Com.assign x (SeqCst.Exp.var y : SeqCst.Exp Loc Val))
      ≤ (SeqCst.read (Val := Val) y >>= fun v => SeqCst.write x v) := by
  rw [SeqCst.den_assign]
  apply le_of_mem
  intro t a ht
  obtain ⟨μ, σ, hR, href⟩ := SeqCst.mem_atom_iff.1 ht
  rw [mem_bind_iff]
  refine ⟨μ y, [(μ, μ)], [(μ, σ)], SeqCst.mem_read y μ, ?_, ?_⟩
  · rw [hR]
    exact SeqCst.mem_write x (μ y) μ
  · exact Relation.ReflTransGen.head (SeqCst.Step.mumble μ μ σ []) href

/-- **The read-then-write composite does *not* refine the atomic assignment.**
The witness is the trace `[(μ, μ), (σ, [x ↦ μ y] σ)]` with `σ ≠ μ`: the
environment changed the whole store between the read and the write, so the
value written is stale.  No refinement of a single atomic step admits such a
trace, because every atomic step of an assignment stays inside `UpdRel`, and
stuttering and mumbling preserve `UpdRel` (`SeqCst.refines_compat`).

This needs only two distinct values; `x` and `y` may even coincide. -/
theorem not_readWrite_le_den_assign [DecidableEq Val] (x y : Loc) {v₀ v₁ : Val}
    (hv : v₀ ≠ v₁) :
    ¬ ((SeqCst.read (Val := Val) y >>= fun v => SeqCst.write x v)
        ≤ SeqCst.den (SeqCst.Com.assign x (SeqCst.Exp.var y : SeqCst.Exp Loc Val))) := by
  intro hle
  have hmem :
      (([((fun _ => v₀ : SeqCst.Store Loc Val), (fun _ => v₀ : SeqCst.Store Loc Val)),
          ((fun _ => v₁ : SeqCst.Store Loc Val),
            Function.update (fun _ => v₁ : SeqCst.Store Loc Val) x v₀)]
        : Trace (SeqCst.Store Loc Val × SeqCst.Store Loc Val)), PUnit.unit)
      ∈ (SeqCst.read (Val := Val) y >>= fun v => SeqCst.write x v) :=
    mem_bind _ _ (SeqCst.mem_read y (fun _ => v₀))
      (SeqCst.mem_write x v₀ (fun _ => v₁))
  have hmem' := le_def.1 hle _ _ hmem
  rw [SeqCst.den_assign, SeqCst.mem_atom_iff] at hmem'
  obtain ⟨μ, σ, hR, href⟩ := hmem'
  have hcompat := SeqCst.refines_compat (r := UpdRel x y) (updRel_refl x y)
    (updRel_trans x y) href (by
      intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact Or.inr hR)
  have hsecond := hcompat ((fun _ => v₁ : SeqCst.Store Loc Val),
    Function.update (fun _ => v₁ : SeqCst.Store Loc Val) x v₀) (by simp)
  rcases hsecond with h | h
  · exact hv (by simpa using congrFun h x)
  · exact hv (by simpa using congrFun h x)

/-- **The granularity gap, as an equation that fails.**  The fine-grained
signature of `Models/Brookes.lean` cannot compile to `Com`: the composite
`read y; write x` is *strictly* coarser than `x := y`. -/
theorem readWrite_ne_den_assign [DecidableEq Val] (x y : Loc) {v₀ v₁ : Val}
    (hv : v₀ ≠ v₁) :
    (SeqCst.read (Val := Val) y >>= fun v => SeqCst.write x v)
      ≠ SeqCst.den (SeqCst.Com.assign x (SeqCst.Exp.var y : SeqCst.Exp Loc Val)) := by
  intro h
  exact not_readWrite_le_den_assign x y hv (le_of_eq h)

/-- The same separation, spelled out for the fine-grained instruction
denotations of `Models/Brookes.lean`. -/
theorem instrDenote_readWrite_ne_den_assign [DecidableEq Val] (x y : Loc) {v₀ v₁ : Val}
    (hv : v₀ ≠ v₁) :
    (instrDenote (Loc := Loc) (Val := Val) Instr.read y
        >>= fun v => instrDenote (Loc := Loc) (Val := Val) Instr.write (x, v))
      ≠ SeqCst.den (SeqCst.Com.assign x (SeqCst.Exp.var y : SeqCst.Exp Loc Val)) :=
  readWrite_ne_den_assign (Loc := Loc) (Val := Val) x y hv

end Granularity

/-! ## Not proved here: the SSA leg

`Isotope/LambdaSSA/Translation/Compile.lean` compiles a lambda-iter term to an
SSA region and proves it *well typed* (`compile_hasType`), but there is no
semantic counterpart: `ANF.ToSSA` has `program_hasType` and nothing else, so the
chain

  `denote h`  =  `Direct.denoteProgram (elaborate_hasType h)`  (proved:
  `Direct.denote_elaborate`, `Direct.denoteProgram_toLambdaIter`)
  =  the SSA region's denotation  (**missing**)

breaks at its last link.  The missing lemma is

  `ANF.ToSSA.program_denotes :
     RegionDenotes ε (program_hasType h hout)
       (fun ρ => LambdaIter.Semantics.denote h.toLambdaIter ⋆ (envToBound ρ)
                   >>= fun a => pure (labelInject result hout a))`

and inside it the two-block-CFG case, in which `ANF.iter` compiles to a `cfg`
with a `case (var 0)` dispatcher and a `renameVars` shift that must be contracted
back to a single `Elgot.iter` by uniformity and codiagonal.

Two further obstacles are structural rather than a matter of more proof.
`Region.denote` is a `Classical.choice` pick out of `regionDenotes_exists`, and
`Monadic.RegionTypingCoherent` — the assumption that makes it unique — is
documented in `Semantics/Monadic/Coherence.lean` as *not* derivable from the raw
typing relation, so the honest statement is about `RegionDenotes`, not about an
equation between `Region.denote`s.  And `LabelDen L` is a `Sigma` colimit, not a
nested `Sum`, so even at `L = [unit]` a comparison with `SeqCst.Comp Loc Val
PUnit` needs an inverse for `labelInject 0` that does not exist yet.

Compiling *out* of SSA is further away still: `Translation/FromSSA.lean` returns
`Nonempty` typing derivations rather than derivations, so `denote` cannot even be
applied to its output, and its CFG clause emits a `case` on a *stored* sum, which
is outside the fragment `Compilable` can describe. -/

end BrookesModel

end Isotope.LambdaIter.Subtyping.Semantics
