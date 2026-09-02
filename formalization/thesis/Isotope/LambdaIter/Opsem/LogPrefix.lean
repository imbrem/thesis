import Isotope.LambdaIter.Opsem.LogAdequacy

/-!
# Reachability: observing the log a run *passes through*

`Isotope.LambdaIter.Opsem.LogAdequacy` observes a program by the log it *ends*
with, and proves that this sees exactly what a state model sees
(`obsEq_iff_termLogObsEq`).  That is not an accident of the proof: `Diverges` is
the *absence* of an `Eval`, so `TermObsEq` is literally `Observation.ObsEq`
(`obsEq_iff_termObsEq`), and making the state the log prefix so far changes
nothing by itself.  A run that never returns has no final log, exactly as it has
no final state, so `TermLogObsEq` still identifies the standing counterexample
`Counterexample.loop` and `Counterexample.loopF`.

What a divergent run *does* is visible only in the logs it passes through on the
way.  This file therefore defines **reachability**:

* `IterReach hb γ ρ x s x' s'` — the loop with body `hb`, entered with
  loop-carried value `x` in state `s`, can be at the top of a later iteration
  with value `x'` in state `s'`.  Unlike `IterEval` it does **not** require the
  loop to terminate.
* `Reach h γ ρ s s'` — evaluating the term typed by `h` from state `s`, the
  machine can be in state `s'` at some point.  Every former with a subterm gets
  a constructor entering it, using `Eval` for the subterms already finished; the
  three formers with no subterms -- `fv`, `bv`, `unit` -- reach nothing beyond
  their starting state and are covered by `refl` alone.  In particular there is an `abort` constructor,
  even though `Eval` has none: an `abort` still runs its argument, and so still
  logs, before failing to return.

`Reach` needs no mutual recursion with `Eval`: `IterReach` refers only to
`Eval`, and `Reach` refers to `Eval` and `IterReach`.

Reachability over-approximates nothing that the terminating semantics already
saw: `Eval.toReach` says that a completed run passes through its own final
state, so `Reach` contains the terminating behaviour.  It is also genuinely
larger than `refl` on ordinary, non-`iter` programs — `Counterexample.logReach_tickTm`
exhibits a reachable log for `let _ = tick (); ()` that is not the one it
started with — and it is refutable: `Counterexample.not_logObsEq_unitTm_tickTm`.

## The separation

`LogObsEq` — same terminating logs, *and* same reachable logs — is **strictly
finer** than state observational equivalence.  One half is general:
`LogObsEq.obsEq` derives `Observation.ObsEq` from `LogObsEq`, since
`LogObsEq`'s first clause is `TermLogObsEq` and `TermLogObsEq` is equivalent to
`Observation.ObsEq` (`obsEq_iff_termObsEq`, `termObsEq_iff_termLogObsEq`).  The
other half is the standing counterexample: `loop` passes through no log but the
one it started with (`Counterexample.logReach_loop_eq`), while `loopF` passes
through `l ++ List.replicate k ⟨tick, ()⟩` for every `k`
(`Counterexample.logReach_loopF_replicate`), so they are not log equivalent
(`Counterexample.loops_not_logObsEq`) even though they are state observationally
equivalent, and indeed even terminating-log equivalent
(`Counterexample.loops_termLogObsEq`).  Both halves are assembled in
`Counterexample.logObsEq_strictly_finer`.

## What is *not* claimed here

`Counterexample.completeness_counterexample_not_logObsEq` records that the pair
witnessing `Counterexample.completeness_fails` is *not* a counterexample to the
corresponding statement for log equivalence.  That is a statement about one
pair, and nothing more.  **Completeness of the equational theory for `LogObsEq`
is open**: nothing in this development proves it, and no argument here rules out
other pairs which are log equivalent and still not derivable.

## Inverting `Reach`

`Reach` is indexed by a typing *derivation*, and the `cases` tactic cannot
invert it at a concrete derivation: unifying, say, `HasType.unit` with
`HasType.pair ha hb` would require solving `tensor A B = LambdaIter.unit`, and
both sides are abstract class operations rather than constructors.  This is the
same obstruction that `Isotope.LambdaIter.Opsem.Eval.Inv` works around, and the
same workaround is used: the inversion payload `Reach.Inv` is *computed* from
the derivation by recursion, and `Reach.inv` proves it once and for all.

## Universes

As in `Isotope.LambdaIter.Opsem.Log`, the log lives in the interpretation
universe only when the signature does, so the log sections take
**`Φ : Type v`**, where `v` is the interpretation universe fixed by
`TypeModel.{u, v} τ`.  The reachability relations themselves are stated for a
general `Φ : Type q`.
-/

namespace Isotope.LambdaIter.Opsem

open Isotope.LambdaIter.Subtyping.Semantics
open Isotope.LambdaIter.LocallyNameless
open Isotope.LambdaIter.Subtyping.LocallyNameless

universe u v w q r

/-! ## Reachability: the states a possibly-divergent run passes through -/

section Reachability

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {S : Type v} [StateModel Φ τ ε S]

/-- The loop with body `hb`, entered at value `x` in state `s`, can be at the
top of a later iteration at value `x'` in state `s'`.

Unlike `IterEval` this does not require the loop to terminate: it records the
values and states a possibly-divergent loop passes through, and so — in a log
model — the log prefixes a possibly-divergent loop can be observed to have
produced.  The loop-carried value is part of the relation, so that reachability
can be continued *into* the body of the iteration it stops at. -/
inductive IterReach {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {b : Tm ν Φ (n + 1)} {A B : τ}
    (hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A))
    (γ : CtxDen Γ) (ρ : BoundDen β) : TyDen A → S → TyDen A → S → Prop
  /-- The top of the current iteration is reached. -/
  | refl (x : TyDen A) (s : S) : IterReach hb γ ρ x s x s
  /-- One more iteration of the body: the body returns into the loop, and the
  value and state it left behind are those the next iteration starts in. -/
  | step {x x' x'' : TyDen A} {s s₁ s'' : S}
      {w : TyDen (LambdaIter.coprod B A)}
      (hx : Eval (ε := ε) hb γ (ρ, x) s s₁ w)
      (hw : TypeModel.coprodEquiv B A w = Sum.inr x')
      (rest : IterReach hb γ ρ x' s₁ x'' s'') : IterReach hb γ ρ x s x'' s''

/-- `IterReach` is transitive: reachability composes. -/
theorem IterReach.trans {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {b : Tm ν Φ (n + 1)} {A B : τ}
    {hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A)}
    {γ : CtxDen Γ} {ρ : BoundDen β} {x x' x'' : TyDen A} {s s' s'' : S} :
    IterReach (ε := ε) hb γ ρ x s x' s' →
      IterReach (ε := ε) hb γ ρ x' s' x'' s'' →
      IterReach (ε := ε) hb γ ρ x s x'' s''
  | .refl _ _, h₂ => h₂
  | .step hx hw rest, h₂ => .step hx hw (IterReach.trans rest h₂)

/-- A terminating loop run reaches the top of its final iteration: the run
splits into a reachable prefix followed by the body execution that returns
`ι_l`. -/
theorem IterEval.toIterReach {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {b : Tm ν Φ (n + 1)} {A B : τ}
    {hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A)}
    {γ : CtxDen Γ} {ρ : BoundDen β} :
    {x : TyDen A} → {s s' : S} → {v : TyDen B} →
    IterEval (ε := ε) hb γ ρ x s s' v →
      ∃ (y : TyDen A) (s₁ : S) (w : TyDen (LambdaIter.coprod B A)),
        IterReach (ε := ε) hb γ ρ x s y s₁ ∧
          Eval (ε := ε) hb γ (ρ, y) s₁ s' w ∧
          TypeModel.coprodEquiv B A w = Sum.inl v
  | _, _, _, _, .done hx hw => ⟨_, _, _, .refl _ _, hx, hw⟩
  | _, _, _, _, .more hx hw rest =>
      let ⟨y, s₂, w, hreach, he, hi⟩ := IterEval.toIterReach rest
      ⟨y, s₂, w, .step hx hw hreach, he, hi⟩

/-- The states a run passes through: `Reach h γ ρ s s'` says that, evaluating
the term typed by `h` from state `s`, the machine can be in state `s'` at some
point.  There is no requirement that the run terminate, so this is defined for
divergent programs too, and it is what a log observation of a divergent run
must look at.

Besides `refl`, there is a constructor for each subterm of each former: one
entering the subterm without having finished it, and, for the later subterms,
one which evaluates the earlier ones with `Eval` and then enters.  (`op` gets
two: one for its argument, and one for the state after the instruction runs.)
Two constructors carry the whole content of the relation:

* `op_run` is the only constructor which by itself changes the state — in a log
  model, the only one which makes the log grow;
* `iter_body` is the only constructor which enters a subterm an unbounded number
  of times, by way of `IterReach`.

Note the `abort` constructor.  `Eval` has none, and cannot: an `abort` never
returns, because its argument has empty type.  But it still *runs* its argument,
and so still logs, which reachability sees. -/
inductive Reach : {Γ : Ctx ν τ} → {n : Nat} → {β : BoundCtx τ n} →
    {t : Tm ν Φ n} → {A : τ} → HasType Φ Γ β t A →
    CtxDen Γ → BoundDen β → S → S → Prop
  /-- Every state is reachable from itself: the machine is where it starts
  before it does anything. -/
  | refl {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
      (h : HasType Φ Γ β t A) (γ : CtxDen Γ) (ρ : BoundDen β) (s : S) :
      Reach h γ ρ s s
  /-- Inside the argument of an instruction. -/
  | op_arg {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {f : Φ} {a : Tm ν Φ n}
      {ha : HasType Φ Γ β a (instrSrc f)}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S}
      (hx : Reach ha γ ρ s s') : Reach (HasType.op ha) γ ρ s s'
  /-- After the instruction itself has run. -/
  | op_run {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {f : Φ} {a : Tm ν Φ n}
      {ha : HasType Φ Γ β a (instrSrc f)}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s₁ s' : S}
      {x : TyDen (τ := τ) (instrSrc f)} {v : TyDen (τ := τ) (instrTrg f)}
      (hx : Eval (ε := ε) ha γ ρ s s₁ x)
      (hr : StateModel.run (ε := ε) f s₁ x = (s', v)) :
      Reach (HasType.op ha) γ ρ s s'
  /-- Inside the bound term of a `let`. -/
  | let₁_bound {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
      {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
      {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ (.snoc β A) b B}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S}
      (hx : Reach ha γ ρ s s') : Reach (HasType.let₁ ha hb) γ ρ s s'
  /-- Inside the body of a `let`, after its bound term has returned. -/
  | let₁_body {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
      {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
      {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ (.snoc β A) b B}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s₁ s' : S} {x : TyDen A}
      (hx : Eval (ε := ε) ha γ ρ s s₁ x) (hy : Reach hb γ (ρ, x) s₁ s') :
      Reach (HasType.let₁ ha hb) γ ρ s s'
  /-- Inside the left component of a pair. -/
  | pair_left {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n}
      {A B : τ} {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b B}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S}
      (hx : Reach ha γ ρ s s') : Reach (HasType.pair ha hb) γ ρ s s'
  /-- Inside the right component of a pair, after the left has returned. -/
  | pair_right {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n}
      {A B : τ} {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b B}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s₁ s' : S} {x : TyDen A}
      (hx : Eval (ε := ε) ha γ ρ s s₁ x) (hy : Reach hb γ ρ s₁ s') :
      Reach (HasType.pair ha hb) γ ρ s s'
  /-- Inside the scrutinee of a destructuring `let`. -/
  | let₂_scrut {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
      {a : Tm ν Φ n} {c : Tm ν Φ (n + 2)} {A B C : τ}
      {ha : HasType Φ Γ β a (LambdaIter.tensor A B)}
      {hc : HasType Φ Γ (.snoc (.snoc β A) B) c C}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S}
      (hx : Reach ha γ ρ s s') : Reach (HasType.let₂ ha hc) γ ρ s s'
  /-- Inside the body of a destructuring `let`, after its scrutinee has
  returned. -/
  | let₂_body {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
      {a : Tm ν Φ n} {c : Tm ν Φ (n + 2)} {A B C : τ}
      {ha : HasType Φ Γ β a (LambdaIter.tensor A B)}
      {hc : HasType Φ Γ (.snoc (.snoc β A) B) c C}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s₁ s' : S}
      {p : TyDen (LambdaIter.tensor A B)}
      (hx : Eval (ε := ε) ha γ ρ s s₁ p)
      (hy : Reach hc γ
        ((ρ, (TypeModel.tensorEquiv A B p).1), (TypeModel.tensorEquiv A B p).2)
        s₁ s') :
      Reach (HasType.let₂ ha hc) γ ρ s s'
  /-- Inside the argument of a left injection. -/
  | inl {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {A B : τ}
      {ha : HasType Φ Γ β a A}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S}
      (hx : Reach ha γ ρ s s') : Reach (HasType.inl (B := B) ha) γ ρ s s'
  /-- Inside the argument of a right injection. -/
  | inr {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {b : Tm ν Φ n} {A B : τ}
      {hb : HasType Φ Γ β b B}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S}
      (hy : Reach hb γ ρ s s') : Reach (HasType.inr (A := A) hb) γ ρ s s'
  /-- Inside the scrutinee of a `case`. -/
  | case_scrut {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
      {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {A B C : τ}
      {he : HasType Φ Γ β e (LambdaIter.coprod A B)}
      {hl : HasType Φ Γ (.snoc β A) l C} {hr : HasType Φ Γ (.snoc β B) r C}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S}
      (hx : Reach he γ ρ s s') : Reach (HasType.case he hl hr) γ ρ s s'
  /-- Inside the left branch of a `case`, which the injection selected. -/
  | caseL {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
      {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {A B C : τ}
      {he : HasType Φ Γ β e (LambdaIter.coprod A B)}
      {hl : HasType Φ Γ (.snoc β A) l C} {hr : HasType Φ Γ (.snoc β B) r C}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s₁ s' : S}
      {w : TyDen (LambdaIter.coprod A B)} {x : TyDen A}
      (hx : Eval (ε := ε) he γ ρ s s₁ w)
      (hw : TypeModel.coprodEquiv A B w = Sum.inl x)
      (hy : Reach hl γ (ρ, x) s₁ s') : Reach (HasType.case he hl hr) γ ρ s s'
  /-- Inside the right branch of a `case`, which the injection selected. -/
  | caseR {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
      {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {A B C : τ}
      {he : HasType Φ Γ β e (LambdaIter.coprod A B)}
      {hl : HasType Φ Γ (.snoc β A) l C} {hr : HasType Φ Γ (.snoc β B) r C}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s₁ s' : S}
      {w : TyDen (LambdaIter.coprod A B)} {y : TyDen B}
      (hx : Eval (ε := ε) he γ ρ s s₁ w)
      (hw : TypeModel.coprodEquiv A B w = Sum.inr y)
      (hy : Reach hr γ (ρ, y) s₁ s') : Reach (HasType.case he hl hr) γ ρ s s'
  /-- Inside the argument of an `abort`.  `Eval` has no `abort` rule — an
  `abort` never returns — but its argument still runs, and still logs. -/
  | abort {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {C : τ}
      {ha : HasType Φ Γ β a LambdaIter.empty}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S}
      (hx : Reach ha γ ρ s s') : Reach (HasType.abort (C := C) ha) γ ρ s s'
  /-- Inside the initial value of a loop. -/
  | iter_init {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
      {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
      {ha : HasType Φ Γ β a A}
      {hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A)}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S}
      (hx : Reach ha γ ρ s s') : Reach (HasType.iter ha hb) γ ρ s s'
  /-- Inside the body of a loop, at the top of some iteration: run the initial
  value, iterate to a later loop state, and enter the body from there.  No
  iteration is required to return `ι_l`, so this sees what a divergent loop
  does. -/
  | iter_body {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
      {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
      {ha : HasType Φ Γ β a A}
      {hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A)}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s₁ s₂ s' : S} {x x' : TyDen A}
      (hx : Eval (ε := ε) ha γ ρ s s₁ x)
      (hloop : IterReach (ε := ε) hb γ ρ x s₁ x' s₂)
      (hbody : Reach hb γ (ρ, x') s₂ s') :
      Reach (HasType.iter ha hb) γ ρ s s'
  /-- Inside a subsumption: the coercion is applied to the returned value and
  does not touch the state. -/
  | sub {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {A B : τ}
      {ha : HasType Φ Γ β a A} {d : Subty A B}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S}
      (hx : Reach ha γ ρ s s') : Reach (HasType.sub ha d) γ ρ s s'

attribute [simp] Reach.refl

/-- Reachability is reflexive. -/
theorem Reach.rfl {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n}
    {A : τ} {h : HasType Φ Γ β t A} {γ : CtxDen Γ} {ρ : BoundDen β} {s : S} :
    Reach (ε := ε) h γ ρ s s := .refl h γ ρ s

mutual

/-- **A completed run passes through its own final state.**  So reachability
contains the terminating behaviour.  The converse inclusion is false, and
deliberately so: `Counterexample.logReach_loopF_replicate` exhibits reachable
logs of a program with no terminating run at all.  Nothing here bounds `Reach`
from above. -/
theorem Eval.toReach {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} {h : HasType Φ Γ β t A}
    {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S} {v : TyDen A} :
    Eval (ε := ε) h γ ρ s s' v → Reach (ε := ε) h γ ρ s s'
  | .fv hx γ ρ s => .refl _ γ ρ s
  | .bv γ ρ s => .refl _ γ ρ s
  | .unit γ ρ s => .refl _ γ ρ s
  | .op hx hr => .op_run hx hr
  | .let₁ hx hy => .let₁_body hx (Eval.toReach hy)
  | .pair hx hy => .pair_right hx (Eval.toReach hy)
  | .let₂ hx hy => .let₂_body hx (Eval.toReach hy)
  | .inl hx => .inl (Eval.toReach hx)
  | .inr hy => .inr (Eval.toReach hy)
  | .caseL hx hw hy => .caseL hx hw (Eval.toReach hy)
  | .caseR hx hw hy => .caseR hx hw (Eval.toReach hy)
  | .iter hx hloop =>
      let ⟨_y, _s₁, hreach, hbody⟩ := IterEval.toReach hloop
      .iter_body hx hreach hbody
  | .sub hx => .sub (Eval.toReach hx)

/-- A completed loop run passes through the top of its final iteration, and the
body execution which returns `ι_l` passes through its own final state. -/
theorem IterEval.toReach {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {b : Tm ν Φ (n + 1)} {A B : τ}
    {hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A)}
    {γ : CtxDen Γ} {ρ : BoundDen β} :
    {x : TyDen A} → {s s' : S} → {v : TyDen B} →
    IterEval (ε := ε) hb γ ρ x s s' v →
      ∃ (y : TyDen A) (s₁ : S),
        IterReach (ε := ε) hb γ ρ x s y s₁ ∧ Reach (ε := ε) hb γ (ρ, y) s₁ s'
  | _, _, _, _, .done hx _ => ⟨_, _, .refl _ _, Eval.toReach hx⟩
  | _, _, _, _, .more hx hw rest =>
      let ⟨y, s₂, hreach, hbody⟩ := IterEval.toReach rest
      ⟨y, s₂, .step hx hw hreach, hbody⟩

end

/-! ### Inversion

`cases` cannot invert `Reach` at a concrete derivation, for the reason recorded
in the module docstring, so the inversion payload is computed from the
derivation and proved once, exactly as for `Eval.Inv`. -/

/-- The inversion payload of a reachability proof: what it means to reach `s'`
from `s`, spelled out per former.  The three formers with no subterms — `fv`,
`bv` and `unit` — reach nothing but their own starting state. -/
def Reach.Inv : {Γ : Ctx ν τ} → {n : Nat} → {β : BoundCtx τ n} →
    {t : Tm ν Φ n} → {A : τ} → HasType Φ Γ β t A →
    CtxDen Γ → BoundDen β → S → S → Prop
  | _, _, _, _, _, .fv _, _, _, s, s' => s' = s
  | _, _, _, _, _, .bv, _, _, s, s' => s' = s
  | _, _, _, _, _, .unit, _, _, s, s' => s' = s
  | _, _, _, _, _, .op (f := f) ha, γ, ρ, s, s' =>
      Reach (ε := ε) ha γ ρ s s' ∨
        ∃ s₁ x v, Eval (ε := ε) ha γ ρ s s₁ x ∧
          StateModel.run (ε := ε) f s₁ x = (s', v)
  | _, _, _, _, _, .let₁ ha hb, γ, ρ, s, s' =>
      Reach (ε := ε) ha γ ρ s s' ∨
        ∃ s₁ x, Eval (ε := ε) ha γ ρ s s₁ x ∧ Reach (ε := ε) hb γ (ρ, x) s₁ s'
  | _, _, _, _, _, .pair ha hb, γ, ρ, s, s' =>
      Reach (ε := ε) ha γ ρ s s' ∨
        ∃ s₁ x, Eval (ε := ε) ha γ ρ s s₁ x ∧ Reach (ε := ε) hb γ ρ s₁ s'
  | _, _, _, _, _, .let₂ ha hc, γ, ρ, s, s' =>
      Reach (ε := ε) ha γ ρ s s' ∨
        ∃ s₁ p, Eval (ε := ε) ha γ ρ s s₁ p ∧
          Reach (ε := ε) hc γ
            ((ρ, (TypeModel.tensorEquiv _ _ p).1),
              (TypeModel.tensorEquiv _ _ p).2) s₁ s'
  | _, _, _, _, _, .inl ha, γ, ρ, s, s' => Reach (ε := ε) ha γ ρ s s'
  | _, _, _, _, _, .inr hb, γ, ρ, s, s' => Reach (ε := ε) hb γ ρ s s'
  | _, _, _, _, _, .case he hl hr, γ, ρ, s, s' =>
      Reach (ε := ε) he γ ρ s s' ∨
        (∃ s₁ w x, Eval (ε := ε) he γ ρ s s₁ w ∧
          TypeModel.coprodEquiv _ _ w = Sum.inl x ∧
          Reach (ε := ε) hl γ (ρ, x) s₁ s') ∨
        (∃ s₁ w y, Eval (ε := ε) he γ ρ s s₁ w ∧
          TypeModel.coprodEquiv _ _ w = Sum.inr y ∧
          Reach (ε := ε) hr γ (ρ, y) s₁ s')
  | _, _, _, _, _, .abort ha, γ, ρ, s, s' => Reach (ε := ε) ha γ ρ s s'
  | _, _, _, _, _, .iter ha hb, γ, ρ, s, s' =>
      Reach (ε := ε) ha γ ρ s s' ∨
        ∃ s₁ s₂ x x', Eval (ε := ε) ha γ ρ s s₁ x ∧
          IterReach (ε := ε) hb γ ρ x s₁ x' s₂ ∧
          Reach (ε := ε) hb γ (ρ, x') s₂ s'
  | _, _, _, _, _, .sub ha _, γ, ρ, s, s' => Reach (ε := ε) ha γ ρ s s'

/-- The inversion payload holds trivially of a state reached from itself. -/
theorem Reach.Inv.refl : {Γ : Ctx ν τ} → {n : Nat} → {β : BoundCtx τ n} →
    {t : Tm ν Φ n} → {A : τ} → (h : HasType Φ Γ β t A) →
    (γ : CtxDen Γ) → (ρ : BoundDen β) → (s : S) →
    Reach.Inv (ε := ε) h γ ρ s s
  | _, _, _, _, _, .fv _, _, _, _ => _root_.rfl
  | _, _, _, _, _, .bv, _, _, _ => _root_.rfl
  | _, _, _, _, _, .unit, _, _, _ => _root_.rfl
  | _, _, _, _, _, .op ha, γ, ρ, s => Or.inl (.refl ha γ ρ s)
  | _, _, _, _, _, .let₁ ha _, γ, ρ, s => Or.inl (.refl ha γ ρ s)
  | _, _, _, _, _, .pair ha _, γ, ρ, s => Or.inl (.refl ha γ ρ s)
  | _, _, _, _, _, .let₂ ha _, γ, ρ, s => Or.inl (.refl ha γ ρ s)
  | _, _, _, _, _, .inl ha, γ, ρ, s => Reach.refl ha γ ρ s
  | _, _, _, _, _, .inr hb, γ, ρ, s => Reach.refl hb γ ρ s
  | _, _, _, _, _, .case he _ _, γ, ρ, s => Or.inl (.refl he γ ρ s)
  | _, _, _, _, _, .abort ha, γ, ρ, s => Reach.refl ha γ ρ s
  | _, _, _, _, _, .iter ha _, γ, ρ, s => Or.inl (.refl ha γ ρ s)
  | _, _, _, _, _, .sub ha _, γ, ρ, s => Reach.refl ha γ ρ s

/-- **Inversion for reachability.**  Every reachability proof satisfies the
payload computed from its derivation. -/
theorem Reach.inv {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} {h : HasType Φ Γ β t A}
    {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S} :
    Reach (ε := ε) h γ ρ s s' → Reach.Inv (ε := ε) h γ ρ s s'
  | .refl h γ ρ s => Reach.Inv.refl h γ ρ s
  | .op_arg hx => Or.inl hx
  | .op_run hx hr => Or.inr ⟨_, _, _, hx, hr⟩
  | .let₁_bound hx => Or.inl hx
  | .let₁_body hx hy => Or.inr ⟨_, _, hx, hy⟩
  | .pair_left hx => Or.inl hx
  | .pair_right hx hy => Or.inr ⟨_, _, hx, hy⟩
  | .let₂_scrut hx => Or.inl hx
  | .let₂_body hx hy => Or.inr ⟨_, _, hx, hy⟩
  | .inl hx => hx
  | .inr hy => hy
  | .case_scrut hx => Or.inl hx
  | .caseL hx hw hy => Or.inr (Or.inl ⟨_, _, _, hx, hw, hy⟩)
  | .caseR hx hw hy => Or.inr (Or.inr ⟨_, _, _, hx, hw, hy⟩)
  | .abort hx => hx
  | .iter_init hx => Or.inl hx
  | .iter_body hx hloop hbody => Or.inr ⟨_, _, _, _, hx, hloop, hbody⟩
  | .sub hx => hx

/-- A free variable reaches nothing but its own starting state. -/
theorem Reach.fv_inv {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {x : ν} {A : τ}
    {hx : Γ.lookup x = some A} {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S}
    (h : Reach (ε := ε) (HasType.fv (Φ := Φ) (β := β) hx) γ ρ s s') : s' = s :=
  h.inv

/-- A bound variable reaches nothing but its own starting state. -/
theorem Reach.bv_inv {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {ι : Fin n}
    {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S}
    (h : Reach (ε := ε)
      (HasType.bv (Φ := Φ) (Γ := Γ) (β := β) (ι := ι)) γ ρ s s') : s' = s :=
  h.inv

/-- `()` reaches nothing but its own starting state. -/
theorem Reach.unit_inv {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S}
    (h : Reach (ε := ε)
      (HasType.unit (Φ := Φ) (Γ := Γ) (β := β)) γ ρ s s') : s' = s :=
  h.inv

/-- Inversion for a right injection: reaching inside `ι_r b` is reaching inside
`b`. -/
theorem Reach.inr_inv {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {b : Tm ν Φ n} {A B : τ} {hb : HasType Φ Γ β b B}
    {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S}
    (h : Reach (ε := ε) (HasType.inr (A := A) hb) γ ρ s s') :
    Reach (ε := ε) hb γ ρ s s' := h.inv

/-- Inversion for a loop: either the initial value has not returned yet, or it
has, and the machine is somewhere inside the body of some iteration. -/
theorem Reach.iter_inv {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    {ha : HasType Φ Γ β a A}
    {hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A)}
    {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S}
    (h : Reach (ε := ε) (HasType.iter ha hb) γ ρ s s') :
    Reach (ε := ε) ha γ ρ s s' ∨
      ∃ s₁ s₂ x x', Eval (ε := ε) ha γ ρ s s₁ x ∧
        IterReach (ε := ε) hb γ ρ x s₁ x' s₂ ∧
        Reach (ε := ε) hb γ (ρ, x') s₂ s' := h.inv

end Reachability

/-! ## Reachability in a log model -/

section LogReachability

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε] [DecidableEq ε]
variable {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
variable {a b c : Tm ν Φ n} {A : τ}

/-- The log prefixes a loop passes through, in the log model of `I`. -/
def LogIterReach (I : LogInterp Φ τ ε) {b : Tm ν Φ (n + 1)} {A B : τ}
    (hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A))
    (γ : CtxDen Γ) (ρ : BoundDen β) (x : TyDen A) (l : Log Φ τ)
    (x' : TyDen A) (l' : Log Φ τ) : Prop :=
  letI := logStateModel I
  IterReach (ε := ε) (S := Log Φ τ) hb γ ρ x l x' l'

/-- The log prefixes a program passes through, in the log model of `I`:
`LogReach I h γ ρ l l'` says that the program typed by `h`, started with log
prefix `l`, can be observed to have produced the log `l'` at some point of its
run — whether or not it ever terminates. -/
def LogReach (I : LogInterp Φ τ ε) {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β t A) (γ : CtxDen Γ) (ρ : BoundDen β)
    (l l' : Log Φ τ) : Prop :=
  letI := logStateModel I
  Reach (ε := ε) (S := Log Φ τ) h γ ρ l l'

/-- `LogIterReach` is loop reachability in the log model, by definition. -/
theorem logIterReach_iff (I : LogInterp Φ τ ε) {b : Tm ν Φ (n + 1)} {A B : τ}
    (hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A))
    (γ : CtxDen Γ) (ρ : BoundDen β) (x : TyDen A) (l : Log Φ τ)
    (x' : TyDen A) (l' : Log Φ τ) :
    LogIterReach I hb γ ρ x l x' l' ↔
      letI := logStateModel I
      IterReach (ε := ε) (S := Log Φ τ) hb γ ρ x l x' l' := Iff.rfl

/-- `LogReach` is reachability in the log model, by definition. -/
theorem logReach_iff (I : LogInterp Φ τ ε) {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β t A) (γ : CtxDen Γ) (ρ : BoundDen β)
    (l l' : Log Φ τ) :
    LogReach I h γ ρ l l' ↔
      letI := logStateModel I
      Reach (ε := ε) (S := Log Φ τ) h γ ρ l l' := Iff.rfl

/-- A program is observed to have produced the log it started with. -/
@[simp] theorem logReach_rfl (I : LogInterp Φ τ ε) {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β t A) (γ : CtxDen Γ) (ρ : BoundDen β) (l : Log Φ τ) :
    LogReach I h γ ρ l l := by
  letI := logStateModel I
  exact Reach.refl (S := Log Φ τ) h γ ρ l

/-- A terminating log run is observed: the final log is reachable. -/
theorem LogEval.toLogReach (I : LogInterp Φ τ ε) {t : Tm ν Φ n} {A : τ}
    {h : HasType Φ Γ β t A} {γ : CtxDen Γ} {ρ : BoundDen β}
    {l l' : Log Φ τ} {v : TyDen A} (he : LogEval I h γ ρ l l' v) :
    LogReach I h γ ρ l l' := by
  letI := logStateModel I
  exact Eval.toReach (S := Log Φ τ) he

/-- **Log observational equivalence.**  Two programs are log observationally
equivalent when they have the same terminating logs *and* pass through the same
log prefixes, under every pure interpretation and every oracle.

The second clause is the divergence-sensitive one: it compares the prefixes of
an unfinished log, and so says something about programs that never return.  The
definition is a conjunction so that `LogObsEq` is by construction at least as
strong as `TermLogObsEq` (`LogObsEq.termLogObsEq`).  It is *strictly* stronger:
`Counterexample.logObsEq_strictly_finer` exhibits a pair -- the two loops -- which
is `TermLogObsEq` but not `LogObsEq`. -/
def LogObsEq (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b A) : Prop :=
  TermLogObsEq (ε := ε) ha hb ∧
    ∀ (I : LogInterp Φ τ ε) (γ : CtxDen Γ) (ρ : BoundDen β) (l l' : Log Φ τ),
      LogReach I ha γ ρ l l' ↔ LogReach I hb γ ρ l l'

/-- Log observational equivalence is reflexive. -/
@[refl] theorem LogObsEq.refl (ha : HasType Φ Γ β a A) :
    LogObsEq (ε := ε) ha ha :=
  ⟨TermLogObsEq.refl ha, fun _ _ _ _ _ => Iff.rfl⟩

/-- Log observational equivalence is symmetric. -/
theorem LogObsEq.symm {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
    (h : LogObsEq (ε := ε) ha hb) : LogObsEq (ε := ε) hb ha :=
  ⟨h.1.symm, fun I γ ρ l l' => (h.2 I γ ρ l l').symm⟩

/-- Log observational equivalence is transitive. -/
theorem LogObsEq.trans {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
    {hc : HasType Φ Γ β c A} (h₁ : LogObsEq (ε := ε) ha hb)
    (h₂ : LogObsEq (ε := ε) hb hc) : LogObsEq (ε := ε) ha hc :=
  ⟨h₁.1.trans h₂.1, fun I γ ρ l l' => (h₁.2 I γ ρ l l').trans (h₂.2 I γ ρ l l')⟩

/-- Log observational equivalence implies its terminating part, by
construction. -/
theorem LogObsEq.termLogObsEq {ha : HasType Φ Γ β a A}
    {hb : HasType Φ Γ β b A} (h : LogObsEq (ε := ε) ha hb) :
    TermLogObsEq (ε := ε) ha hb := h.1

end LogReachability

/-! ## The worked example: reachability is not vacuous -/

namespace Counterexample

open Example

variable {I : LogInterp Instr (Ty Base) Effect}
  {γ : CtxDen Γ0} {ρ : BoundDen β0}

/-- The single event `loopF` logs on each iteration. -/
def tickEvent : Event Instr (Ty Base) := ⟨Instr.tick, ()⟩

/-! ### A non-`iter` program with a non-trivial reachable log

The point of a general reachability relation, rather than one defined at `iter`
alone, is that it has content away from `iter`.  `tickTm = let _ = tick (); ()`
has no loop in it, and it reaches a log it did not start with. -/

/-- **`let _ = tick (); ()` is observed to have produced its `tick`.**  The
reachable log `[⟨tick, ()⟩]` is not the one the program started with, so `Reach`
is inhabited beyond `refl` at a program whose head former is not `iter`. -/
theorem logReach_tickTm (γ : CtxDen Γ0) (ρ : BoundDen β0) :
    LogReach logInterp tickTmTy γ ρ [] [tickEvent] := by
  letI := logStateModel logInterp
  exact Reach.let₁_bound
    (Reach.op_run (Eval.unit (Φ := Instr) γ ρ []) (logStateModel_tick [] ()))

/-- **`()` reaches only the log it started with.**  So reachability is not
just `refl` in disguise on one side and everything on the other; the separation
of `unitTm` from `tickTm` is `not_logObsEq_unitTm_tickTm`. -/
theorem logReach_unitTm_eq {l l' : Log Instr (Ty Base)}
    (h : LogReach I unitTmTy γ ρ l l') : l' = l := by
  letI := logStateModel I
  exact Reach.unit_inv (Φ := Instr) h

/-- **Log observational equivalence is refutable.**  `()` and
`let _ = tick (); ()` pass through different logs, so no relation containing the
reachability clause can identify them. -/
theorem not_logObsEq_unitTm_tickTm :
    ¬ LogObsEq (ε := Effect) unitTmTy tickTmTy := by
  intro h
  have hu := (h.2 logInterp PUnit.unit PUnit.unit [] [tickEvent]).2
    (logReach_tickTm PUnit.unit PUnit.unit)
  exact absurd (logReach_unitTm_eq hu) (by simp [tickEvent])

/-! ### `loop` logs nothing -/

/-- One iteration of the body of `loop` leaves the log alone: it is the pure
term `ι_r x`, so it makes no call. -/
theorem logEval_loop_body_eq (x : TyDen (τ := Ty Base) (LambdaIter.unit : Ty Base))
    (l l₁ : Log Instr (Ty Base))
    {w : TyDen (τ := Ty Base)
      (LambdaIter.coprod (Ty.unit : Ty Base) (LambdaIter.unit : Ty Base))}
    (hx : LogEval I (HasType.inr (A := (Ty.unit : Ty Base))
      (HasType.newest (Φ := Instr) (Γ := Γ0) (β := β0)
        (A := (LambdaIter.unit : Ty Base)))) γ (ρ, x) l l₁ w) :
    l₁ = l := by
  letI := logStateModel I
  have hcanon :
      Eval (ε := Effect) (S := Log Instr (Ty Base))
        (HasType.inr (A := (Ty.unit : Ty Base))
          (HasType.newest (Φ := Instr) (Γ := Γ0) (β := β0)
            (A := (LambdaIter.unit : Ty Base)))) γ (ρ, x) l l _ :=
    Eval.inr (Eval.bv (Φ := Instr) (Γ := Γ0)
      (β := BoundCtx.snoc β0 (LambdaIter.unit : Ty Base)) (ι := (0 : Fin 1))
      γ (ρ, x) l)
  exact (Eval.deterministic hx hcanon).1

/-- The body of `loop` reaches only the log it started with: it is the pure term
`ι_r x`, whose only subterm is a bound variable. -/
theorem logReach_loop_body_eq
    {x : TyDen (τ := Ty Base) (LambdaIter.unit : Ty Base)}
    {l l' : Log Instr (Ty Base)}
    (h : LogReach I (HasType.inr (A := (Ty.unit : Ty Base))
      (HasType.newest (Φ := Instr) (Γ := Γ0) (β := β0)
        (A := (LambdaIter.unit : Ty Base)))) γ (ρ, x) l l') :
    l' = l := by
  letI := logStateModel I
  exact Reach.bv_inv (Φ := Instr) (Γ := Γ0)
    (β := BoundCtx.snoc β0 (LambdaIter.unit : Ty Base)) (ι := (0 : Fin 1))
    (Reach.inr_inv h)

/-- **The body of `loop` passes through no log but the one it started with.**
The program-level statement is `logReach_loop_eq`.  It diverges
without ever calling anything. -/
theorem logIterReach_loop_eq
    {x x' : TyDen (τ := Ty Base) (LambdaIter.unit : Ty Base)}
    {l l' : Log Instr (Ty Base)}
    (h : LogIterReach I (HasType.inr (A := (Ty.unit : Ty Base))
      (HasType.newest (Φ := Instr) (Γ := Γ0) (β := β0)
        (A := (LambdaIter.unit : Ty Base)))) γ ρ x l x' l') :
    l' = l := by
  induction h with
  | refl x s => rfl
  | step hx _ _ ih => exact ih.trans (logEval_loop_body_eq _ _ _ hx)

/-- **`loop` produces no log at all.**  Whatever prefix it is started with, that
is the only log it is ever observed to have — at any point of its run, not only
at the end, which it never reaches. -/
theorem logReach_loop_eq {l l' : Log Instr (Ty Base)}
    (h : LogReach I loopTy γ ρ l l') : l' = l := by
  letI := logStateModel I
  rcases Reach.iter_inv h with hinit | ⟨l₁, l₂, x, x', hx, hloop, hbody⟩
  · exact Reach.unit_inv (Φ := Instr) hinit
  · obtain ⟨rfl, -⟩ := Eval.deterministic hx (Eval.unit (Φ := Instr) γ ρ l)
    exact (logReach_loop_body_eq hbody).trans (logIterReach_loop_eq hloop)

/-! ### `loopF` logs a `tick` per iteration -/

/-- One iteration of the body of `loopF` appends exactly one `tick` event to the
log and returns into the loop. -/
theorem logEval_loopF_body
    (x : TyDen (τ := Ty Base) (LambdaIter.unit : Ty Base))
    (l : Log Instr (Ty Base)) :
    LogEval I (HasType.let₁ (HasType.op (f := Instr.tick)
        (HasType.newest (Φ := Instr) (Γ := Γ0) (β := β0)
          (A := (LambdaIter.unit : Ty Base))))
      (HasType.inr (A := (Ty.unit : Ty Base)) HasType.previous))
      γ (ρ, x) l (l ++ [tickEvent])
      ((TypeModel.coprodEquiv (Ty.unit : Ty Base)
        (LambdaIter.unit : Ty Base)).symm (Sum.inr x)) := by
  letI := logStateModel I
  have hr := logStateModel_run_of_impure I Instr.tick impure_ne_bot l x
  exact Eval.let₁
    (Eval.op (Eval.bv (Φ := Instr) (Γ := Γ0)
      (β := BoundCtx.snoc β0 (LambdaIter.unit : Ty Base)) (ι := (0 : Fin 1))
      γ (ρ, x) l) hr)
    (Eval.inr (Eval.bv (Φ := Instr) (Γ := Γ0)
      (β := BoundCtx.snoc (BoundCtx.snoc β0 (LambdaIter.unit : Ty Base))
        (instrTrg Instr.tick))
      (ι := (1 : Fin 2)) γ ((ρ, x), _) (l ++ [tickEvent])))

/-- **The body of `loopF` passes through `l ++ List.replicate k ⟨tick, ()⟩` for
every `k`.**  Its log grows without bound: one `tick` per iteration, forever.
The program-level statement is `logReach_loopF_replicate`. -/
theorem logIterReach_loopF_replicate :
    ∀ (k : Nat) (x : TyDen (τ := Ty Base) (LambdaIter.unit : Ty Base))
      (l : Log Instr (Ty Base)),
      LogIterReach I (HasType.let₁ (HasType.op (f := Instr.tick)
          (HasType.newest (Φ := Instr) (Γ := Γ0) (β := β0)
            (A := (LambdaIter.unit : Ty Base))))
        (HasType.inr (A := (Ty.unit : Ty Base)) HasType.previous))
        γ ρ x l x (l ++ List.replicate k tickEvent)
  | 0, x, l => by
      letI := logStateModel I
      simpa using IterReach.refl (ε := Effect) x l
  | k + 1, x, l => by
      letI := logStateModel I
      refine IterReach.step (logEval_loopF_body x l) ?_
        (by simpa [List.replicate_succ] using
          logIterReach_loopF_replicate k x (l ++ [tickEvent]))
      exact Equiv.apply_symm_apply _ _

/-- `loopF`, started with log prefix `l`, is observed to have produced
`l ++ List.replicate k ⟨tick, ()⟩` for every `k`. -/
theorem logReach_loopF_replicate (k : Nat) (l : Log Instr (Ty Base)) :
    LogReach I loopFTy γ ρ l (l ++ List.replicate k tickEvent) := by
  letI := logStateModel I
  exact Reach.iter_body (Eval.unit (Φ := Instr) γ ρ l)
    (logIterReach_loopF_replicate k _ l) (Reach.refl _ _ _ _)

/-- The two diverging loops pass through different logs: `loopF` is observed to
have produced a one-`tick` log, and `loop` is never observed to have produced
any log but the one it started with.

This is the concrete arithmetic behind the separation: it is what
`loops_not_logObsEq` feeds into the reachability clause of `LogObsEq`. -/
theorem loop_logs_ne_loopF_logs (I : LogInterp Instr (Ty Base) Effect)
    (γ : CtxDen Γ0) (ρ : BoundDen β0) :
    LogReach I loopFTy γ ρ [] [tickEvent] ∧
      ¬ LogReach I loopTy γ ρ [] [tickEvent] := by
  refine ⟨by simpa using logReach_loopF_replicate (I := I) 1 [], ?_⟩
  intro h
  exact absurd (logReach_loop_eq h) (by simp [tickEvent])

end Counterexample

/-! ## Log equivalence implies state observational equivalence

The forward direction of the headline is general, and is proved once here for an
arbitrary signature. -/

section Strictness

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε] [DecidableEq ε]
variable {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
variable {a b : Tm ν Φ n} {A : τ}

/-- **Log equivalence refines state observational equivalence.**  `LogObsEq` is
a conjunction whose first clause is `TermLogObsEq`, and `TermLogObsEq` is
equivalent to `Observation.ObsEq` — through `termObsEq_iff_termLogObsEq` (a log
model is a state model, and a state run lifts to a log run) and
`obsEq_iff_termObsEq` (the divergence clause of `ObsEq` is redundant, because
`Diverges` is the absence of an `Eval`).

Dropping the reachability clause therefore lands exactly on state observational
equivalence: everything `LogObsEq` identifies, `ObsEq` identifies too. -/
theorem LogObsEq.obsEq {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
    (h : LogObsEq (ε := ε) ha hb) : Observation.ObsEq (ε := ε) ha hb :=
  obsEq_iff_termObsEq.mpr (termObsEq_iff_termLogObsEq.mpr h.termLogObsEq)

end Strictness

/-! ## The headline: the separation, and what it does and does not settle -/

namespace Counterexample

open Example

variable {I : LogInterp Instr (Ty Base) Effect}
  {γ : CtxDen Γ0} {ρ : BoundDen β0}

/-! ### The two loops

`loop` and `loopF` are the standing counterexample to completeness of the
equational theory for state observation: they are observationally equivalent in
every state model (`loop_obsEq_loopF`) but not related by the equational theory
(`loop_not_related`).  The two theorems above show that the *logs they pass
through* tell them apart, and this section assembles that into the headline. -/

/-- **A non-trivial reachable log for `loopF`, at `k = 1`.**  This is
`logReach_loopF_replicate` at `k = 1`, recorded separately so that the unbounded
statement is visibly not collapsing to `Reach.refl`: the log `l ++ [⟨tick, ()⟩]`
is strictly longer than the one the program started with, and `loopF` never
returns, so no terminating observation can see it. -/
theorem logReach_loopF_tick (l : Log Instr (Ty Base)) :
    LogReach I loopFTy γ ρ l (l ++ [tickEvent]) := by
  simpa using logReach_loopF_replicate (I := I) 1 l

/-- **The two loops are not log equivalent.**  `loopF` passes through the log
`[⟨tick, ()⟩]` from the empty log, and `loop` passes through no log but the one
it started with (`logReach_loop_eq`), so the reachability clause of `LogObsEq`
separates them.

Note that the refutation goes through the *reachability* clause `h.2`, not
through `TermLogObsEq`: the terminating clause cannot separate them, since
neither loop ever terminates (`loops_termLogObsEq`). -/
theorem loops_not_logObsEq : ¬ LogObsEq (ε := Effect) loopTy loopFTy := by
  intro h
  obtain ⟨hF, hL⟩ := loop_logs_ne_loopF_logs logInterp PUnit.unit PUnit.unit
  exact hL ((h.2 logInterp PUnit.unit PUnit.unit [] [tickEvent]).2 hF)

/-- **The two loops *are* terminating-log equivalent.**  Both diverge, so
neither has a terminating run at all, and they agree vacuously on terminating
logs.

Formally this is read off the already-established state observational
equivalence `loop_obsEq_loopF`: `obsEq_iff_termObsEq` drops the (redundant)
divergence clause, and `termObsEq_iff_termLogObsEq` transports the terminating
part to the log model. -/
theorem loops_termLogObsEq : TermLogObsEq (ε := Effect) loopTy loopFTy :=
  termObsEq_iff_termLogObsEq.mp (obsEq_iff_termObsEq.mp loop_obsEq_loopF)

/-- **The headline: log equivalence is strictly finer than state observational
equivalence.**  Both halves are spelled out:

* every log equivalent pair is state observationally equivalent
  (`LogObsEq.obsEq`, stated here at the example signature);
* the converse fails, witnessed by `loop` and `loopF`, which are state
  observationally equivalent (`loop_obsEq_loopF`) — indeed even
  terminating-log equivalent (`loops_termLogObsEq`) — and yet not log
  equivalent (`loops_not_logObsEq`), because their reachable logs differ.

The witness is what a purely terminating observation cannot supply: the two
programs have *no* terminating runs, so every clause about final states or final
logs is vacuous for them.  Only the logs they pass through on the way separate
them. -/
theorem logObsEq_strictly_finer :
    (∀ (a b : Tm Empty Instr 0) (A : Ty Base)
        (ha : HasType Instr Γ0 β0 a A) (hb : HasType Instr Γ0 β0 b A),
        LogObsEq (ε := Effect) ha hb → Observation.ObsEq (ε := Effect) ha hb) ∧
      Observation.ObsEq (ε := Effect) loopTy loopFTy ∧
      TermLogObsEq (ε := Effect) loopTy loopFTy ∧
      ¬ LogObsEq (ε := Effect) loopTy loopFTy :=
  ⟨fun _ _ _ _ _ h => h.obsEq, loop_obsEq_loopF, loops_termLogObsEq,
    loops_not_logObsEq⟩

/-- **The known counterexample to completeness dissolves under log
equivalence.**

`completeness_fails` refutes the converse of
`Isotope.LambdaIter.Opsem.Observation.obsEq_of_related` — that is, it refutes

    `Observation.ObsEq ha hb → TypedEquiv.Related ⊥ Γ ha hb`

and its single witness is the pair `loop`, `loopF`: they are observationally
equivalent in every state model but not related by the equational theory.

This theorem records that the *same pair* is not a witness against the
corresponding statement for log equivalence,

    `LogObsEq ha hb → TypedEquiv.Related ⊥ Γ ha hb`,

because its hypothesis is false at this pair: `LogObsEq loopTy loopFTy → False`.
A refutation of the log statement would need a *different* pair.

## What this does **not** show

It does **not** show that the equational theory is complete for `LogObsEq`.
Nothing in this development proves that; completeness for log equivalence is
**open**.  All that is established is the strictly weaker fact that the one
counterexample which is known to refute completeness for state observation stops
applying once the observation is the log.  There may well be other pairs which
are log equivalent and still not derivable, and no argument here rules them
out. -/
theorem completeness_counterexample_not_logObsEq :
    Observation.ObsEq (ε := Effect) loopTy loopFTy ∧
      ¬ TypedEquiv.Related (⊥ : Effect) Γ0 loopTy loopFTy ∧
      (LogObsEq (ε := Effect) loopTy loopFTy → False) :=
  ⟨loop_obsEq_loopF, loop_not_related, loops_not_logObsEq⟩

end Counterexample

end Isotope.LambdaIter.Opsem
