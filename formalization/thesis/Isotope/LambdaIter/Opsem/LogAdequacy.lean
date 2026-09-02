import Isotope.LambdaIter.Opsem.Log
import Isotope.LambdaIter.Opsem.Counterexample

/-!
# Log adequacy: on terminating runs, the state and the log see the same thing

`Isotope.LambdaIter.Opsem.Log` builds the log observation as a family of state
models — the state *is* the log prefix so far — and shows one direction of the
comparison: a terminating run of a log model is a terminating run of every state
model it was induced from (`eval_of_logEval`).  This file proves the converse
and the theorem it yields.

The converse is the **lifting lemma** `Eval.toLog`: every terminating run of an
arbitrary state model is the image, under `replay`, of a terminating run of the
induced log model.  It cannot be stated naively, because the induction threads
the state through the derivation while what we build is a log, and the state at
each intermediate point is only *represented* by a log prefix.  So the statement
is generalized over the log prefix reached so far:

    Eval h γ ρ s s' v → ∀ l, replay s₀ l = s → ∃ l', LogEval … l l' v ∧ replay s₀ l' = s'

Each constructor threads the log in exactly the order it threads the state; the
log grows in the `op` case, and only there, and only for an impure instruction
(`run_toLog`).

The two lemmas together say that state observation and terminating log
observation agree.  Note carefully what this does *not* buy.  `Diverges` is the
*absence* of an `Eval`, so agreement of the evaluation relations already forces
agreement of divergence (`Observation.diverges_congr`); consequently `TermObsEq`
is not a weakening of `Observation.ObsEq` but literally the same relation
(`obsEq_iff_termObsEq`), and the main theorem therefore says

    Observation.ObsEq  ↔  TermLogObsEq                     (`obsEq_iff_termLogObsEq`)

Making the state the log prefix so far does **not**, by itself, produce a finer
observation: a terminating log run is still only visible when it terminates.  In
particular `TermLogObsEq` still identifies the standing counterexample
`Counterexample.loop` and `Counterexample.loopF`, which diverge in every model.
To see the difference between logging infinitely many `tick`s and logging
nothing one must observe the log prefixes a run *passes through*, not only the
one it ends with; that is `Isotope.LambdaIter.Opsem.LogPrefix`.

The existing `Observation.ObsEq` is left untouched.

## Universes

As in `Isotope.LambdaIter.Opsem.Log`, an `Event` bundles an instruction with an
argument, so the log lives in the interpretation universe only when the
signature does.  Every section of this file therefore takes **`Φ : Type v`**,
where `v` is the interpretation universe fixed by `TypeModel.{u, v} τ`.  This is
satisfied by `Isotope.LambdaIter.Opsem.Example` (`Instr : Type`, `v = 0`).
-/

namespace Isotope.LambdaIter.Opsem

open Isotope.LambdaIter.Subtyping.Semantics
open Isotope.LambdaIter.LocallyNameless
open Isotope.LambdaIter.Subtyping.LocallyNameless

universe u v w r

/-! ## Lifting a terminating run to the induced log model -/

section Lifting

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε] [DecidableEq ε]
variable {S : Type v} [M : StateModel Φ τ ε S]

/-- A single instruction call lifts to the induced log model: whatever a call
does to the state, there is a log extension doing the same thing, and the value
returned is the same.

This is the only place the log grows.  For a pure instruction the log is left
alone — the purity law says the state is unchanged too, and that the returned
value does not depend on the state, so the log model computes the same value.
For an impure instruction the call is appended, and replaying the extended log
performs exactly that call (`replay_append_one`), while the induced oracle is by
definition the value the model itself would have returned. -/
theorem run_toLog (s₀ : S) (f : Φ) (l₁ : Log Φ τ)
    (x : TyDen (τ := τ) (instrSrc f)) {s₁ s' : S}
    {v : TyDen (τ := τ) (instrTrg f)}
    (hl₁ : replay (ε := ε) s₀ l₁ = s₁)
    (hr : StateModel.run (ε := ε) f s₁ x = (s', v)) :
    ∃ l' : Log Φ τ,
      (logStateModel (LogInterp.induced (ε := ε) s₀)).run f l₁ x = (l', v) ∧
        replay (ε := ε) s₀ l' = s' := by
  subst hl₁
  by_cases hf : (instrEff f : ε) = (⊥ : ε)
  · rw [StateModel.run_pure (ε := ε) f hf] at hr
    refine ⟨l₁, ?_, congrArg Prod.fst hr⟩
    rw [logStateModel_run_of_pure _ f hf]
    exact congrArg (fun y => (l₁, y)) (congrArg Prod.snd hr)
  · refine ⟨l₁ ++ [⟨f, x⟩], ?_, ?_⟩
    · rw [logStateModel_run_of_impure _ f hf]
      exact congrArg (fun y => (l₁ ++ [⟨f, x⟩], y)) (congrArg Prod.snd hr)
    · rw [replay_append_one]
      exact congrArg Prod.fst hr

mutual

/-- **The lifting lemma.**  Every terminating run of an arbitrary state model is
the image of a terminating run of the log model it induces: if the run starts in
a state represented by the log prefix `l`, then it produces a log `l'`
representing the final state, and the same value.

The statement is generalized over the log prefix `l` — with `l` fixed to the
empty log the induction would not go through, because the initial state of a
sub-derivation is an arbitrary intermediate state, which is only ever presented
to us as `replay s₀ l` for some prefix `l`. -/
theorem Eval.toLog (s₀ : S) {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} {h : HasType Φ Γ β t A}
    {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S} {v : TyDen A} :
    Eval (ε := ε) (S := S) h γ ρ s s' v →
      ∀ l : Log Φ τ, replay (ε := ε) s₀ l = s →
        ∃ l' : Log Φ τ,
          LogEval (LogInterp.induced (ε := ε) s₀) h γ ρ l l' v ∧
            replay (ε := ε) s₀ l' = s'
  | .fv hx γ ρ _ => by
      intro l hl
      letI := logStateModel (LogInterp.induced (Φ := Φ) (τ := τ) (ε := ε) s₀)
      exact ⟨l, Eval.fv hx γ ρ l, hl⟩
  | .bv γ ρ _ => by
      intro l hl
      letI := logStateModel (LogInterp.induced (Φ := Φ) (τ := τ) (ε := ε) s₀)
      exact ⟨l, Eval.bv γ ρ l, hl⟩
  | .unit γ ρ _ => by
      intro l hl
      letI := logStateModel (LogInterp.induced (Φ := Φ) (τ := τ) (ε := ε) s₀)
      exact ⟨l, Eval.unit γ ρ l, hl⟩
  | .op hx hr => by
      intro l hl
      letI := logStateModel (LogInterp.induced (Φ := Φ) (τ := τ) (ε := ε) s₀)
      obtain ⟨l₁, hlog, hl₁⟩ := Eval.toLog s₀ hx l hl
      obtain ⟨l', hrun, hl'⟩ := run_toLog s₀ _ l₁ _ hl₁ hr
      exact ⟨l', Eval.op hlog hrun, hl'⟩
  | .let₁ hx hy => by
      intro l hl
      letI := logStateModel (LogInterp.induced (Φ := Φ) (τ := τ) (ε := ε) s₀)
      obtain ⟨l₁, hlog, hl₁⟩ := Eval.toLog s₀ hx l hl
      obtain ⟨l', hlog', hl'⟩ := Eval.toLog s₀ hy l₁ hl₁
      exact ⟨l', Eval.let₁ hlog hlog', hl'⟩
  | .pair hx hy => by
      intro l hl
      letI := logStateModel (LogInterp.induced (Φ := Φ) (τ := τ) (ε := ε) s₀)
      obtain ⟨l₁, hlog, hl₁⟩ := Eval.toLog s₀ hx l hl
      obtain ⟨l', hlog', hl'⟩ := Eval.toLog s₀ hy l₁ hl₁
      exact ⟨l', Eval.pair hlog hlog', hl'⟩
  | .let₂ hx hy => by
      intro l hl
      letI := logStateModel (LogInterp.induced (Φ := Φ) (τ := τ) (ε := ε) s₀)
      obtain ⟨l₁, hlog, hl₁⟩ := Eval.toLog s₀ hx l hl
      obtain ⟨l', hlog', hl'⟩ := Eval.toLog s₀ hy l₁ hl₁
      exact ⟨l', Eval.let₂ hlog hlog', hl'⟩
  | .inl hx => by
      intro l hl
      letI := logStateModel (LogInterp.induced (Φ := Φ) (τ := τ) (ε := ε) s₀)
      obtain ⟨l', hlog, hl'⟩ := Eval.toLog s₀ hx l hl
      exact ⟨l', Eval.inl hlog, hl'⟩
  | .inr hy => by
      intro l hl
      letI := logStateModel (LogInterp.induced (Φ := Φ) (τ := τ) (ε := ε) s₀)
      obtain ⟨l', hlog, hl'⟩ := Eval.toLog s₀ hy l hl
      exact ⟨l', Eval.inr hlog, hl'⟩
  | .caseL hx hw hy => by
      intro l hl
      letI := logStateModel (LogInterp.induced (Φ := Φ) (τ := τ) (ε := ε) s₀)
      obtain ⟨l₁, hlog, hl₁⟩ := Eval.toLog s₀ hx l hl
      obtain ⟨l', hlog', hl'⟩ := Eval.toLog s₀ hy l₁ hl₁
      exact ⟨l', Eval.caseL hlog hw hlog', hl'⟩
  | .caseR hx hw hy => by
      intro l hl
      letI := logStateModel (LogInterp.induced (Φ := Φ) (τ := τ) (ε := ε) s₀)
      obtain ⟨l₁, hlog, hl₁⟩ := Eval.toLog s₀ hx l hl
      obtain ⟨l', hlog', hl'⟩ := Eval.toLog s₀ hy l₁ hl₁
      exact ⟨l', Eval.caseR hlog hw hlog', hl'⟩
  | .iter hx hloop => by
      intro l hl
      letI := logStateModel (LogInterp.induced (Φ := Φ) (τ := τ) (ε := ε) s₀)
      obtain ⟨l₁, hlog, hl₁⟩ := Eval.toLog s₀ hx l hl
      obtain ⟨l', hlog', hl'⟩ := IterEval.toLog s₀ hloop l₁ hl₁
      exact ⟨l', Eval.iter hlog hlog', hl'⟩
  | .sub hx => by
      intro l hl
      letI := logStateModel (LogInterp.induced (Φ := Φ) (τ := τ) (ε := ε) s₀)
      obtain ⟨l', hlog, hl'⟩ := Eval.toLog s₀ hx l hl
      exact ⟨l', Eval.sub hlog, hl'⟩

/-- The lifting lemma for a successful loop run: each iteration extends the log
built by the previous ones. -/
theorem IterEval.toLog (s₀ : S) {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {b : Tm ν Φ (n + 1)} {A B : τ}
    {hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A)}
    {γ : CtxDen Γ} {ρ : BoundDen β} {x : TyDen A} {s s' : S} {v : TyDen B} :
    IterEval (ε := ε) (S := S) hb γ ρ x s s' v →
      ∀ l : Log Φ τ, replay (ε := ε) s₀ l = s →
        ∃ l' : Log Φ τ,
          LogIterEval (LogInterp.induced (ε := ε) s₀) hb γ ρ x l l' v ∧
            replay (ε := ε) s₀ l' = s'
  | .done hx hw => by
      intro l hl
      letI := logStateModel (LogInterp.induced (Φ := Φ) (τ := τ) (ε := ε) s₀)
      obtain ⟨l', hlog, hl'⟩ := Eval.toLog s₀ hx l hl
      exact ⟨l', IterEval.done hlog hw, hl'⟩
  | .more hx hw rest => by
      intro l hl
      letI := logStateModel (LogInterp.induced (Φ := Φ) (τ := τ) (ε := ε) s₀)
      obtain ⟨l₁, hlog, hl₁⟩ := Eval.toLog s₀ hx l hl
      obtain ⟨l', hlog', hl'⟩ := IterEval.toLog s₀ rest l₁ hl₁
      exact ⟨l', IterEval.more hlog hw hlog', hl'⟩

end

/-- The lifting lemma at the empty log: a terminating run from `s` is a
terminating run of the log model induced by `s` itself, started with no log. -/
theorem Eval.toLogNil (s : S) {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} {h : HasType Φ Γ β t A}
    {γ : CtxDen Γ} {ρ : BoundDen β} {s' : S} {v : TyDen A}
    (he : Eval (ε := ε) (S := S) h γ ρ s s' v) :
    ∃ l' : Log Φ τ,
      LogEval (LogInterp.induced (ε := ε) s) h γ ρ [] l' v ∧
        replay (ε := ε) s l' = s' :=
  Eval.toLog s he [] rfl

end Lifting

/-! ## Terminating state observation -/

section StateObservation

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
variable {a b c : Tm ν Φ n} {A : τ}

/-- Terminating state observational equivalence: the two programs have the same
terminating runs, in every state model.

This is `Observation.ObsEq` with its divergence clause dropped -- which turns
out to drop nothing at all: the two relations are equivalent
(`obsEq_iff_termObsEq`), because `Diverges` is the absence of an `Eval`. -/
def TermObsEq (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b A) : Prop :=
  ∀ (S : Type v) [StateModel Φ τ ε S] (γ : CtxDen Γ) (ρ : BoundDen β)
    (s s' : S) (v : TyDen A),
    Eval (ε := ε) ha γ ρ s s' v ↔ Eval (ε := ε) hb γ ρ s s' v

/-- Terminating state observational equivalence is reflexive. -/
@[refl] theorem TermObsEq.refl (ha : HasType Φ Γ β a A) :
    TermObsEq (ε := ε) ha ha := by
  intro S _ γ ρ s s' v; rfl

/-- Terminating state observational equivalence is symmetric. -/
theorem TermObsEq.symm {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
    (h : TermObsEq (ε := ε) ha hb) : TermObsEq (ε := ε) hb ha := by
  intro S _ γ ρ s s' v; exact (h S γ ρ s s' v).symm

/-- Terminating state observational equivalence is transitive. -/
theorem TermObsEq.trans {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
    {hc : HasType Φ Γ β c A} (h₁ : TermObsEq (ε := ε) ha hb)
    (h₂ : TermObsEq (ε := ε) hb hc) : TermObsEq (ε := ε) ha hc := by
  intro S _ γ ρ s s' v; exact (h₁ S γ ρ s s' v).trans (h₂ S γ ρ s s' v)

/-- State observational equivalence implies its terminating part. -/
theorem Observation.ObsEq.termObsEq {ha : HasType Φ Γ β a A}
    {hb : HasType Φ Γ β b A} (h : Observation.ObsEq (ε := ε) ha hb) :
    TermObsEq (ε := ε) ha hb := by
  intro S _ γ ρ s s' v
  exact h.eval_iff S γ ρ s s' v

/-- **The divergence clause is redundant.**  `Diverges` is the *absence* of an
`Eval`, so agreement of the evaluation relations already forces agreement of
divergence (`Observation.diverges_congr`, via `Observation.obsEq_of_eval_iff`).
`TermObsEq` is therefore not a weakening of `Observation.ObsEq`: they are the
same relation. -/
theorem obsEq_iff_termObsEq {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A} :
    Observation.ObsEq (ε := ε) ha hb ↔ TermObsEq (ε := ε) ha hb :=
  ⟨fun h => h.termObsEq,
   fun h => Observation.obsEq_of_eval_iff (ε := ε)
     (fun S _ γ ρ s s' v => h S γ ρ s s' v)⟩

/-- Soundness of the equational theory for terminating state observation. -/
theorem termObsEq_of_related {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
    (h : TypedEquiv.Related (⊥ : ε) Γ ha hb) : TermObsEq (ε := ε) ha hb :=
  (Observation.obsEq_of_related h).termObsEq

end StateObservation

/-! ## Terminating log observation, and the main theorem -/

section LogObservation

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε] [DecidableEq ε]
variable {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
variable {a b c : Tm ν Φ n} {A : τ}

/-- Terminating log observational equivalence: the two programs have the same
terminating logs, for every pure interpretation and every oracle.

Quantifying over the oracle is what makes this an observation of the log rather
than of one particular run: the two programs must log the same calls however
their impure calls are answered. -/
def TermLogObsEq (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b A) : Prop :=
  ∀ (I : LogInterp Φ τ ε) (γ : CtxDen Γ) (ρ : BoundDen β)
    (l l' : Log Φ τ) (v : TyDen A),
    LogEval I ha γ ρ l l' v ↔ LogEval I hb γ ρ l l' v

/-- Terminating log observational equivalence is reflexive. -/
@[refl] theorem TermLogObsEq.refl (ha : HasType Φ Γ β a A) :
    TermLogObsEq (ε := ε) ha ha := fun _ _ _ _ _ _ => Iff.rfl

/-- Terminating log observational equivalence is symmetric. -/
theorem TermLogObsEq.symm {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
    (h : TermLogObsEq (ε := ε) ha hb) : TermLogObsEq (ε := ε) hb ha :=
  fun I γ ρ l l' v => (h I γ ρ l l' v).symm

/-- Terminating log observational equivalence is transitive. -/
theorem TermLogObsEq.trans {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
    {hc : HasType Φ Γ β c A} (h₁ : TermLogObsEq (ε := ε) ha hb)
    (h₂ : TermLogObsEq (ε := ε) hb hc) : TermLogObsEq (ε := ε) ha hc :=
  fun I γ ρ l l' v => (h₁ I γ ρ l l' v).trans (h₂ I γ ρ l l' v)

/-- **The main theorem.**  Restricted to terminating runs, state observation and
log observation coincide.

Forward, a log model *is* a state model, so terminating log equivalence is an
instance of terminating state equivalence.  Backward, a terminating run of an
arbitrary state model lifts to a terminating run of the log model it induces
(`Eval.toLog`), which log equivalence transports to the other program, and which
`eval_of_logEval` pushes back to the original model along `replay`. -/
theorem termObsEq_iff_termLogObsEq {ha : HasType Φ Γ β a A}
    {hb : HasType Φ Γ β b A} :
    TermObsEq (ε := ε) ha hb ↔ TermLogObsEq (ε := ε) ha hb := by
  constructor
  · intro h I γ ρ l l' v
    letI := logStateModel I
    exact h (Log Φ τ) γ ρ l l' v
  · intro h S _ γ ρ s s' v
    constructor
    · intro he
      obtain ⟨l', hlog, hl'⟩ := Eval.toLogNil s he
      have hpush := eval_of_logEval s
        ((h (LogInterp.induced (ε := ε) s) γ ρ [] l' v).1 hlog)
      rwa [replay_nil, hl'] at hpush
    · intro he
      obtain ⟨l', hlog, hl'⟩ := Eval.toLogNil s he
      have hpush := eval_of_logEval s
        ((h (LogInterp.induced (ε := ε) s) γ ρ [] l' v).2 hlog)
      rwa [replay_nil, hl'] at hpush

/-- State observational equivalence implies terminating log equivalence. -/
theorem Observation.ObsEq.termLogObsEq {ha : HasType Φ Γ β a A}
    {hb : HasType Φ Γ β b A} (h : Observation.ObsEq (ε := ε) ha hb) :
    TermLogObsEq (ε := ε) ha hb :=
  termObsEq_iff_termLogObsEq.mp h.termObsEq

/-- **Soundness of the equational theory for the log.**  Programs related by the
equational theory have the same terminating logs, under every pure
interpretation and every oracle.

This is the payoff of the main theorem: soundness was proved once, for the
denotational semantics, and it transfers to an observation of effects that the
final state cannot see. -/
theorem termLogObsEq_of_related {ha : HasType Φ Γ β a A}
    {hb : HasType Φ Γ β b A} (h : TypedEquiv.Related (⊥ : ε) Γ ha hb) :
    TermLogObsEq (ε := ε) ha hb :=
  (Observation.obsEq_of_related h).termLogObsEq

/-- Soundness of the equational theory for the log, from a derivation. -/
theorem termLogObsEq_of_deriv {ha : HasType Φ Γ β a A}
    {hb : HasType Φ Γ β b A} (d : TypedEquiv.Deriv (⊥ : ε) Γ ha hb) :
    TermLogObsEq (ε := ε) ha hb :=
  termLogObsEq_of_related ⟨d⟩

end LogObservation

/-! ## Non-vacuity: the log separates a `tick` from a no-op -/

namespace Example

/-- `()` logs nothing. -/
theorem logEval_unitTm :
    LogEval logInterp Counterexample.unitTmTy PUnit.unit PUnit.unit
      ([] : Log Instr (Ty Base)) [] (TypeModel.unitEquiv.symm ()) := by
  letI := logStateModel logInterp
  exact .unit _ _ _

/-- `let _ = tick (); ()` logs exactly its one call to `tick`. -/
theorem logEval_tickTm :
    LogEval logInterp Counterexample.tickTmTy PUnit.unit PUnit.unit
      ([] : Log Instr (Ty Base)) [⟨Instr.tick, ()⟩]
      (TypeModel.unitEquiv.symm ()) := by
  letI := logStateModel logInterp
  exact .let₁ (.op (.unit _ _ _) (logStateModel_tick [] ())) (.unit _ _ _)

/-- The log observation is not vacuous: `()` and `let _ = tick (); ()` both
terminate, and are separated by their logs — `[]` against `[⟨tick, ()⟩]` — under
the concrete interpretation `logInterp`. -/
theorem not_termLogObsEq_unitTm_tickTm :
    ¬ TermLogObsEq (ε := Effect) Counterexample.unitTmTy
        Counterexample.tickTmTy := by
  intro h
  letI := logStateModel logInterp
  have hb := (h logInterp PUnit.unit PUnit.unit ([] : Log Instr (Ty Base)) []
    (TypeModel.unitEquiv.symm ())).mp logEval_unitTm
  have hlog := (Eval.deterministic hb logEval_tickTm).1
  exact absurd hlog (by simp)

/-- Consequently the two programs are not terminating-state observationally
equivalent either, by the main theorem. -/
theorem not_termObsEq_unitTm_tickTm :
    ¬ TermObsEq (ε := Effect) Counterexample.unitTmTy
        Counterexample.tickTmTy :=
  fun h => not_termLogObsEq_unitTm_tickTm (termObsEq_iff_termLogObsEq.mp h)

end Example

end Isotope.LambdaIter.Opsem
