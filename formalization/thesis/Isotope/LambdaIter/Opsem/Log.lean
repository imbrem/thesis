import Isotope.LambdaIter.Opsem.BigStep

/-!
# The log model: making the log of effectful calls the state

`Isotope.LambdaIter.Opsem.ModelObsEq` observes a program by its *final state*,
and a program that never returns has no final state: divergent computations are
all identified, which is precisely why the equational theory is not complete for
state observation (`Isotope.LambdaIter.Opsem.Counterexample.completeness_fails`).

The observation we actually want is the (potentially infinite) *log* of
effectful calls: which instruction was called, and on which argument.  This file
builds that observation out of the machinery already in place, with no new
semantics: **the log is the state.**  A `logStateModel` runs an instruction by

* doing nothing to the log when the instruction is pure — this is what makes
  pure instructions invisible to the log, and it is forced by the purity law of
  a `StateModel`; and
* appending the `Event` `⟨f, a⟩` to the log when the instruction is impure.

An impure call must still be answered with a value of its target type, and the
answer may depend on everything that has happened so far; that datum is an
*oracle*, a function of the log prefix.  So a log model is exactly a pure
interpretation together with an oracle: a `LogInterp`.

The bridge to an arbitrary state model is a **homomorphism of state models**
(`Hom`): a map on states commuting with `run` in both components.  `Eval.map`
transports a terminating evaluation along any such homomorphism.  `replay`,
which folds `run` over a log, is a homomorphism out of the log model induced by
a state model and an initial state (`replayHom`), so every terminating log run
is a terminating run of every state model (`eval_of_logEval`).  This is the
direction of the main theorem that holds for *all* runs; its converse needs the
run to terminate, which is exactly the restriction under which state
observational equivalence and log observational equivalence agree.

## Universes

An `Event` bundles an instruction with an argument, so it lives in
`Type (max q v)` where `Φ : Type q` and `v` is the interpretation universe fixed
by `TypeModel.{u, v} τ`.  A `StateModel`'s state set must live in the
interpretation universe, so the log sections of this file take **`Φ : Type v`**:
the signature lives in the interpretation universe.  This is satisfied by
`Isotope.LambdaIter.Opsem.Example` (`Instr : Type`, `v = 0`).  The
homomorphism section is stated for a general `Φ : Type q`.
-/

namespace Isotope.LambdaIter.Opsem

open Isotope.LambdaIter.Subtyping.Semantics
open Isotope.LambdaIter.LocallyNameless
open Isotope.LambdaIter.Subtyping.LocallyNameless

universe u v w q r

/-! ## Homomorphisms of state models -/

section Homomorphism

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {S T : Type v}

/-- A homomorphism of state models: a map on states which commutes with `run`,
in both components at once.  The state component says that `map` transports the
state transition of every instruction; the value component says that the value
returned by an instruction is unchanged, so no observation of the returned value
can tell the two models apart. -/
structure Hom (M : StateModel Φ τ ε S) (N : StateModel Φ τ ε T) where
  /-- The underlying map on states. -/
  map : S → T
  /-- The map commutes with `run`: applying it to the resulting state, and
  leaving the returned value alone, turns a step of `M` into a step of `N`. -/
  map_run (f : Φ) (s : S) (a : TyDen (τ := τ) (instrSrc f)) :
    Prod.map map id (M.run f s a) = N.run f (map s) a

namespace Hom

variable {M : StateModel Φ τ ε S} {N : StateModel Φ τ ε T}

/-- The state component of the commutation law. -/
theorem map_run_fst (φ : Hom M N) (f : Φ) (s : S)
    (a : TyDen (τ := τ) (instrSrc f)) :
    φ.map (M.run f s a).1 = (N.run f (φ.map s) a).1 :=
  congrArg Prod.fst (φ.map_run f s a)

/-- The value component of the commutation law. -/
theorem map_run_snd (φ : Hom M N) (f : Φ) (s : S)
    (a : TyDen (τ := τ) (instrSrc f)) :
    (M.run f s a).2 = (N.run f (φ.map s) a).2 :=
  congrArg Prod.snd (φ.map_run f s a)

end Hom

end Homomorphism

/-! ## Transporting evaluations along a homomorphism -/

section Transport

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {S T : Type v} [M : StateModel Φ τ ε S] [N : StateModel Φ τ ε T]

mutual

/-- A terminating evaluation is transported along a homomorphism of state
models: the same derivation, the same value, and the mapped states. -/
theorem Eval.map (φ : Hom M N) {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} {h : HasType Φ Γ β t A}
    {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S} {v : TyDen A} :
    Eval (ε := ε) (S := S) h γ ρ s s' v →
      Eval (ε := ε) (S := T) h γ ρ (φ.map s) (φ.map s') v
  | .fv hx γ ρ s => .fv hx γ ρ (φ.map s)
  | .bv γ ρ s => .bv γ ρ (φ.map s)
  | .unit γ ρ s => .unit γ ρ (φ.map s)
  | .op hx hr => by
      refine .op (Eval.map φ hx) ?_
      rw [← φ.map_run, hr]
      rfl
  | .let₁ hx hy => .let₁ (Eval.map φ hx) (Eval.map φ hy)
  | .pair hx hy => .pair (Eval.map φ hx) (Eval.map φ hy)
  | .let₂ hx hy => .let₂ (Eval.map φ hx) (Eval.map φ hy)
  | .inl hx => .inl (Eval.map φ hx)
  | .inr hy => .inr (Eval.map φ hy)
  | .caseL hx hw hy => .caseL (Eval.map φ hx) hw (Eval.map φ hy)
  | .caseR hx hw hy => .caseR (Eval.map φ hx) hw (Eval.map φ hy)
  | .iter hx hloop => .iter (Eval.map φ hx) (IterEval.map φ hloop)
  | .sub hx => .sub (Eval.map φ hx)

/-- A successful loop run is transported along a homomorphism of state
models. -/
theorem IterEval.map (φ : Hom M N) {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {b : Tm ν Φ (n + 1)} {A B : τ}
    {hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A)}
    {γ : CtxDen Γ} {ρ : BoundDen β} {x : TyDen A} {s s' : S} {v : TyDen B} :
    IterEval (ε := ε) (S := S) hb γ ρ x s s' v →
      IterEval (ε := ε) (S := T) hb γ ρ x (φ.map s) (φ.map s') v
  | .done hx hw => .done (Eval.map φ hx) hw
  | .more hx hw rest => .more (Eval.map φ hx) hw (IterEval.map φ rest)

end

end Transport

/-! ## Events and logs -/

section Events

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]

/-- One entry of a log: an instruction together with the argument it was called
on.  This is the complete record of a single effectful call, and it is
everything the log observes about it. -/
structure Event (Φ : Type v) (τ : Type u) [TypeFormers τ] [Subtyping τ]
    [TypeModel.{u, v} τ] [HasTy Φ τ] : Type v where
  /-- The instruction that was called. -/
  instr : Φ
  /-- The argument it was called on. -/
  arg : TyDen (τ := τ) (instrSrc instr)

/-- Two events are equal when their instructions are equal and their arguments
are heterogeneously equal; the arguments cannot be compared homogeneously,
because their type depends on the instruction. -/
@[ext] theorem Event.ext {e₁ e₂ : Event Φ τ} (hf : e₁.instr = e₂.instr)
    (ha : HEq e₁.arg e₂.arg) : e₁ = e₂ := by
  cases e₁; cases e₂
  cases hf
  cases ha
  rfl

/-- A log: the finite sequence of effectful calls made so far, oldest first. -/
abbrev Log (Φ : Type v) (τ : Type u) [TypeFormers τ] [Subtyping τ]
    [TypeModel.{u, v} τ] [HasTy Φ τ] : Type v := List (Event Φ τ)

/-- The data determining a log model: how the pure instructions compute, and how
the impure ones are answered.  The `oracle` is a function of the log prefix, so
an impure call may be answered on the basis of everything that has happened
before it, and of nothing else. -/
structure LogInterp (Φ : Type v) (τ : Type u) (ε : Type r) [TypeFormers τ]
    [Subtyping τ] [TypeModel.{u, v} τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε] where
  /-- The state-free function computed by a `⊥`-effect instruction. -/
  pureFn (f : Φ) (hf : (instrEff f : ε) = (⊥ : ε)) :
    TyDen (τ := τ) (instrSrc f) → TyDen (τ := τ) (instrTrg f)
  /-- The answer given to an impure call, as a function of the log so far. -/
  oracle (l : Log Φ τ) (f : Φ) (a : TyDen (τ := τ) (instrSrc f)) :
    TyDen (τ := τ) (instrTrg f)

/-! ## The log model

Making the log the state.  This is a `def` and deliberately **not** an
`instance`: there is one log model per `LogInterp`, so a global instance would
both be wrong and make instance resolution ambiguous. -/

/-- The log model of a `LogInterp`: the state is the log so far, a pure
instruction leaves it alone, and an impure instruction appends its call to it
and is answered by the oracle. -/
@[reducible] def logStateModel [DecidableEq ε] (I : LogInterp Φ τ ε) :
    StateModel Φ τ ε (Log Φ τ) where
  run f l a :=
    if hf : (instrEff f : ε) = (⊥ : ε) then (l, I.pureFn f hf a)
    else (l ++ [⟨f, a⟩], I.oracle l f a)
  pureFn := I.pureFn
  run_pure _ hf _ _ := dif_pos hf

/-- A pure instruction leaves the log alone and computes by the pure
interpretation: it is invisible to the log. -/
@[simp] theorem logStateModel_run_of_pure [DecidableEq ε] (I : LogInterp Φ τ ε)
    (f : Φ) (hf : (instrEff f : ε) = (⊥ : ε)) (l : Log Φ τ)
    (a : TyDen (τ := τ) (instrSrc f)) :
    (logStateModel I).run f l a = (l, I.pureFn f hf a) := dif_pos hf

/-- An impure instruction appends its call to the log and is answered by the
oracle. -/
@[simp] theorem logStateModel_run_of_impure [DecidableEq ε] (I : LogInterp Φ τ ε)
    (f : Φ) (hf : ¬ (instrEff f : ε) = (⊥ : ε)) (l : Log Φ τ)
    (a : TyDen (τ := τ) (instrSrc f)) :
    (logStateModel I).run f l a = (l ++ [⟨f, a⟩], I.oracle l f a) := dif_neg hf

end Events

/-! ## Evaluation in a log model -/

section Evaluation

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε] [DecidableEq ε]
variable {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}

/-- Evaluation in the log model of `I`: `LogEval I h γ ρ l l' v` says that the
program typed by `h`, started with log prefix `l`, terminates with log `l'` and
value `v`. -/
def LogEval (I : LogInterp Φ τ ε) {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β t A) (γ : CtxDen Γ) (ρ : BoundDen β)
    (l l' : Log Φ τ) (v : TyDen A) : Prop :=
  letI := logStateModel I
  Eval (ε := ε) (S := Log Φ τ) h γ ρ l l' v

/-- A successful loop run in the log model of `I`. -/
def LogIterEval (I : LogInterp Φ τ ε) {b : Tm ν Φ (n + 1)} {A B : τ}
    (hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A))
    (γ : CtxDen Γ) (ρ : BoundDen β) (x : TyDen A)
    (l l' : Log Φ τ) (v : TyDen B) : Prop :=
  letI := logStateModel I
  IterEval (ε := ε) (S := Log Φ τ) hb γ ρ x l l' v

/-- `LogEval` is evaluation in the log model, by definition. -/
theorem logEval_iff (I : LogInterp Φ τ ε) {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β t A) (γ : CtxDen Γ) (ρ : BoundDen β)
    (l l' : Log Φ τ) (v : TyDen A) :
    LogEval I h γ ρ l l' v ↔
      letI := logStateModel I
      Eval (ε := ε) (S := Log Φ τ) h γ ρ l l' v := Iff.rfl

/-- `LogIterEval` is a loop run in the log model, by definition. -/
theorem logIterEval_iff (I : LogInterp Φ τ ε) {b : Tm ν Φ (n + 1)} {A B : τ}
    (hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A))
    (γ : CtxDen Γ) (ρ : BoundDen β) (x : TyDen A)
    (l l' : Log Φ τ) (v : TyDen B) :
    LogIterEval I hb γ ρ x l l' v ↔
      letI := logStateModel I
      IterEval (ε := ε) (S := Log Φ τ) hb γ ρ x l l' v := Iff.rfl

end Evaluation

/-! ## Replaying a log in a state model -/

section Replay

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {S : Type v} [M : StateModel Φ τ ε S]

/-- Replay a log in a state model: run every logged call, in order, from the
given initial state. -/
def replay (s : S) : Log Φ τ → S
  | [] => s
  | e :: l => replay (M.run e.instr s e.arg).1 l

/-- Replaying the empty log does nothing. -/
@[simp] theorem replay_nil (s : S) : replay (ε := ε) s ([] : Log Φ τ) = s := rfl

/-- Replaying a cons runs the first call and continues. -/
@[simp] theorem replay_cons (s : S) (e : Event Φ τ) (l : Log Φ τ) :
    replay (ε := ε) s (e :: l) = replay (ε := ε) (M.run e.instr s e.arg).1 l := rfl

/-- Replaying a log extended by one call runs that call last. -/
theorem replay_append_one (s : S) (l : Log Φ τ) (e : Event Φ τ) :
    replay (ε := ε) s (l ++ [e]) =
      (M.run e.instr (replay (ε := ε) s l) e.arg).1 := by
  induction l generalizing s with
  | nil => rfl
  | cons e' l ih => simpa using ih _

/-- The log interpretation *induced* by a state model and an initial state: the
pure instructions compute as they do in the model, and an impure call is
answered by replaying the log so far and running the call from there. -/
def LogInterp.induced (s₀ : S) : LogInterp Φ τ ε where
  pureFn f hf := StateModel.pureFn S f hf
  oracle l f a := (M.run f (replay (ε := ε) s₀ l) a).2

/-- Replaying is a homomorphism from the log model of the induced
interpretation to the state model itself.

The pure case is exactly the purity law of a state model: the log is unchanged,
*and* the value returned by a pure instruction does not depend on the state, so
it agrees with the value the log model computed.  The impure case is the
definition of the induced oracle together with `replay_append_one`. -/
def replayHom [DecidableEq ε] (s₀ : S) :
    Hom (logStateModel (LogInterp.induced (ε := ε) s₀)) M where
  map := replay (ε := ε) s₀
  map_run f l a := by
    by_cases hf : (instrEff f : ε) = (⊥ : ε)
    · rw [logStateModel_run_of_pure _ f hf, StateModel.run_pure (ε := ε) f hf]
      rfl
    · rw [logStateModel_run_of_impure _ f hf]
      change ((replay (ε := ε) s₀ (l ++ [⟨f, a⟩])), _) = _
      rw [replay_append_one]
      rfl

end Replay

/-! ## Terminating log runs are runs of every state model -/

section Adequacy

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε] [DecidableEq ε]
variable {S : Type v} [M : StateModel Φ τ ε S]
variable {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}

/-- A terminating run in the induced log model is a terminating run of the state
model itself, along the replay map: the log records enough of what happened to
reconstruct the final state. -/
theorem eval_of_logEval (s₀ : S) {t : Tm ν Φ n} {A : τ}
    {h : HasType Φ Γ β t A} {γ : CtxDen Γ} {ρ : BoundDen β}
    {l l' : Log Φ τ} {v : TyDen A}
    (he : LogEval (LogInterp.induced (ε := ε) s₀) h γ ρ l l' v) :
    Eval (ε := ε) h γ ρ (replay (ε := ε) s₀ l) (replay (ε := ε) s₀ l') v :=
  Eval.map (M := logStateModel (LogInterp.induced (ε := ε) s₀)) (replayHom s₀) he

/-- A successful loop run in the induced log model is a successful loop run of
the state model itself, along the replay map. -/
theorem iterEval_of_logIterEval (s₀ : S) {b : Tm ν Φ (n + 1)} {A B : τ}
    {hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A)}
    {γ : CtxDen Γ} {ρ : BoundDen β} {x : TyDen A}
    {l l' : Log Φ τ} {v : TyDen B}
    (he : LogIterEval (LogInterp.induced (ε := ε) s₀) hb γ ρ x l l' v) :
    IterEval (ε := ε) hb γ ρ x (replay (ε := ε) s₀ l) (replay (ε := ε) s₀ l') v :=
  IterEval.map (M := logStateModel (LogInterp.induced (ε := ε) s₀)) (replayHom s₀) he

end Adequacy

/-! ## The log model of the worked example -/

namespace Example

/-- A log interpretation for the example signature: `succ` computes as usual,
and the oracle answers `tick` with the unit value (its target type has no other
inhabitant). -/
def logInterp : LogInterp Instr (Ty Base) Effect where
  pureFn := pureFnInstr
  oracle _ f _ :=
    match f with
    | .succ => (0 : Nat)
    | .tick => ()

/-- The pure instruction `succ` leaves the log alone. -/
theorem logStateModel_succ (l : Log Instr (Ty Base)) (a : Nat) :
    (logStateModel logInterp).run Instr.succ l a = (l, a + 1) :=
  logStateModel_run_of_pure logInterp Instr.succ rfl l a

/-- The impure instruction `tick` appends its call to the log. -/
theorem logStateModel_tick (l : Log Instr (Ty Base)) (a : Unit) :
    (logStateModel logInterp).run Instr.tick l a =
      (l ++ [⟨Instr.tick, a⟩], ()) :=
  logStateModel_run_of_impure logInterp Instr.tick impure_ne_bot l a

/-- A one-call example program: `let _ = tick (); ()`. -/
def tickOnce : Tm Empty Instr 0 := .let₁ (.op Instr.tick .unit) .unit

/-- The typing derivation of `tickOnce`. -/
def tickOnceTy :
    HasType Instr (.nil : Ctx Empty (Ty Base)) .nil tickOnce Ty.unit :=
  .let₁ (.op (f := Instr.tick) .unit) .unit

/-- `tickOnce` logs exactly one event, its single call to `tick`.  Log models
are therefore not vacuous: a terminating program does record its effects. -/
theorem logEval_tickOnce :
    LogEval logInterp tickOnceTy PUnit.unit PUnit.unit
      ([] : Log Instr (Ty Base)) [⟨Instr.tick, ()⟩]
      (TypeModel.unitEquiv.symm ()) := by
  letI := logStateModel logInterp
  exact .let₁ (.op (.unit _ _ _) (logStateModel_tick [] ())) (.unit _ _ _)

/-- Replaying that log in the `Nat`-state example model performs the `tick`:
the log really does reconstruct the final state. -/
theorem eval_tickOnce (s₀ : Nat) :
    Eval (ε := Effect) tickOnceTy PUnit.unit PUnit.unit s₀ (s₀ + 1)
      (TypeModel.unitEquiv.symm ()) := by
  have hr := logStateModel_run_of_impure
    (LogInterp.induced (Φ := Instr) (τ := Ty Base) (ε := Effect) s₀)
    Instr.tick impure_ne_bot [] ()
  refine eval_of_logEval s₀ (h := tickOnceTy)
    (l := ([] : Log Instr (Ty Base))) (l' := [⟨Instr.tick, ()⟩]) ?_
  letI := logStateModel
    (LogInterp.induced (Φ := Instr) (τ := Ty Base) (ε := Effect) s₀)
  exact .let₁ (.op (.unit _ _ _) hr) (.unit _ _ _)

end Example

end Isotope.LambdaIter.Opsem
