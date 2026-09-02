import Isotope.Elgot.StateT
import Isotope.LambdaIter.Subtyping.Semantics.Instruction

/-!
# State models: the semantics of the individual operations

An *operational* reading of `λ_iter` fixes an abstract set `S` of machine
states and says what each primitive instruction *does* to a state.  A
`StateModel` records exactly that datum, and nothing else:

* `run f` is a **total** and **deterministic** state transformer.  It is a
  genuine function `S → ⟦src f⟧ → S × ⟦trg f⟧`, so an instruction can neither
  fail, nor diverge, nor make a nondeterministic choice.  All partiality in the
  language comes from `iter`, and from `iter` alone.
* `run_pure` is the **purity law**: an instruction whose effect is `⊥` neither
  *writes* nor *reads* the state.  Writing `run f s a = (s, pureFn f hf a)`
  with `pureFn f hf` a function of the argument alone forces both halves at
  once: the returned state is the incoming state `s` (no writes), and the
  returned value is independent of `s` (no reads).  Read-only instructions are
  deliberately excluded: an instruction that merely observed the state would
  already break the pure-substitution rule `letBeta`, which duplicates and
  reorders pure subterms.

Everything else about `S` is abstract: a state model may not assume anything
about states beyond what `run` says.

The operational semantics *is* the denotational semantics in the Elgot monad
`StateT S Part`: `instructionModelOfStateModel` turns a state model into an
`InstructionModel` for `PartState S = StateT S Part`, and
`Isotope.Elgot.StateT.instLawfulElgotMonad` makes that monad a
`LawfulElgotMonad`, so `Isotope.LambdaIter.Subtyping.Semantics.denote` and
`Isotope.LambdaIter.Subtyping.Semantics.sound` apply verbatim.
-/

namespace Isotope.LambdaIter.Opsem

open Isotope.LambdaIter.Subtyping.Semantics

universe u v w x

/-- The semantics of the individual operations of `λ_iter`, over an abstract
state set `S`.

`run f` is a *total, deterministic* state transformer: instructions are neither
partial nor nondeterministic.  `run_pure` is the purity law: a `⊥`-effect
instruction neither writes nor reads the state. -/
class StateModel (Φ : Type u) (τ : Type v) (ε : Type w) (S : Type x)
    [TypeFormers τ] [Subtyping τ] [TypeModel.{v, x} τ]
    [HasTy Φ τ] [HasEff Φ ε] [Bot ε] where
  /-- The total, deterministic state transformer executed by an instruction. -/
  run (f : Φ) : S → TyDen (τ := τ) (instrSrc f) → S × TyDen (τ := τ) (instrTrg f)
  /-- The state-free function computed by a `⊥`-effect instruction. -/
  pureFn (f : Φ) (hf : (instrEff f : ε) = (⊥ : ε)) :
    TyDen (τ := τ) (instrSrc f) → TyDen (τ := τ) (instrTrg f)
  /-- Purity law: a `⊥`-effect instruction returns the incoming state unchanged
  (it performs no write) and returns a value independent of that state (it
  performs no read). -/
  run_pure (f : Φ) (hf : (instrEff f : ε) = (⊥ : ε)) (s : S)
      (a : TyDen (τ := τ) (instrSrc f)) :
    run f s a = (s, pureFn f hf a)

namespace StateModel

variable {Φ : Type u} {τ : Type v} {ε : Type w} {S : Type x}
  [TypeFormers τ] [Subtyping τ] [TypeModel.{v, x} τ]
  [HasTy Φ τ] [HasEff Φ ε] [Bot ε]

/-- The `StateT S Part` computation executed by an instruction: run the state
transformer and return, with the pair reassociated into `StateT`'s
`(value, state)` order.  It is everywhere defined, since `run` is total. -/
def runT [StateModel Φ τ ε S] (f : Φ) :
    TyDen (τ := τ) (instrSrc f) → Elgot.PartState S (TyDen (τ := τ) (instrTrg f)) :=
  fun a s ↦ Part.some (Prod.swap (StateModel.run (ε := ε) f s a))

/-- Computation rule for `runT`. -/
@[simp] theorem runT_apply [StateModel Φ τ ε S] (f : Φ)
    (a : TyDen (τ := τ) (instrSrc f)) (s : S) :
    runT (ε := ε) f a s =
      Part.some ((StateModel.run (ε := ε) f s a).2, (StateModel.run (ε := ε) f s a).1) :=
  rfl

end StateModel

/-- Every state model *is* an instruction model for `StateT S Part`: the
operational semantics of `λ_iter` is its denotational semantics in the Elgot
monad of partial state transformers. -/
instance instructionModelOfStateModel {Φ : Type u} {τ : Type v} {ε : Type w} {S : Type x}
    [TypeFormers τ] [Subtyping τ] [TypeModel.{v, x} τ]
    [HasTy Φ τ] [HasEff Φ ε] [Bot ε] [StateModel Φ τ ε S] :
    InstructionModel Φ τ ε (Elgot.PartState S) where
  denote f := StateModel.runT (ε := ε) f
  denotePure f hf := StateModel.pureFn (Φ := Φ) (τ := τ) (ε := ε) (S := S) f hf
  denote_pure f hf a := by
    funext s
    rw [StateModel.runT_apply, StateModel.run_pure (ε := ε) f hf s a]
    rfl

/-! ## A worked example

One base type of natural numbers, one pure instruction `succ : nat → nat`, and
one impure instruction `tick : unit → unit` which increments a state of type
`Nat`.  This is a complete, elaborated state model; it is the model the
counterexample development reuses, so every piece is a named definition. -/

namespace Example

/-- The single base type of the example signature. -/
inductive Base
  | nat
  deriving DecidableEq, Repr

/-- The example effect lattice: `pure` is the bottom effect, `impure` is not. -/
inductive Effect
  | pure
  | impure
  deriving DecidableEq, Repr

instance : Bot Effect := ⟨Effect.pure⟩

/-- The bottom effect of the example is `pure`. -/
@[simp] theorem bot_effect : (⊥ : Effect) = Effect.pure := rfl

/-- `impure` is not the bottom effect. -/
theorem impure_ne_bot : Effect.impure ≠ (⊥ : Effect) := by decide

/-- The example signature: a pure successor and a state-incrementing tick. -/
inductive Instr
  | succ
  | tick
  deriving DecidableEq, Repr

instance : HasTy Instr (Ty Base) where
  src
    | .succ => .base .nat
    | .tick => .unit
  trg
    | .succ => .base .nat
    | .tick => .unit

instance : HasEff Instr Effect where
  eff
    | .succ => Effect.pure
    | .tick => Effect.impure

/-- `succ` consumes a natural number. -/
@[simp] theorem instrSrc_succ : instrSrc Instr.succ = Ty.base Base.nat := rfl
/-- `succ` produces a natural number. -/
@[simp] theorem instrTrg_succ : instrTrg Instr.succ = Ty.base Base.nat := rfl
/-- `tick` consumes the unit value. -/
@[simp] theorem instrSrc_tick : instrSrc Instr.tick = (Ty.unit : Ty Base) := rfl
/-- `tick` produces the unit value. -/
@[simp] theorem instrTrg_tick : instrTrg Instr.tick = (Ty.unit : Ty Base) := rfl
/-- `succ` carries the bottom effect. -/
@[simp] theorem instrEff_succ : (instrEff Instr.succ : Effect) = ⊥ := rfl
/-- `tick` carries the non-bottom effect `impure`. -/
@[simp] theorem instrEff_tick : (instrEff Instr.tick : Effect) = Effect.impure := rfl

/-- `succ` is pure. -/
theorem succ_isPure : IsPure (⊥ : Effect) Instr.succ := rfl

/-- `tick` is not pure. -/
theorem tick_not_isPure : ¬ IsPure (⊥ : Effect) Instr.tick := fun h ↦ impure_ne_bot h

/-- The standard set-valued interpretation of the example types. -/
def interp : Ty Base → Type
  | .base .nat => Nat
  | .tensor A B => interp A × interp B
  | .unit => Unit
  | .coprod A B => interp A ⊕ interp B
  | .empty => Empty

/-- The coercion denoted by a subtyping derivation. -/
def coeSubty : {A B : Ty Base} → Ty.Subty A B → interp A → interp B
  | _, _, .refl _ => id
  | _, _, .trans f g => coeSubty g ∘ coeSubty f
  | _, _, .tensor f g => fun p ↦ (coeSubty f p.1, coeSubty g p.2)
  | _, _, .coprod f g => Sum.map (coeSubty f) (coeSubty g)
  | _, _, .empty _ => fun z ↦ z.elim
  | _, _, .unit _ => fun _ ↦ ()

instance instTypeModel : TypeModel.{0, 0} (Ty Base) where
  interp := interp
  tensorEquiv A B := Equiv.refl (interp A × interp B)
  unitEquiv := Equiv.refl Unit
  coprodEquiv A B := Equiv.refl (interp A ⊕ interp B)
  emptyEquiv := Equiv.refl Empty
  coe := coeSubty

/-- The base type denotes the natural numbers. -/
@[simp] theorem tyDen_base_nat : TyDen (τ := Ty Base) (Ty.base Base.nat) = Nat := rfl

/-- The unit type denotes `Unit`. -/
@[simp] theorem tyDen_unit : TyDen (τ := Ty Base) (Ty.unit : Ty Base) = Unit := rfl

/-- The state transformer executed by each example instruction: `succ`
increments its argument and leaves the state alone, while `tick` increments the
state and returns the unit value. -/
def runInstr : (f : Instr) → Nat →
    TyDen (τ := Ty Base) (instrSrc f) → Nat × TyDen (τ := Ty Base) (instrTrg f)
  | .succ, s, a => (((s, Nat.succ a) : Nat × Nat))
  | .tick, s, _ => (((s + 1, ()) : Nat × Unit))

/-- The state-free function computed by a `⊥`-effect example instruction. -/
def pureFnInstr : (f : Instr) → (instrEff f : Effect) = (⊥ : Effect) →
    TyDen (τ := Ty Base) (instrSrc f) → TyDen (τ := Ty Base) (instrTrg f)
  | .succ, _ => (Nat.succ : Nat → Nat)
  | .tick, hf => absurd hf impure_ne_bot

/-- The example state model: states are natural numbers, `succ` increments its
argument without touching the state, and `tick` increments the state while
returning the unit value. -/
instance instStateModel : StateModel Instr (Ty Base) Effect Nat where
  run := runInstr
  pureFn := pureFnInstr
  run_pure
    | .succ, _, _, _ => rfl
    | .tick, hf, _, _ => absurd hf impure_ne_bot

/-- The state model's `run` is `runInstr`. -/
@[simp] theorem run_eq_runInstr :
    StateModel.run (Φ := Instr) (τ := Ty Base) (ε := Effect) (S := Nat) = runInstr := rfl

/-- `succ` increments its argument and leaves the state alone. -/
@[simp] theorem runInstr_succ (s a : Nat) :
    runInstr Instr.succ s a = (((s, a + 1) : Nat × Nat)) := rfl

/-- `tick` increments the state and returns the unit value. -/
@[simp] theorem runInstr_tick (s : Nat) (a : Unit) :
    runInstr Instr.tick s a = (((s + 1, ()) : Nat × Unit)) := rfl

/-- Running `succ` in the derived instruction model leaves the state alone. -/
theorem denote_succ (a s : Nat) :
    InstructionModel.denote (Φ := Instr) (τ := Ty Base) (ε := Effect)
      (m := Elgot.PartState Nat) Instr.succ a s = Part.some ((a + 1, s) : Nat × Nat) := rfl

/-- Running `tick` in the derived instruction model increments the state. -/
theorem denote_tick (a : Unit) (s : Nat) :
    InstructionModel.denote (Φ := Instr) (τ := Ty Base) (ε := Effect)
      (m := Elgot.PartState Nat) Instr.tick a s = Part.some (((), s + 1) : Unit × Nat) := rfl

/-- The derived instruction model, and the Elgot structure of the monad it lives
in, are found by instance synthesis. -/
noncomputable example :
    InstructionModel Instr (Ty Base) Effect (Elgot.PartState Nat) := inferInstance

noncomputable example : Elgot.Iterate (Elgot.PartState Nat) := inferInstance

example : Elgot.LawfulElgotMonad (Elgot.PartState Nat) := inferInstance

end Example

end Isotope.LambdaIter.Opsem
