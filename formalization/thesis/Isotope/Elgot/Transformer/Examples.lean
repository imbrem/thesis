import Isotope.Elgot.Transformer.Reader
import Isotope.Elgot.Transformer.State
import Isotope.Elgot.Transformer.Writer.Divergence
import Isotope.Elgot.Nondet
import Mathlib.Data.Set.Functor

/-!
# Worked models of the Elgot transformers

The transformers of this directory are instantiated at the two concrete Elgot monads available
here: `Part` (divergence-sensitive, partial) and `Set` (unbounded angelic nondeterminism).  Each
example is a small theorem separating genuinely different computations — a stateful loop that
counts down, a stateful loop that spins, a reader-dependent loop whose termination depends on the
environment, a nondeterministic stateful loop reaching every state, and a writer loop that emits
output and then diverges.

`Part`'s iteration operator is noncomputable, so every instance statement about a `Part`-based
transformer needs a `noncomputable` marker.  `Set` is not a global `Monad` in Mathlib, so the
`Set`-based examples live in an `attribute [local instance] Set.monad` section.
-/

namespace Isotope.Elgot.Transformer.Examples

open Isotope.Elgot

/-! ### Instance synthesis -/

/-- The reader transformer over partiality. -/
noncomputable example (R : Type) : LawfulElgotMonad (ReaderT R _root_.Part) := inferInstance

/-- The state transformer over partiality. -/
noncomputable example (S : Type) : LawfulElgotMonad (StateT S _root_.Part) := inferInstance

/-- The writer transformer over partiality.  `FreeMonoid` is used rather than `List`, since
Mathlib's competing `[EmptyCollection] [Append]` monad instance fires for `List`. -/
noncomputable example (E : Type) :
    LawfulElgotMonad (WriterT (FreeMonoid E) _root_.Part) := inferInstance

/-- Transformers compose: state over writer over partiality. -/
noncomputable example (S E : Type) :
    LawfulElgotMonad (StateT S (WriterT (FreeMonoid E) _root_.Part)) := inferInstance

section

attribute [local instance] Set.monad

/-- The state transformer over unbounded nondeterminism. -/
example (S : Type) : LawfulElgotMonad (StateT S Set) := inferInstance

/-- The reader transformer over unbounded nondeterminism. -/
example (R : Type) : LawfulElgotMonad (ReaderT R Set) := inferInstance

end

/-! ### State: a loop that counts the state down, and one that spins -/

/-- Decrement the state, returning once it reaches zero. -/
def decr : Unit → StateT ℕ _root_.Part (Unit ⊕ Unit) :=
  fun _ s ↦ match s with
    | 0 => _root_.Part.some (Sum.inl (), 0)
    | n + 1 => _root_.Part.some (Sum.inr (), n)

/-- The transported body at state `0`. -/
theorem body_decr_zero : State.body decr ((), 0) = _root_.Part.some (Sum.inl ((), 0)) := rfl

/-- The transported body at a successor state. -/
theorem body_decr_succ (n : ℕ) :
    State.body decr ((), n + 1) = _root_.Part.some (Sum.inr ((), n)) := rfl

/-- The countdown terminates from every starting state, with final state `0`. -/
theorem iter_decr : ∀ s : ℕ, iter decr () s = _root_.Part.some ((), 0)
  | 0 => by
      change iter (m := _root_.Part) (State.body decr) ((), 0) = _
      rw [congrFun (Isotope.Elgot.Part.fixpoint (State.body decr)) ((), 0), body_decr_zero,
        _root_.Part.bind_eq_bind, _root_.Part.bind_some]
      rfl
  | n + 1 => by
      change iter (m := _root_.Part) (State.body decr) ((), n + 1) = _
      rw [congrFun (Isotope.Elgot.Part.fixpoint (State.body decr)) ((), n + 1), body_decr_succ,
        _root_.Part.bind_eq_bind, _root_.Part.bind_some]
      exact iter_decr n

/-- Recurse forever, leaving the state alone. -/
def spin : Unit → StateT ℕ _root_.Part (Unit ⊕ Unit) :=
  fun _ s ↦ _root_.Part.some (Sum.inr (), s)

/-- A stateful loop that never returns is undefined, at every starting state: the state
transformer inherits `Part`'s divergence. -/
theorem iter_spin (s : ℕ) : iter spin () s = (_root_.Part.none : _root_.Part (Unit × ℕ)) := by
  change iter (m := _root_.Part) (fun p : Unit × ℕ ↦ _root_.Part.some (Sum.inr p)) ((), s) = _
  exact Isotope.Elgot.Part.iter_forever ((), s)

/-! ### Reader: termination depends on the environment -/

/-- Return immediately if the environment says so, otherwise recurse forever. -/
def envLoop : Unit → ReaderT Bool _root_.Part (Unit ⊕ Unit) :=
  fun _ b ↦ if b then _root_.Part.some (Sum.inl ()) else _root_.Part.some (Sum.inr ())

/-- In the `true` environment the loop returns immediately. -/
theorem iter_envLoop_true : iter envLoop () true = _root_.Part.some () := by
  change iter (m := _root_.Part) (fun _ : Unit ↦ _root_.Part.some (Sum.inl ())) () = _
  exact Isotope.Elgot.Part.iter_immediate () ()

/-- In the `false` environment the very same loop diverges: `ReaderT` iteration is genuinely
pointwise in the environment. -/
theorem iter_envLoop_false : iter envLoop () false = (_root_.Part.none : _root_.Part Unit) := by
  change iter (m := _root_.Part) (fun a : Unit ↦ _root_.Part.some (Sum.inr a)) () = _
  exact Isotope.Elgot.Part.iter_forever ()

/-! ### State over nondeterminism: every state is reachable -/

section

attribute [local instance] Set.monad

/-- Either stop, or increment the state and go round again. -/
def branch : Unit → StateT ℕ Set (Unit ⊕ Unit) :=
  fun _ s ↦ {(Sum.inl (), s), (Sum.inr (), s + 1)}

/-- The transported body may return in the current state. -/
theorem mem_body_branch_inl (k : ℕ) : Sum.inl ((), k) ∈ State.body branch ((), k) := by
  change Sum.inl ((), k) ∈ State.distr <$> branch () k
  rw [Set.fmap_eq_image]
  exact Set.mem_image_of_mem _ (Set.mem_insert _ _)

/-- The transported body may instead increment the state and recurse. -/
theorem mem_body_branch_inr (k : ℕ) : Sum.inr ((), k + 1) ∈ State.body branch ((), k) := by
  change Sum.inr ((), k + 1) ∈ State.distr <$> branch () k
  rw [Set.fmap_eq_image]
  exact Set.mem_image_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- From state `k`, the loop can return in state `k + d`, for every `d`. -/
theorem runs_branch : ∀ d k : ℕ, Nondet.Runs (State.body branch) ((), k) ((), k + d)
  | 0, k => .done (mem_body_branch_inl k)
  | d + 1, k => by
      refine .more (mem_body_branch_inr k) ?_
      have h := runs_branch d (k + 1)
      rwa [show k + 1 + d = k + (d + 1) by omega] at h

/-- The nondeterministic stateful loop reaches *every* final state: unbounded nondeterminism
survives the state transformer. -/
theorem iter_branch : iter branch () 0 = (Set.univ : Set (Unit × ℕ)) := by
  ext p
  obtain ⟨⟨⟩, n⟩ := p
  simp only [Set.mem_univ, iff_true]
  change Nondet.Runs (State.body branch) ((), 0) ((), n)
  have h := runs_branch n 0
  rwa [Nat.zero_add] at h

end

/-! ### Writer: emitting output and then diverging -/

/-- A terminating writer loop accumulates exactly the product of its per-step outputs. -/
theorem run_iter_countdown {E : Type} (e : E) (k : ℕ) :
    WriterT.run (iter (Writer.countdown (n := _root_.Part) (FreeMonoid.of e)) k)
      = _root_.Part.some ((), FreeMonoid.of e ^ k) :=
  Writer.countdown_run _ k

/-- A writer loop that emits output and then diverges denotes nothing at all: its infinite log is
discarded together with the divergent run. -/
theorem run_iter_tellLoop {E : Type} (e : E) (B : Type) :
    WriterT.run (iter (Writer.tellLoop (m := _root_.Part) (FreeMonoid.of e) B) PUnit.unit)
      = _root_.Part.none :=
  Writer.part_tellLoop_none _ (Writer.freeMonoid_no_left_fixed e) _ (fun f ↦ Writer.fixpoint f) B

/-- Two productive loops emitting different letters are nevertheless identified, while their
finite approximants are separated by `Writer.countdown_distinguishes`. -/
theorem tellLoop_collapse {E : Type} (e e' : E) (B : Type) :
    iter (Writer.tellLoop (m := _root_.Part) (FreeMonoid.of e) B)
      = iter (Writer.tellLoop (m := _root_.Part) (FreeMonoid.of e') B) :=
  Writer.tellLoop_indistinguishable e e' B

end Isotope.Elgot.Transformer.Examples
