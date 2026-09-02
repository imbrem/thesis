import Isotope.Elgot.Nondet.Powerset
import Isotope.Elgot.Nondet.Finite
import Isotope.Elgot.Nondet.Countable
import Isotope.Elgot.Nondet.Categorical

/-!
# Nondeterministic Elgot models

Three carriers, iterated by reachability:

* `Isotope.Elgot.Nondet.Powerset` — the powerset monad `Set` (and Mathlib's `SetM` wrapper).
  `Iterate Set`, `LawfulElgotMonad Set`, plus the corresponding `SetM` instances.
* `Isotope.Elgot.Nondet.Countable` — the countable powerset `CSet A = {s : Set A // s.Countable}`.
  `Monad`, `LawfulMonad`, `Iterate`, `LawfulElgotMonad`.
* `Isotope.Elgot.Nondet.Finite` — the finite powerset `FinSet A = {s : Set A // s.Finite}` and
  Mathlib's `Finset`.  Lawful monads, but **no** iteration operator on either satisfies the Elgot
  fixpoint law.
* `Isotope.Elgot.Nondet.Categorical` — the resulting Kleisli/Freyd structure.

## Honest boundary

**Proved.**

* `instIterateSet`, `instLawfulElgotMonadSet`: all four Elgot laws (fixpoint, naturality,
  codiagonal, pure uniformity) for `Set` with `iter f a = {b | Runs f a b}`, plus the `SetM`
  re-exports `instIterateSetM`, `instLawfulElgotMonadSetM`.
* `iter_eq_lfp`: `iter f` is the least fixpoint (`OrderHom.lfp`) of one loop unfolding on the
  complete lattice `A → Set B`; `iter_eq_reflTransGen`: the same set, via
  `Relation.ReflTransGen`.  Both are bridges to Mathlib's closure infrastructure; neither is used
  in the law proofs, which go by induction on `Runs`.
* Worked examples: `iter_immediate`, `iter_forever`, `iter_coin`, `iter_diverge_or_return`,
  `iter_countUp` (a two-way-branching body whose result set is all of `ℕ`).
* `FinSet.no_lax_fixpoint`, `FinSet.not_iterate_fixpoint`, `FinSet.not_lawfulElgotMonad`,
  `FinSet.not_nonempty_lawfulElgotMonad`, and the `Finset` analogues in
  `FinsetCounterexample`, all factored through the carrier-independent kernel
  `no_finite_lax_iteration`.  Positive companions `FinSet.instLawfulMonad` (and Mathlib's for
  `Finset`) are in place, so the failure is genuinely about iteration, not about the monad.
* `CSet.instLawfulMonad`, `runs_countable` (countable branching is closed under reachability),
  `CSet.instIterate`, `CSet.instLawfulElgotMonad`.
* `Categorical`: `Kleisli (TM SetM)` and `Kleisli (TM CSet)` are Elgot categories and strong
  Elgot Freyd categories, by instance synthesis from the generic construction in
  `Isotope.CategoryTheory.Monad.Elgot`.

**Not proved / deliberately out of scope.**

* *No `LambdaIter` denotational model.*  Issue #66 asks to "instantiate the LambdaIter
  Kleisli/Freyd semantics".  Only the categorical half is delivered.  A full
  `Semantics.TypeModel` + `LawfulTypeModel` + `InstructionModel` at a concrete signature does not
  exist anywhere in this repository yet, and building the first one is a separate piece of work
  about the *type universe*, orthogonal to nondeterminism.  There is no universe obstruction —
  `Set.{v} : Type v → Type v` matches `Denotation.lean`'s `m : Type v → Type v` exactly — so this
  is a scope decision, not an impossibility.
* *Divergence is identified with failure.*  The powerset model is angelic / partial-correctness:
  `iter (fun a ↦ {Sum.inr a}) a = ∅` and `iter (fun a ↦ {Sum.inl b, Sum.inr a}) a = {b}`, so
  "returns `b`, or diverges" is denoted exactly as "returns `b`".  All four laws hold; the model
  is simply not divergence-sensitive.  A divergence-sensitive nondeterministic model needs a
  different carrier (a convex/lower powerdomain, or interaction trees).
* *No `Iterate` instance is registered for `FinSet` or `Finset`.*  Doing so would be picked up by
  the many `[Iterate m]` binders downstream.  The impossibility results take the operator as an
  explicit argument instead.
* *`Multiset` is not treated.*  The same kernel lemma would apply, but bag semantics is not a
  powerset model and is not part of the issue.

**Axioms.**  Everything here uses only `propext`, `Classical.choice`, `Quot.sound`.  The `Set`
development needs no choice at all; `CSet` inherits countable choice through
`Set.countable_iUnion` / `Set.Countable.biUnion`, and the `Finset` counterexample uses
`Classical.propDecidable` for Mathlib's classical `Monad Finset`.  No new axiom is declared.
-/
