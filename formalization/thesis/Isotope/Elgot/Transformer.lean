import Isotope.Elgot.Transformer.Reader
import Isotope.Elgot.Transformer.State
import Isotope.Elgot.Transformer.Writer
import Isotope.Elgot.Transformer.Writer.Divergence
import Isotope.Elgot.Transformer.Writer.Infinite
import Isotope.Elgot.Transformer.Categorical
import Isotope.Elgot.Transformer.Examples

/-!
# Elgot-preserving monad transformers

Reader, state and writer transformers that lift a complete Elgot monad to a complete Elgot monad.

* `Isotope.Elgot.Transformer.Reader` — `ReaderT R m`, iterated pointwise in the environment.
* `Isotope.Elgot.Transformer.State` — `StateT S m`, iterated by threading the state through the
  recursive argument, along the distributor `(B ⊕ A) × S → (B × S) ⊕ (A × S)`.
* `Isotope.Elgot.Transformer.Writer` — `WriterT W m` for a monoid `W`, iterated by threading the
  accumulated output through the recursive argument, seeded at `1`.
* `Isotope.Elgot.Transformer.Writer.Divergence` — why output produced by a divergent run cannot be
  retained, by any operator, over any monoid.
* `Isotope.Elgot.Transformer.Writer.Infinite` — the interface a *productive* writer would need,
  and the theorem that its fixed-point equation has no solution inside `W`.
* `Isotope.Elgot.Transformer.Categorical` — the resulting Kleisli/Freyd structure.
* `Isotope.Elgot.Transformer.Examples` — worked models over `Part` and `Set`.

Universes: with `m : Type u → Type u` and `R S W : Type u`, all three transformers land at
`Type u → Type u`, which is what `Isotope.Elgot.Iterate` requires.  No `ULift` is needed.

## Honest boundary

**Proved, per transformer and per law.**  Throughout, `m` is an arbitrary
`[Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]`; nothing is specialised to `Part` or
`Set`.

* `Reader.instIterate`, `Reader.instLawfulElgotMonad`: all four laws (fixpoint, naturality,
  codiagonal, pure uniformity) for `ReaderT R m`, for every `R : Type u`, with no assumption on
  `R`.  Each law is a transport of the corresponding law of `m` along evaluation at a fixed
  environment.
* `State.instIterate`, `State.instLawfulElgotMonad`: all four laws for `StateT S m`, for every
  `S : Type u`, with no assumption on `S`.  Codiagonality is the only nontrivial one: `State.body`
  of an iteration is a *postcomposition* of an iteration with the distributor (`State.body_iter`),
  so `m`'s naturality must be applied before `m`'s codiagonal.
* `Writer.instIterate`, `Writer.instLawfulElgotMonad`: all four laws for `WriterT W m`, for every
  `[Monoid W]`, with **no further assumption on `W`** — no commutativity, cancellation, order,
  or completeness, and no choice.  `Monoid` is minimal in the only sense available: Mathlib's
  `LawfulMonad (WriterT W m)`, which `LawfulElgotMonad` presupposes, already consumes `one_mul`,
  `mul_one` and `mul_assoc`, so no per-law weakening to `Mul`/`MulOneClass` is exploitable.  The
  per-law audit of which monoid axioms and which laws of `m` are consumed is tabulated in
  `Writer.lean`'s module docstring.  The load-bearing lemma is `Writer.iter_shift`, an
  equivariance result obtained by composing `m`'s naturality (result side) with `m`'s uniformity
  (state side).
* `Writer.forget_iter`: erasing the output is a morphism of Elgot monads, so the writer
  transformer is conservative on values.
* `Writer.Divergence`: three independent obstruction theorems — carrier
  (`subsingleton_writerT_part`, `subsingleton_writerT_set`), naturality (`noReturn_shift` with
  `part_bot_of_succ_stable` / `set_bot_of_succ_stable`), and fixpoint (`tellLoop_shift`,
  `no_left_fixed`, `part_tellLoop_none`, `set_tellLoop_empty`).  Each takes the iteration operator
  and the single law it needs as an explicit argument, following
  `Isotope.Elgot.Nondet.no_finite_lax_iteration`, so none competes with the instances above.
  `countdown_run`, `countdown_distinguishes` and `tellLoop_indistinguishable` render the
  information loss as theorems: every finite approximant is separated by its log, and the limits
  are all undefined.
* `Writer.Infinite`: the classes `StreamProd` and `StreamMulAction`, a consistency witness
  (`instStreamMulActionPUnit`), the forced fixed-point equation `streamProd_const`, and
  `no_streamProd_self`.
* `Categorical`: the Kleisli categories of `ReaderT R Part`, `StateT S Part`,
  `WriterT (FreeMonoid E) Part`, `StateT S SetM` and `ReaderT R SetM` are (strong) Elgot Freyd
  categories, by instance synthesis from `Isotope.CategoryTheory.Monad.Elgot`.
* `Examples`: `iter_decr`, `iter_spin`, `iter_envLoop_true`, `iter_envLoop_false`, `iter_branch`,
  `run_iter_countdown`, `run_iter_tellLoop`, `tellLoop_collapse`.

**Not proved / deliberately out of scope.**

* *The productive infinite-output writer is not constructed*, and no `Iterate` or
  `LawfulElgotMonad` instance is claimed for any infinite-output writer.  By
  `Writer.Divergence` this is not a gap in the `WriterT` story but a statement that the
  construction does not live there: the right carrier is a trace monad `m ((A × W) ⊕ Winf)`,
  which duplicates the (absent) `Isotope.Elgot.Trace` development.  Codiagonality there
  additionally needs a block law relating `streamProd` of a stream of blocks to `streamProd` of
  the stream of block products, which does **not** follow from `StreamMulAction` — a
  tail-invariant `streamProd` satisfies `streamProd_cons` and refutes codiagonality.  That
  countermodel is not formalised here, because it is stated about trace-set iteration.  See
  `Writer/Infinite.lean` for the full reason.
* *The `Set` divergence obstruction uses a ℕ-grading, not merely `∀ u, w * u ≠ u`.*  The proof
  descends along a chain of members of strictly decreasing length, and the weaker hypothesis does
  not iterate: in the two-element group `{1, w}` it holds while `w ^ 2 * u = u`.  This is a
  limitation of the proof, not a claim that the theorem fails without the grading.  The `Part`
  version needs only the weaker hypothesis.
* *No `LambdaIter` denotational model.*  As in `Isotope.Elgot.Nondet`, only the categorical half
  is delivered.  No concrete `Semantics.TypeModel` + `LawfulTypeModel` + `InstructionModel` exists
  anywhere in this repository yet, so "add LambdaIter model instances" would mean building the
  first one, which is a separate piece of work about the type universe, orthogonal to
  transformers.  There is no universe obstruction: `Denotation.lean` binds
  `{m : Type v → Type v}`, and `StateT S m` with `S : Type v` matches exactly, so
  `Soundness.lean`'s `sound` and `sound_iter*` apply at the transformed monads by synthesis the
  moment the instances above are in scope.
* *No `MonadLift`-preserves-`iter` theorem.*  `Writer.forget_iter` is proved in the erasing
  direction only; the dual statement for `MonadLift m (WriterT W m)` is not.
* *Only reader, state and writer.*  `ExceptT` and `ContT` are not treated.

**Instance hazards, recorded because they bite.**

* Registering global `Iterate` instances for `ReaderT`, `StateT` and `WriterT` means every
  downstream `[Iterate m]` binder can now synthesise them.  `lake build Isotope` is green with
  them in place.
* Mathlib declares `Monad (WriterT ω M)` twice, from `[Monoid ω]` and from
  `[EmptyCollection ω] [Append ω]`.  For `ω = List E` only the second fires, so the
  `[Monoid W]`-keyed instances here do not apply; use `FreeMonoid E`.
* `Part`'s `Iterate` is noncomputable, so every instance statement about a `Part`-based
  transformer needs a `noncomputable` marker.  `Set` is not a global `Monad`, so `Set`-based
  material needs `attribute [local instance] Set.monad`, or the `SetM` wrapper.

**Axioms.**  Everything here uses only `propext`, `Classical.choice`, `Quot.sound`.  The abstract
transformer development needs no choice at all; choice enters only through `Part`'s and `Set`'s
own instances in the examples.  No new axiom is declared, and there is no `sorry`, `admit` or
`unsafe` in this directory.
-/
