import Isotope.Elgot.TraceSet.Basic
import Isotope.Elgot.TraceSet.Iteration
import Isotope.Elgot.TraceSet.Laws
import Isotope.Elgot.TraceSet.Nondeterminism
import Isotope.Elgot.TraceSet.Compare
import Isotope.Elgot.TraceSet.Examples

/-!
# Nondeterministic trace sets as an Elgot monad

`TraceSet E T A` is a set of `Trace E T A`, where a trace is either termination
with a value and an accumulated effect from `E`, or divergence carrying an
infinite observation from `T`.  This is the nondeterministic counterpart of the
deterministic `FiniteTrace` model in the module `Isotope.Elgot.Trace`.

Note the naming: the *inductive* `Isotope.Elgot.Trace` introduced here (a single
observation) is a different thing from the *module* `Isotope.Elgot.Trace`, which
defines `FiniteTrace`.

## Honest boundary

**Proved here.**

* `Monad`/`LawfulMonad (TraceSet E T)` under `[Monoid E] [MulAction E T]`, together
  with `MulAction E (TraceSet E T A)` and the membership calculus.
* `Iterate (TraceSet E T)` under the weaker `[Mul E] [SMul E T]`, defined by an
  inductive `Runs` relation collecting the traces of every **finite** unfolding.
* All four `LawfulElgotMonad` equations — `fixpoint`, `naturality`, `codiagonal`
  and uniformity along **pure** maps — under `[Monoid E] [MulAction E T]`.
* Nondeterminism: union/`bind`/`iter` compatibility and monotonicity
  (`Isotope.Elgot.TraceSet.Nondeterminism`).
* The comparison with `FiniteTrace`: the deterministic model embeds as an
  injective monad morphism that also commutes with iteration
  (`Isotope.Elgot.TraceSet.Compare`).
* Consequently the Kleisli category of `TraceSet E T` inherits the
  `ElgotCategory` / `ElgotFreydCategory` structure of
  `Isotope.CategoryTheory.Monad.Elgot` and the `LambdaIter` soundness theorems,
  with no further work.

**Not proved, and not claimed.**

* This is *milestones 1 and 2* of issue #28 only.  Iteration keeps every finite
  trace, including divergence produced *by a single step* (`Trace.inf`), but a
  productive infinite loop — infinitely many unfoldings, each terminating —
  contributes **no** trace at all: `iter (fun a ↦ {done (inr a) e}) a = ∅`.
* Consequently there is **no** stream action here: no `StreamProd`, no
  `streamProd`, no infinite-trace component `infiniteTraces`, and no
  `iterateTraces = finiteTraces ∪ infiniteTraces`.  Milestone 3 of issue #28 —
  the ω-generated divergences, and the projection from that model back to this
  one — is future work.  The blocking obstruction recorded during recon is that
  the codiagonal law for the ω-model does *not* follow from the usual stream
  action axioms and needs an extra block/flattening axiom on `streamProd`.
* Divergence with a discarded trace is the **empty** trace set here, i.e. the
  least element for nondeterministic refinement (`∅ ∪ x = x`).  It is
  deliberately *not* an absorbing "undefined behaviour" element; nothing in this
  development conflates the two.  See
  `Isotope.Elgot.TraceSet.discarded_divergence_not_absorbing`.
-/
