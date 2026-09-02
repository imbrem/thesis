import Isotope.Elgot.RA.State
import Isotope.Elgot.RA.Trace
import Isotope.Elgot.RA.Rewrite
import Isotope.Elgot.RA.Closure
import Isotope.Elgot.RA.Monad

/-!
# A release/acquire trace monad

A formalization of the loop-free monad of

> Yotam Dvir, Ohad Kammar and Ori Lahav, *A Denotational Approach to
> Release/Acquire Concurrency*, ESOP 2024, 121–149, doi 10.1007/978-3-031-57267-8_5
> (bib key `release-acquire`),

together with an iteration operator that the paper does not have.

## Sources used

The brief this development was written from quotes the ESOP 2024 *full version*
(80pp, `cs.tau.ac.il/~orilahav/papers/esop24full.pdf`) and the TOPLAS journal
version *A Brookes-Style Denotational Semantics for Release/Acquire Concurrency*
(TOPLAS 47(2):7, doi 10.1145/3715096).  Section numbers below cite the journal
version, with the ESOP full version's numbering in parentheses where it differs.

## What is transcribed from the paper

* `Isotope/Elgot/RA/State.lean`: views `View = ℚ^Loc`, messages
  `ν = ℓ:v@[q, κℓ)⟪κ⟫` with `q < κℓ`, the projections `.lc .vl .i .vw .t .seg`,
  the relations `κ ↣ ν`, `κ ↠ ν`, `κ ↣ μ`, `κ ↠ μ`, and *scattered*,
  *connected*, *causally connected*, the points-to digraph `μ.gph` and the
  cycle condition, hence `WellFormed` (the paper's `Mem`).  §6.1 (§5.1).
* `Isotope/Elgot/RA/Trace.lean`: transitions `⟨μ,ρ⟩`, chronicles with the
  adjacency condition `ρⱼ ⊆ μⱼ₊₁`, `ξ.o`, `ξ.c`, `ξ.own`, pre-traces
  `α ξ ω ◁ r` with non-empty chronicle, and the three trace conditions.  §7.2
  (§6.1).
* `Isotope/Elgot/RA/Rewrite.lean`: the four `𝔠` rules `Stutter`, `Mumble`,
  `Forward`, `Rewind`, Table 2 (Table 1).
* `Isotope/Elgot/RA/Closure.lean`: `★`-closedness with the paper's guard
  "`π` is again a trace", and `U★` as the least closed superset.  §7.1 (§6.3).
* `Isotope/Elgot/RA/Monad.lean`: `T X := P★(Trace X)`, `return`, `>>=`.  §7.2
  (§6.3).
* `Isotope/Elgot/RA/Memory.lean`: `⟦store ℓ,v⟧` and `⟦rmw ℓ,Φ⟧` (read-only and
  read-modify-write).  §7.2 (§6.3).

## Honest boundary

Read this before citing anything here as "the paper's".

1. **We formalize the `𝔠`-model, not the paper's `𝔤𝔠` (Concrete) or `𝔤𝔠𝔞`
   (Abstract) models.**  The rule groups `𝔤 = {Loosen, Expel, Condense}` and
   `𝔞 = {Tighten, Absorb, Dilute}` are *not* formalized.  The paper's
   Propositions 7.7/7.8 (6.6/6.7) assert that the `𝔤𝔠`- and `𝔤𝔠𝔞`-models are
   monads; it makes no claim about `𝔠` alone.  So `LawfulMonad (Comp Loc Val)`
   here is **our theorem about our model**, not a port of a theorem of theirs.
2. **The paper proves no monad laws.**  Propositions 7.7/7.8 (6.6/6.7) are
   stated without proof in both versions we consulted, and the appendices treat
   Rewrite Castling, Deferral of Closure and adequacy instead.  Every proof in
   `Monad.lean` is original.
3. **Countability is dropped.**  The journal version restricts `T X` to
   *countable* `★`-closed sets; the ESOP full version's own display does not.
   We take all `★`-closed sets.  Nothing in this development needs the
   restriction.
4. **`Memory` is a bare set of messages.**  The paper says a memory is a finite
   non-empty set of messages and reserves `Mem` for the well-formed ones; we
   fold finiteness and non-emptiness into `WellFormed`, which is where the
   paper's trace conditions use `Mem`.  Likewise the transition condition
   `μ ⊆ ρ` is a field of `Transition.WF` rather than of `Transition`.  Both are
   presentational: the traces are the same.
5. **Iteration is entirely ours.**  §4 of the paper is explicit that λRA has no
   recursion or loops, deliberately, to avoid ω-cpos and powerdomains.  The
   `Iterate` instance in `Isotope/Elgot/RA/Iteration.lean` is the
   union-of-finite-unrollings operator (`f₀ = ⊥`, `fᵢ₊₁ = f ; [id, fᵢ]`,
   `f† = ⋃ᵢ fᵢ`) of the thesis's own appendix on the Brookes monad `B_c`.  It is
   **partially correct only**: a computation that always diverges denotes `∅`,
   and divergent observations are discarded.  It is not the paper's semantics
   for anything, because the paper has no loops.
6. **No parallel composition.**  `∥∥∥`, the interleaving of chronicles, and
   `sup_μ`/`inf_μ` are not formalized; nothing here is a model of the
   *concurrent* fragment of λRA.  What is formalized is the sequential monad
   and the memory-access constants.
7. **No adequacy, no full abstraction, no correspondence with the operational
   semantics.**  Theorems 8.12–8.14 of the paper are out of scope.

## What is proved

* `LawfulMonad (Comp Loc Val)` — the three monad laws for the `𝔠`-model
  (`Comp.pure_bind`, `Comp.bind_pure`, `Comp.bind_assoc`).
* `LawfulElgotMonad (Comp Loc Val)` — fixpoint, naturality, codiagonal and pure
  uniformity for the union-of-unrollings iteration operator.
* Consequently, by `Isotope/CategoryTheory/Monad/Elgot.lean`, the Kleisli
  category of `Comp Loc Val` is an `ElgotCategory` and an `ElgotFreydCategory`;
  see `Isotope/Elgot/RA/Categorical.lean`.
-/
