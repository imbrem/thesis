import Isotope.Elgot.RA.State
import Isotope.Elgot.RA.Trace
import Isotope.Elgot.RA.Pull
import Isotope.Elgot.RA.GTrace
import Isotope.Elgot.RA.GData
import Isotope.Elgot.RA.Castling
import Isotope.Elgot.RA.Rewrite
import Isotope.Elgot.RA.Closure
import Isotope.Elgot.RA.Monad
import Isotope.Elgot.RA.Concrete
import Isotope.Elgot.RA.Iteration
import Isotope.Elgot.RA.Memory
import Isotope.Elgot.RA.Categorical
import Isotope.Elgot.RA.Generating
import Isotope.Elgot.RA.Assoc
import Isotope.Elgot.RA.Examples

/-!
# A release/acquire trace monad

A formalization of the loop-free monad of

> Yotam Dvir, Ohad Kammar and Ori Lahav, *A Denotational Approach to
> Release/Acquire Concurrency*, ESOP 2024, 121–149, doi 10.1007/978-3-031-57267-8_5
> (bib key `release-acquire`),

together with an iteration operator that the paper does not have.

## Sources used

The primary source is the TOPLAS journal version, *A Brookes-Style Denotational
Semantics for Release/Acquire Concurrency*, TOPLAS 47(2):7, doi 10.1145/3715096,
cross-checked against the ESOP 2024 *full version* (80pp,
`cs.tau.ac.il/~orilahav/papers/esop24full.pdf`).  Section, table, figure and
page numbers below cite the journal version, with the ESOP full version's
numbering in parentheses where it differs.

## What is transcribed from the paper

* `Isotope/Elgot/RA/State.lean`: views `View = ℚ^Loc`, messages
  `ν = ℓ:v@(q, κℓ]⟪κ⟫` with `q < κℓ`, the projections `.lc .vl .i .vw .t .seg`,
  the relations `κ ↣ ν`, `κ ↠ ν`, `κ ↣ μ`, `κ ↠ μ`, and *scattered*,
  *connected*, *causally connected*, the points-to digraph `μ.gph` and the
  cycle condition, hence `WellFormed` (the paper's `Mem`).  §6.1 (§5.1).
  Also the message orders `≤vw`, `⤙`, `⤙=`, the initial-timestamp update
  `ε[i↦q]` and *pulling* `κ[↑ε]`, with **Lemma 7.6** (`View.pull_le_pull`).
  §7.3, pp.31–33.
* `Isotope/Elgot/RA/Trace.lean`: transitions `⟨μ,ρ⟩`, chronicles with the
  adjacency condition `ρⱼ ⊆ μⱼ₊₁`, `ξ.o`, `ξ.c`, `ξ.own`, pre-traces
  `α ξ ω ◁ r` with non-empty chronicle, and the three trace conditions.  §7.2
  (§6.1).
* `Isotope/Elgot/RA/Rewrite.lean`: the rule sets `𝔠 = {St, Mu, Fw, Rw}`,
  `𝔤 = {Ls, Ex, Cn}` and `𝔤𝔠 = 𝔤 ∪ 𝔠`, and the seven rules themselves,
  Table 2 (Table 1), with the one-step relation `Step R` indexed by an
  arbitrary rule set, as in the paper's `─★→`.
* `Isotope/Elgot/RA/Closure.lean`: `★`-closedness with the paper's guard
  "`π` is again a trace", and `U★` as the least closed superset.  §7.2 (§6.3).
* `Isotope/Elgot/RA/Monad.lean`: `T X := P★(Trace X)`, `return`, `>>=`.  §7.2
  (§6.3).
* `Isotope/Elgot/RA/Concrete.lean`: the model tower `N`, `G`, `C` of Table 1,
  p.29 (§7.2–§7.4).
* `Isotope/Elgot/RA/Memory.lean`: `⟦store ℓ,v⟧` and `⟦rmw ℓ,Φ⟧` (read-only and
  read-modify-write).  §7.2 (§6.3).
* `Isotope/Elgot/RA/Castling.lean`: **Lemma 8.3, Rewrite Castling** (§8.1,
  p.39), for `x ∈ 𝔠` and `y ∈ 𝔤` — diagrams 1–18 of Table 5, p.62 — together
  with the rearrangement it is introduced for ("`𝔤`-rewrites appear first, then
  `𝔠`-rewrites").  The proofs are ours; the paper's run through Lemma F.1.
* `Isotope/Elgot/RA/Generating.lean`: **Proposition 7.5** (§7.3, p.30), that
  the operations absorb the `𝔤`-rules.  The paper's proof is a sketch.
* `Isotope/Elgot/RA/Assoc.lean`: **Proposition 7.7**, that the Concrete model
  is a monad (§7.4, p.34), following the paper's sketch in Example 8.6, p.41.
* `Isotope/Elgot/RA/Pull.lean`, `GTrace.lean`, `GData.lean`: the supporting
  apparatus for the three results above.  Ours, except for Lemma 7.6.

## What is reconstructed, not transcribed

* **The chronicle notation `η ⊎ {ε}`** used by all three `𝔤` rules is never
  defined in the paper.  `Isotope/Elgot/RA/Rewrite.lean` documents the reading
  we adopt — add `ε` to every memory of every transition of `η`, with `ε`
  absent from all of them — together with the three uses it is inferred from.
  Do not cite it as the paper's definition.
* **The trace-validity side conditions `Ls✓`, `Ex✓`, `Cn✓`** of the paper's
  Lemma F.1 (p.61) are *not* transcribed.  They characterize when the target of
  a rewrite is again a trace; the closure guard `IsTrace π` makes them
  unnecessary until Rewrite Castling, which is not formalized.
* **Relaxed dovetailing.**  We take the premises `ν ⤙ ε`, `ν ⤙= ε` of Table 2
  literally (`ν.vw ≤ ε.vw`), not the equal-view variant drawn in Figs. 13–14.
  The paper says twice (pp.32, 33) that the two presentations give the same
  semantics but proves neither claim; neither do we.

## Honest boundary

Read this before citing anything here as "the paper's".

1. **The rule group `𝔞 = {Ti, Ab, Di}` is not formalized**, so the paper's
   Abstract model `A` (`𝔤𝔠𝔞`) does not exist here.  What does exist is the
   whole tower below it: the Null model (`R = ∅`), the Generating model
   (`R = 𝔤`), the Concrete model `C` (`R = 𝔤𝔠`, the ESOP version's `M`), and
   the intermediate `𝔠`-model, all as instances of one `Comp R Loc Val`.
2. **The paper proves no monad laws.**  Propositions 7.7/7.8 (6.6/6.7) are
   stated without proof in both versions we consulted; the appendices treat
   Rewrite Castling, Deferral of Closure and adequacy instead.  Its one piece
   of supporting argument, Example 8.6 (p.41), covers associativity alone, and
   as a sketch.  Every proof in `Monad.lean`, `Concrete.lean`, `Assoc.lean`
   and `Generating.lean` is therefore original.  The same holds of
   Proposition 7.5 (p.30), whose proof in the paper is one sentence per rule
   for `Ls` and `Ex` and a prose paragraph, labelled "harder to demonstrate",
   for `Cn`.
3. **Associativity for the Concrete model `C` now holds** (Proposition 7.7),
   but not by the method used at `𝔠`.  Deferring a rewrite of one operand past
   the bind seam is *provably unavailable* for `𝔤`: `Loosen`, `Expel` and
   `Condense` replace messages in the closing memory of the left operand, so
   neither `ChroStep.c_sub` nor `ChroStep.o_sub` holds and the seam condition
   `τ.ch.c ⊆ υ.ch.o` is not transported backwards along a rewrite.  The route
   taken is the paper's own: Proposition 7.5 (`Generating.lean`) makes the
   operations absorb the `𝔤`-closure, Rewrite Castling (`Castling.lean`) turns
   the `𝔤𝔠`-closure of a `𝔤`-closed set into its `𝔠`-closure, and associativity
   at `𝔠` finishes (`Assoc.lean`).  `C` therefore has `LawfulMonad`,
   `LawfulElgotMonad` and the Kleisli Elgot/Freyd structure, as well as the
   carrier, `⊥`, arbitrary unions, `bind_mono`, the iteration operator and the
   memory-access constants.
4. **`ξ.own` is a rewriting invariant only at `𝔠`.**  `Refines.own_eq` now
   carries the hypothesis `R ⊆ 𝔠`; the `𝔤` rules change which environment
   messages occur, and `Condense` maps every message through the pull.  What
   survives at `𝔤𝔠` is `Refines.own_empty`: *having no* local messages is
   preserved.  That weaker invariant is what both unit laws run on.
5. **Countability is dropped.**  The journal version restricts `T X` to
   *countable* `★`-closed sets; the ESOP full version's own display does not.
   We take all `★`-closed sets.  Nothing in this development needs the
   restriction.
6. **`Memory` is a bare set of messages.**  The paper says a memory is a finite
   non-empty set of messages and reserves `Mem` for the well-formed ones; we
   fold finiteness and non-emptiness into `WellFormed`, which is where the
   paper's trace conditions use `Mem`.  Likewise the transition condition
   `μ ⊆ ρ` is a field of `Transition.WF` rather than of `Transition`.  Both are
   presentational: the traces are the same.
7. **Iteration is entirely ours.**  §4 of the paper is explicit that λRA has no
   recursion or loops, deliberately, to avoid ω-cpos and powerdomains.  The
   `Iterate` instance in `Isotope/Elgot/RA/Iteration.lean` is the
   union-of-finite-unrollings operator (`f₀ = ⊥`, `fᵢ₊₁ = f ; [id, fᵢ]`,
   `f† = ⋃ᵢ fᵢ`) of the thesis's own appendix on the Brookes monad `B_c`.  It is
   **partially correct only**: a computation that always diverges denotes `∅`,
   and divergent observations are discarded.  It is not the paper's semantics
   for anything, because the paper has no loops.
8. **No parallel composition.**  `∥∥∥`, the interleaving of chronicles, and
   `sup_μ`/`inf_μ` are not formalized; nothing here is a model of the
   *concurrent* fragment of λRA.  What is formalized is the sequential monad
   and the memory-access constants.
9. **Rewrite Castling is formalized only in the half that does not mention
   `𝔞`.**  Lemma 8.3 (p.39) covers `x ∈ 𝔞, y ∈ 𝔤𝔠` and `x ∈ 𝔠𝔞, y ∈ 𝔤`; what is
   proved here is `x ∈ 𝔠, y ∈ 𝔤`, i.e. diagrams 1–18 of Table 5 (p.62).  The
   remaining 48 diagrams all involve `𝔞`, which is not formalized.
   **Deferral of Closure (Lemma 8.5) is formalized only at `★ = 𝔠`**
   (`bindGen_closure_left`/`right`), which is what the associativity proof
   needs; the paper states it for `𝔠 ⊆ ★ ⊆ 𝔠𝔞`.  **Retroactive Closure
   (Lemma 8.7) is not formalized**, and hence neither is **adequacy, full
   abstraction, or any correspondence with the operational semantics**:
   Theorems 8.11–8.15 and Table 3's program transformations are out of scope.
10. **`Condense` is read with a possibly empty rewritten suffix.**  In
   `α ξ (η ⊎ {ν,ε}) ω ─Cn→ (α ξ (η ⊎ {ν}) ω)[↑ε]` we allow `η` to be empty, so
   that the rule may pull the whole pre-trace along a message that occurs
   nowhere in it.  The evidence is Fig. 15's caption (p.33): "since `ε` is to
   appear as an environment message in the chronicle, it can appear since the
   opening memory, **not appear even in the closing memory**, or somewhere in
   between".  This is not a harmless liberality — it is load-bearing.  In the
   `St ⇄ Cn` case of Rewrite Castling the stutter'ee can be the *only*
   transition carrying `ε`, and then the castled `Cn`-rewrite has nothing left
   to condense and must be exactly such a pure pull; with the stricter reading
   that case of Lemma 8.3 is false.  The trace guard keeps the liberality
   sound: a pull along a message whose segment is not free destroys
   scatteredness, so the target is not a trace.
11. **Lemma F.1 is not transcribed.**  What `Isotope/Elgot/RA/GTrace.lean`
   proves is its reusable half: each `𝔤` rule takes traces to traces *given
   that the target's memories are well-formed*.  The paper instead
   characterizes when the target is a trace, deriving well-formedness; every
   use here has it already.

## What is proved

* `LawfulMonad (Comp cRules Loc Val)` — the three monad laws for the
  `𝔠`-model (`Comp.left_neutrality`, `Comp.right_neutrality`,
  `Comp.associativity`).
* `LawfulMonad (Comp gcRules Loc Val)` — **the paper's Proposition 7.7: the
  Concrete model `C` is a monad**, which the paper states without proof.  Its
  three laws are `Concrete.pure_bind`, `Concrete.bind_pure` and
  `Concrete.associativity`; and hence also `LawfulElgotMonad` and, by
  `Isotope/CategoryTheory/Monad/Elgot.lean`, the Kleisli Elgot and Elgot-Freyd
  structure of `C` (`nonempty_elgotCategory_concrete`,
  `nonempty_elgotFreydCategory_concrete`).
* `castling` — **Rewrite Castling** (Lemma 8.3) for `x ∈ 𝔠`, `y ∈ 𝔤`, with
  `Refines.sort_gc` and `closure_gcRules_eq`.
* `pureGen_closed` and `bindGen_closed` — **Proposition 7.5**.
* `Concrete.pure_bind` and `Concrete.bind_pure` — both unit laws for `C`.  Proved uniformly for every `𝔠 ⊆ R ⊆ 𝔤𝔠` from a single
  invariant: a trace in the closure of `return r` has no local messages, so
  every one of its transitions is a stutter and its memories form a
  `⊆`-chain.
* `not_bind_pure` — the Null and Generating models are **not** monads, right
  neutrality failing because no `𝔤` rule changes the number of transitions
  (`Refines.length_eq`).  The paper asserts this in one sentence (p.30).
* `closure_mono_rules` — the paper's `G X ⊇ C X ⊇ A X` (§8.2, p.41), asserted
  there without argument.
* `View.pull_le_pull` — the paper's Lemma 7.6 (p.33).
* `LawfulElgotMonad (Comp cRules Loc Val)` — fixpoint, naturality, codiagonal
  and pure uniformity for the union-of-unrollings iteration operator.  The
  operator itself and its `fixpoint` law exist at every rule set.
* Consequently, by `Isotope/CategoryTheory/Monad/Elgot.lean`, the Kleisli
  category of `Comp cRules Loc Val` is an `ElgotCategory` and an
  `ElgotFreydCategory` (`nonempty_elgotCategory`, `nonempty_elgotFreydCategory`).
* Rewriting invariants that separate computations: the returned value
  (`Refines.ret_eq`, at every rule set), the local messages
  (`Refines.own_eq`, at `𝔠`), having no local messages
  (`Refines.own_empty`, at `𝔤𝔠`), and the number of transitions
  (`Refines.length_eq`, at `𝔤`).
* Worked examples in `Isotope/Elgot/RA/Examples.lean`: `pure_ne_pure`,
  `bot_ne_pure`, `storedMem_wellFormed` (a well-formed memory with two messages
  at one location), `mem_store`, `store_ne_pure`, `store_ne_bot`, `load_stale`
  (a load returning a value that a strictly later write at the same location
  has already superseded), and the loop examples `iter_diverge`, `iter_exit`,
  `iter_store_diverge`.
-/
