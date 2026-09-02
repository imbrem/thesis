import Isotope.Elgot.RA.State
import Isotope.Elgot.RA.Trace
import Isotope.Elgot.RA.Pull
import Isotope.Elgot.RA.GTrace
import Isotope.Elgot.RA.GData
import Isotope.Elgot.RA.Castling
import Isotope.Elgot.RA.Rewrite
import Isotope.Elgot.RA.Closure
import Isotope.Elgot.RA.Monad
import Isotope.Elgot.RA.Bounds
import Isotope.Elgot.RA.Parallel
import Isotope.Elgot.RA.Exchange
import Isotope.Elgot.RA.Concrete
import Isotope.Elgot.RA.Iteration
import Isotope.Elgot.RA.Memory
import Isotope.Elgot.RA.Categorical
import Isotope.Elgot.RA.Generating
import Isotope.Elgot.RA.Assoc
import Isotope.Elgot.RA.Examples
import Isotope.Elgot.RA.ParExamples
import Isotope.Elgot.RA.Abstract
import Isotope.Elgot.RA.Opt

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
  `𝔤 = {Ls, Ex, Cn}`, `𝔞 = {Ti, Ab, Di}`, `𝔤𝔠` and `𝔤𝔠𝔞`, and all nine
  rules themselves, Table 2 (Table 1), with the one-step relation `Step R`
  indexed by an arbitrary rule set, as in the paper's `─★→`.  The three `𝔞`
  rows were read off the typeset table and off the displays `(Tighten)`,
  `(Absorb)` (p.36) and `(Dilute)` (p.37) by rendering those pages.
* `Isotope/Elgot/RA/Closure.lean`: `★`-closedness with the paper's guard
  "`π` is again a trace", and `U★` as the least closed superset.  §7.2 (§6.3).
* `Isotope/Elgot/RA/Monad.lean`: `T X := P★(Trace X)`, `return`, `>>=`.  §7.2
  (§6.3).
* `Isotope/Elgot/RA/Concrete.lean`: the model tower `N`, `G`, `C` of Table 1,
  p.29 (§7.2–§7.4).
* `Isotope/Elgot/RA/Abstract.lean`: the Abstract model `A = Comp gcaRules`
  (§7.5, p.35), and the comparison between the models.
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
* `Isotope/Elgot/RA/Bounds.lean`: the delimiting views of a parallel
  composition, `sup_μ U = ⊔U` (which is literally the pointwise join, since
  `↠μ` is closed under `⊔`) and `inf_μ U = ⊔{κ | ⊓U ⊒ κ ↠ μ}`.  §7.2, p.29.
* `Isotope/Elgot/RA/Parallel.lean`: parallel composition
  `(|||ᵀ) : T X × T Y → T (X × Y)`, §7.1 p.27 (the operation) and §7.2 p.29
  (the definition), with Proposition 7.4 for `|||`.
* `Isotope/Elgot/RA/Exchange.lean`: Proposition E.1, *Generalized Sequencing*
  (p.58; ESOP Proposition C.1), and the thread-inlining transformation
  `M ∥ N ↠ ⟨M,N⟩` of Fig. 3 (p.12) and Table 3 (p.44).

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
* **The chronicle shuffle `ξ₁ ∥ ξ₂`** is never defined in the paper beyond the
  phrase "the set of all the interleavings of `ξ₁` and `ξ₂` that form
  chronicles" (p.29).  `Isotope/Elgot/RA/Parallel.lean` reads it as a
  position-wise shuffle of the two transition lists — transitions carried across
  verbatim, neither merged nor rewritten — that is again a chronicle, and
  records the three places in the paper the reading is forced by (Prop E.5's
  worked computation, the Appendix A decomposition, and the `R`-model).  It is a
  reading, not a quotation.
* **`inf_μ U` is characterised, not constructed.**  `IsInfMem μ U κ` says that
  `κ` is the greatest view pointing downwards into `μ` and below every element
  of `U` — equivalently, that the `⊔` of the paper's formula is attained.  The
  paper's existence argument (`↠μ` is finite and has a minimum `λℓ. min μ_ℓ.t`)
  is **not** formalized, so `IsInfMem` is a hypothesis of `parGen`, never a
  conclusion.  Two consequences are recorded in the honest boundary below.
* **`inf_μ` outside its stated domain.**  §7.2 defines `inf_μ U` only for
  `U ⊆ ↠μ`, but the definition of `|||` applies it at `U = {α₁,α₂}`, `μ = ξ.o`,
  where `α₂ ↠ ξ.o` can fail: `ξ.o` is contained in each `ξᵢ.o`
  (`ChroInterleave.o_sub_left`), and pointing downwards is monotone only
  *upwards* in the memory.  The paper's own Appendix A proof (p.49) uses the
  general reading, so `IsInfMem` imposes no relation between `U` and `μ`.  This
  is a documented repair, not the paper's text.

## Honest boundary

Read this before citing anything here as "the paper's".

1. **`A` exists, but Proposition 7.8 is not proved.**  All nine rules and the
   whole tower are formalized as instances of one `Comp R Loc Val`: the Null
   model (`R = ∅`), the Generating model (`R = 𝔤`), the Concrete model `C`
   (`R = 𝔤𝔠`, the ESOP version's `M`), the Abstract model `A` (`R = 𝔤𝔠𝔞`),
   and the intermediate `𝔠`-model.  What is *not* proved is that `A` is a monad.
   Both unit laws hold for every `𝔠 ⊆ R ⊆ 𝔤𝔠 ∪ {Ti, Ab}`, and **not** for
   `R = 𝔤𝔠𝔞`: `Dilute` creates a local message where there was none, so the
   invariant the unit-law proof runs on fails.  This is not an artefact of the
   transcription — `dilute_return` of `Isotope/Elgot/RA/Abstract.lean` exhibits
   a `Di`-rewrite of a `return`-trace built on the paper's own initial memory.
   The paper's own route to Proposition 7.8 must therefore be Deferral of
   Closure (Lemma 8.5, p.41), which is not formalized.  Associativity is open
   for `A` as it is for `C`.
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
   of supporting argument, Example 8.6 (p.41), covers associativity alone.
   Every proof in `Monad.lean` and `Concrete.lean` is therefore original.
3. **Associativity for the Concrete model `C` is open.**  It is proved here
   only for `R ⊆ 𝔠`.  The proof method — deferring a rewrite of one operand
   past the bind seam — is *provably unavailable* for `𝔤`: `Loosen`, `Expel`
   and `Condense` replace messages in the closing memory of the left operand,
   so neither `ChroStep.c_sub` nor `ChroStep.o_sub` holds and the seam
   condition `τ.ch.c ⊆ υ.ch.o` is not transported backwards along a rewrite.
   The paper's own route runs through Proposition 7.5 (the `N`-operations are
   `𝔤`-closed) and Lemma 8.3 (Rewrite Castling, 66 diagrams in Appendix F);
   neither is formalized.  Consequently there is **no** `LawfulMonad`,
   `LawfulElgotMonad`, or Kleisli Elgot/Freyd instance for `C`; those exist
   only at `R = 𝔠`.  What `C` does have: both unit laws, the carrier, `⊥`,
   arbitrary unions, `bind_mono`, the iteration *operator* and its `fixpoint`,
   and the memory-access constants.
4. **`ξ.own` is a rewriting invariant only at `𝔠`.**  `Refines.own_eq`
   carries the hypothesis `R ⊆ 𝔠`; the `𝔤` rules change which environment
   messages occur, and `Condense` maps every message through the pull.  What
   survives at `𝔤𝔠 ∪ {Ti, Ab}` is `Refines.own_empty`: *having no* local
   messages is preserved — vacuously for `Ti` and `Ab`, whose sources have a
   local message by construction.  That weaker invariant is what both unit laws
   run on, and `Di` breaks it (item 1).
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
8. **Parallel composition is formalized, but not its full equational theory.**
   `Comp.par` (the paper's `|||`, §7.1 p.27, §7.2 p.29), chronicle
   interleaving, `sup_μ` and `inf_μ` are in `RA/{Bounds,Parallel,Exchange}.lean`,
   with Proposition 7.4, Symmetry as an equality of trace sets, thread inlining
   `M ∥ N ↠ ⟨M,N⟩`, and Proposition E.1 (Generalized Sequencing).  What is
   **not** proved: associativity of `|||`, the converse half of its unit law,
   the remaining symmetric-monoidal laws claimed in the Fig. 3 caption (p.12),
   and Deferral of Closure for `|||` (Lemma 8.5, p.41) — the last is not
   reachable with the present design, because `inf_μ` is *characterised*
   (`IsInfMem`) rather than constructed, so its four `𝔠` cases cannot produce
   the required witness.  Existence of `inf_μ` is likewise not formalized, so
   `parGen` carries `IsInfMem` as a hypothesis and `Comp.par` is not proved
   non-empty in general (`par_pure_pure_nonempty` covers the concrete case).
   The interaction of `|||` with iteration is untouched, and no litmus test
   (SB, MP, SB+F) is proved in either direction.
9. **Rewrite Castling is formalized only in the half that does not mention
   `𝔞`.**  Lemma 8.3 (p.39) covers `x ∈ 𝔞, y ∈ 𝔤𝔠` and `x ∈ 𝔠𝔞, y ∈ 𝔤`; what is
   proved here is `x ∈ 𝔠, y ∈ 𝔤`, i.e. diagrams 1–18 of Table 5 (p.62).  The
   remaining 48 diagrams all involve `𝔞`; the `𝔞` rules are formalized, but
   `castling` is stated at `Castles cRules gRules`, so every case that mentions
   `Ti`, `Ab` or `Di` is discharged from that hypothesis rather than proved.
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
8. **Parallel composition is formalized, with two gaps.**  `∥∥∥`, the
   chronicle shuffle, `sup_μ` and `inf_μ` are in
   `Isotope/Elgot/RA/{Bounds,Parallel,Exchange}.lean`, uniformly in the rule
   set.  Two things are missing.

   (a) **`inf_μ` existence.**  `IsInfMem` is a characterisation, so `parGen`
   quantifies over a witness.  The paper's existence proof needs `↠μ` finite
   (hence `Finite Loc`) and its minimum, via Proposition 6.7(2); none of that is
   formalized.  So `Comp.par` is not proved non-empty *in general* — though it
   is proved to contain the whole sequential pairing (`Comp.seqPair_le_par`),
   which is a witness whenever the two initial views agree.

   (b) **Deferral of Closure for `|||`** (Lemma 8.5, journal p.41, proof
   pp.48–49) is **not** proved, and cannot be with the present design: all four
   of its `𝔠` cases replace one operand's initial view or one shuffle's opening
   memory and then need `inf` at the *new* data, i.e. exactly the existence
   theorem of (a).  This is the one place where characterising `inf_μ` instead
   of constructing it actually costs a result.

   Also **not** proved and **not** attempted: associativity of `|||`, the
   converse half of the unit law (only `P ⊆ P ||| return r` is proved; see
   `Isotope/Elgot/RA/Exchange.lean` for why the converse is hard), the
   remaining symmetric-monoidal laws, Proposition 7.5, and every litmus test
   (SB, MP, SB+F) — the paper states these only operationally and never carries
   out the denotational calculation itself (p.42: "can be shown").  Half of
   Proposition E.5 (Write-Read Deorder) is out of reach for a further reason:
   its (WR) interleaving needs the `𝔞` rule `Ti`.
9. **No Proposition 7.5, no Deferral of Closure at `𝔤`, no Rewrite Castling,
   no Retroactive Closure**, and hence **no adequacy, no full abstraction, and
   no correspondence with the operational semantics**.  Theorems 8.11–8.15 and
   Table 3's program transformations are out of scope.

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
* `pureGen_closed` and `bindGen_closed` — **Proposition 7.5**, in the two
  clauses the monad laws need.  Its clauses for `⟦store⟧`, `⟦rmw⟧` and `|||`
  are **not** proved.
* `Concrete.pure_bind` and `Concrete.bind_pure` — both unit laws for `C`.  Proved uniformly for every `𝔠 ⊆ R ⊆ 𝔤𝔠` from a single
  invariant: a trace in the closure of `return r` has no local messages, so
  every one of its transitions is a stutter and its memories form a
  `⊆`-chain.
* `not_bind_pure` — the Null and Generating models are **not** monads, right
  neutrality failing because no `𝔤` rule changes the number of transitions
  (`Refines.length_eq`).  The paper asserts this in one sentence (p.30).
* `closure_mono_rules` — the paper's `G X ⊆ C X ⊆ A X` (§8.2, p.41), asserted
  there without argument.  As printed the sentence is loose: these are sets of
  `★`-closed sets, and a `𝔤`-closed set need not be `𝔤𝔠`-closed.  What holds is
  that the *closure operators* are ordered (`closure_le_closure`, hence
  pointwise `⟦M⟧_G ⊆ ⟦M⟧_C ⊆ ⟦M⟧_A`) while the *carriers* are ordered the other
  way (`Closed.mono_rules`); `Comp.extend_le_iff` makes the pair an adjunction.
* `pure_bind_gcTiAb`, `bind_pure_gcTiAb` — both unit laws for `𝔤𝔠 ∪ {Ti, Ab}`,
  the largest fragment of the Abstract model's rule set for which we can prove
  them.  **Original work.**
* `dilute_return`, `not_refines_dilute_return`,
  `pure_concrete_ssubset_pure_abstract` — a concrete `Dilute` rewrite of a
  `return`-trace, the fact that no `𝔤𝔠 ∪ {Ti, Ab}`-rewriting realises it, and
  hence `return_C r ⊊ return_A r`.  The paper asserts that the Concrete model is
  "insufficiently abstract" (p.26) but exhibits no separating trace anywhere;
  this is **original work**.
* `absorb_two_writes` — a concrete `Absorb` rewrite merging the two dovetailing
  local writes of the paper's `ℓ ≔ w ; ℓ ≔ v ↠ ℓ ≔ v` example (p.37) into one —
  and `tighten_write`, a concrete `Tighten` rewrite advancing the view of a
  local write to point at a later message at a second location, the shape of
  the paper's write–read reordering step (§E.5, p.59); each with its
  `not_refines_cRules_…` companion.  Together with `dilute_return` these keep
  all three `𝔞` constructors honest: their side conditions are jointly
  satisfiable on genuine traces, which the vacuous `own_empty` cases for `Ti`
  and `Ab` do not show.  **Original work**: the paper constructs no trace.
* `union_initialMem_wellFormed` — the initial memory extended by extra writes is
  well formed under five explicit conditions, the last two of which are what
  keeps the paper's *cycle* condition true.  Generalizes `storedMem_wellFormed`.
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
* **Parallel composition** (`Isotope/Elgot/RA/Parallel.lean`,
  `Isotope/Elgot/RA/Exchange.lean`), uniformly in the rule set:
  - `parGen_isTrace` — the paper's `∈ Trace (X₁ × X₂)` guard in the definition
    of `|||` is redundant, exactly as `IsTrace.append` makes it redundant for
    `>>=`.  Original.
  - `Comp.par_mono` — the `|||` half of Proposition 7.4 (p.29).
  - `ChroInterleave.own_union` and `ChroInterleave.own_disjoint` — parallel
    composition splits the local messages, and the union is **disjoint**.
    Original: the paper has no separation statement, no frame rule and no
    footprints; disjointness is forced by chronicle adjacency alone rather than
    imposed as a side condition.
  - `Comp.par_swap` — **Symmetry** (Table 3, p.44), as an equality of trace
    sets.  Original: the paper claims Symmetry and "all symmetric-monoidal laws"
    (Fig. 3 caption, p.12) with no proposition, proof or sketch anywhere.
  - `Comp.seqPair_le_par` — **thread inlining**, `M ∥ N ↠ ⟨M,N⟩` (Fig. 3 p.12,
    Table 3 p.44), the paper's RA-vs-x86-TSO discriminator (p.45), claimed and
    never proved.  Original.
  - `bindGen_parGen_subset` and `Comp.bind_par_le_par_bind` — **Proposition
    E.1**, *Generalized Sequencing* (p.58): the exchange law
    `(P₁ ||| Q₁) >>= (λ⟨a,b⟩. F a ||| G b) ⊆ (P₁ >>= F) ||| (Q₁ >>= G)`.  The
    generating-set form needs no closure and no hypothesis on the rule set,
    which is stronger than the paper's proof.  Note that the paper's proof text
    contradicts its own statement of the direction; see the module docstring.
  - `Comp.mapRet_image_subset_par_pure` — `P ⊆ P ||| return r`, the reachable
    half of the unit law.  Original.
  - `par_pure_pure_nonempty` and `par_pure_pure_ne_bot`
    (`Isotope/Elgot/RA/ParExamples.lean`) — a concrete trace of
    `return a ||| return b`, so that `Comp.par` is demonstrably not vacuous
    despite `inf_μ` being characterised rather than constructed.
* Worked examples in `Isotope/Elgot/RA/Examples.lean`: `pure_ne_pure`,
  `bot_ne_pure`, `storedMem_wellFormed` (a well-formed memory with two messages
  at one location), `mem_store`, `store_ne_pure`, `store_ne_bot`, `load_stale`
  (a load returning a value that a strictly later write at the same location
  has already superseded), and the loop examples `iter_diverge`, `iter_exit`,
  `iter_store_diverge`.
-/
