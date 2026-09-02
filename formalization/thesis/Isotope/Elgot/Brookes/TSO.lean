import Isotope.Elgot.Brookes.TSO.Basic
import Isotope.Elgot.Brookes.TSO.Monad
import Isotope.Elgot.Brookes.TSO.Interleaving
import Isotope.Elgot.Brookes.TSO.Invariant
import Isotope.Elgot.Brookes.TSO.Litmus
import Isotope.Elgot.Brookes.TSO.Examples
import Isotope.Elgot.Brookes.TSO.Compare

/-!
# A Brookes-style store-buffer model of TSO weak memory

`TSO.Comp Tid Loc Val` is the Brookes monad of `Brookes/Monad.lean` at the
stuttering/mumbling rewriting system over the state

    St = (global memory : Loc → Val) × (write buffer per thread : Tid → List (Loc × Val))

Memory operations are the paper's, sandwiched between partial buffer flushes:
`write` appends to the issuing thread's buffer, `pflush` commits a prefix of it,
`read` observes the issuing thread's own buffered write if there is one and global
memory otherwise, and `fence` drains the buffer.  The sequentially consistent
operations `writeSC`/`readSC` live in the *same* monad over the *same* state, so
that TSO and SC can be compared as sets of traces rather than through a
translation.

## What is proved

* Carrier, `pure` and `bind`, `Monad`, `LawfulMonad`, `Iterate` and
  `LawfulElgotMonad` — **inherited, not reproved**.  `TSO.Comp` is
  `Brookes (SeqCst.rewriting (St Tid Loc Val))`, and the whole generic
  development of `Brookes/{Closure,Monad,Iteration}.lean` applies verbatim, since
  the TSO model differs from sequential consistency only in its *state*, exactly
  as the paper suggests at lines 5191-5193.  Closure under the healthiness
  condition is `Rewriting.closure_closed`; there is no extra healthiness field on
  the carrier (see the boundary below).
* `Buf.peek`, with the paper's three defining equations for `[·]_ℓ`
  (lines 4827-4839): `Buf.peek_nil`, `Buf.peek_append_self`, `Buf.peek_append_ne`.
* `pflush_idem` — the lemma the paper uses at lines 4913-4918 to make `pflush` an
  identity, and never proves — together with `pflush_write`, `write_pflush`,
  `pflush_read`, `read_pflush`, `pflush_fence`.  These are the content for which
  the paper builds the idempotent-envelope category `Ide(Set_TSO, pflush)`
  (lines 4908-4939); as equations between operations they need no new category,
  and no `Ide` construction is made here.
* `Interleave`, `par` and `Seq`, with `Seq.of_refines`: stuttering and mumbling
  can only *undo* into an interference-free execution, which is what makes
  reasoning about the closure of `par` possible at all.
* The write-then-read invariant `Wrote`, closed under refinement
  (`Wrote.refines`), and the four propagation lemmas culminating in
  `store_buffering_absurd`.
* **`sc_forbids_store_buffering`**: no interference-free execution of
  `(x := 1; r₁ := y) ∥ (y := 1; r₂ := x)` with sequentially consistent writes,
  started from `x = y = 0`, has `r₁ = r₂ = 0`.
* **`tso_admits_store_buffering`**: an explicit interference-free execution of the
  same program with TSO writes that does have `r₁ = r₂ = 0`.
* **`tso_strictly_richer`**: the two together.
* `writeCore_invisible` (a TSO write changes no global memory) versus
  `writeSC_visible`, `writeCore_ne_writeSC`, and
  `writeCore_fence_commits` (after a fence the buffered write is in memory and
  the buffer is empty) with its ingredients `fence_drains`, `fence_commits`.
* `SeqCst.mapState`, a monad morphism on the nose for any state abstraction, and
  its instance `toSeqCst` forgetting write buffers: `toSeqCst_writeSC` and
  `toSeqCst_readSC` are equalities with the sequential-consistency model of
  `Brookes/SeqCst.lean`, `toSeqCst_writeCore_le` says a buffered write abstracts
  to a stutter, and `toSeqCst_writeCore_ne_writeSC` says the abstraction is still
  not degenerate.

## Honest boundary

* **This is not the Kavanagh-Brookes pomset semantics.**  The paper
  (`papers/isotope/denotational-semantics-of-ssa.tex`, lines 4740-5008, after
  `\citet{sparky}`) builds TSO from pomsets over `𝒜_TSO` quotiented by removal of
  the null action, `TSO = StateT Buf (Traces Σ)` for the stream action `Σ` on TSO
  pomsets, a post-filter for validity, and finally the idempotent-envelope
  category `PTSO = Ide(Set_TSO, pflush)`.  **None of that is formalized here.**
  What is here is an *interleaving* store-buffer model, which is what the paper's
  own closing remark (lines 5191-5193 — "more complex states (e.g. involving
  per-thread buffers) and closure operators can allow us to model weak memory
  models; [jagadeesan-brookes-relaxed-12] gives a Brookes model of TSO") licenses.
  A faithful pomset port needs infinite pomsets up to isomorphism of labelled
  posets with a side-conditioned quotient, the `Traces Σ` Elgot structure with its
  productive-divergence branch, and `Ide` as a bespoke category whose identity is
  not `𝟙`; the `discretion` port of the pomset layer is finite-only and its
  `MonadIterate`/`ElgotMonad` instances are unfinished, and `formalization/CLAIM_AUDIT.md`
  records the `sparky` snapshot as carrying active proof holes in exactly that
  machinery.  **Nothing here discharges the paper's claim that "the SPARC TSO
  semantics forms a valid model of SSA"; that row of `CLAIM_AUDIT.md` stays
  contradicted.**
* **Two deliberate divergences from the paper's operations.**  The globally
  visible write event is emitted when a buffered write drains, not when it is
  issued (the paper's line 4848 emits it at issue time, which is only coherent
  under its post-filter); and a read that misses in the buffer reads memory
  rather than an arbitrary value (line 4845).  Both are forced by taking an
  interleaving reading.  Two paper errata noticed while porting: line 4823 should
  read `Traces Σ`, not the deterministic `Trace Σ`, since every subsequent TSO
  denotation is set-valued; and `W_x^TSO` at line 4848 returns `v` where its
  declared type (line 4773) says `𝟏`.
* **Partial correctness only.**  Iteration is the inherited `Brookes` one: it
  collects finite executions and discards divergence, so an always-recursing body
  denotes `⊥`.  *No divergence completion is needed for lawful Elgot iteration* —
  `LawfulElgotMonad (Brookes c)` is a genuine instance with all four laws — so
  the answer to "which completion does a lambda-iter model need?" is: none.  A
  completion would be needed only to distinguish divergence from having no
  execution at all, and to support the paper's nonempty-set (`𝒫⁺`) variant, which
  is *incompatible* with finite-trace-only iteration: a divergent body has no
  finite run, so its iteration would be empty.  Infinite traces are neither
  constructed nor claimed.
* **No healthiness condition on the carrier.**  The paper's validity condition
  (lines 4886-4892: at least one execution completely flushes the buffer,
  whatever the initial state) is not imposed, and is not even stable: it fails for
  `pure` from a non-empty buffer, which is exactly why the paper's
  `pflush ; id ; pflush = pflush ≠ id` (lines 4900-4906) does not cut out a
  subcategory, and it is not preserved by iteration.  It is not formalized here in
  any form, not even as a predicate.
* **Rely steps are unconstrained.**  As in any Brookes monad, nothing in
  `TSO.Comp` stops the environment from rewriting a thread's *own* write buffer
  between its steps, so the trace set contains executions no real machine has.
  Neither result above depends on excluding them: the invariant `OkStep`
  constrains global memory only, and the TSO witness is an explicit trace.  A
  model that ruled them out would need buffer ownership in the closure operator
  or in `par`, and is not attempted.
* **`par` is not the paper's fork-join `∥`.**  It is plain trace interleaving on a
  shared state carrying one buffer per thread.  The paper's operator (lines
  4863-4880) flushes first, runs the branches with *separate* buffers, and filters
  executions that fail to flush; none of that is here.  `par` is also not part of
  the monad and no lambda-iter obligation mentions it — it exists only so that the
  litmus test has two threads.
* **The fenced litmus is not proved.**  `writeCore_fence_commits` proves that a
  fence publishes the buffered write, which is the mechanism, but the statement
  "the two-thread program with fences forbids `r₁ = r₂ = 0`" is *not* proved.  The
  obstruction is real: a thread's trace set contains executions whose leading
  `pflush` commits writes the environment left in its buffer, to arbitrary
  locations, so the `Wrote` invariant does not hold of the fenced program without
  an initial-empty-buffer side condition, which is not a thread-local property of
  a trace.
* **No `InstructionModel`, and so no shipped lambda-iter model.**  `TSO.Comp`
  satisfies every *monad* class `Isotope/LambdaIter/Semantics/Denotation.lean`
  requires, so any `TypeModel`/`InstructionModel` over it yields a lambda-iter
  model by instance resolution; but that needs a concrete type universe with
  `TypeFormers`, `Subtyping` and a `LawfulTypeModel`, none of which is chosen
  here.  No instance is shipped and no model claim is made.
* **`toSeqCst` is not shown to commute with `iter`**, only with `pure` and `bind`.
* The separations rest on the invariants actually proved.  Finer facts — for
  instance that `write i ℓ v` and `write i ℓ w` differ for `v ≠ w`, or a
  characterisation of the closed trace set of any composite program — are not
  proved.
-/
