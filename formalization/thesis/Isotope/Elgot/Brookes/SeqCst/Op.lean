import Isotope.Elgot.Brookes.SeqCst.Op.Basic
import Isotope.Elgot.Brookes.SeqCst.Op.Traces
import Isotope.Elgot.Brookes.SeqCst.Op.Clauses
import Isotope.Elgot.Brookes.SeqCst.Op.Counted
import Isotope.Elgot.Brookes.SeqCst.Op.Seq
import Isotope.Elgot.Brookes.SeqCst.Op.While
import Isotope.Elgot.Brookes.SeqCst.Op.Par
import Isotope.Elgot.Brookes.SeqCst.Op.Prop62

/-!
# An operational semantics for the shared-variable parallel language

`Brookes/SeqCst/Syntax.lean` transcribes Brookes's Proposition 6.2 and takes the
resulting compositional clauses as the *definition* of the trace semantics `T`.
This directory supplies the missing operational side: a small-step machine, its
transition traces, and a proof that their closure is that same `T`.  Proposition
6.2 is therefore a theorem here, not a definition, and full abstraction can be
stated with no denotational vocabulary at all.

## What is proved

* `Op.Red` / `Op.Reds` (`Op/Basic.lean`) — the small-step relation on
  configurations `Option (Com Loc Val) × Store Loc Val`, with `none` the
  terminated residual.  `await` is a single step whose premise is a whole
  terminating `Reds` derivation of its body; this is strictly positive, so the
  mutual block needs no fuel, stratification or well-founded recursion.
  `steps_iff` identifies `Reds` with `Relation.ReflTransGen CStep`, and
  everything after `Op/Basic.lean` works in the latter.
* `Op.Run`, `Op.TTrace`, `Op.opDen`, `Op.opObs` (`Op/Traces.lean`) — running
  with interference, transition traces, the closure `opDen`, and operational
  termination.  `TTrace.ne_nil` is ε-freeness; `opObs_iff` is the one-pair
  fragment, whose content is `Run.stitch`: a run whose pairs form an
  interference-free `Chain` is a single uninterrupted execution.  `run_peel`
  exposes the first real small step of a transition trace.
* The clauses of Proposition 6.2, one per module:
  `opDen_skip`, `opDen_assign`, `opDen_await`, `opDen_ite` (`Op/Clauses.lean`,
  via the reusable `Op.Atomic` machinery), `opDen_seq` (`Op/Seq.lean`, via
  `seqCfg` and a step-counted decomposition from `Op/Counted.lean`),
  `opDen_wh` (`Op/While.lean`, the `⊆` half by strong induction on the step
  count), and `opDen_par` (`Op/Par.lean`, by per-small-step thread projection
  into an `Interleave`).
* `Op.opDen_eq_den` (`Op/Prop62.lean`) — **Proposition 6.2**.
* `Op.obs_iff_opObs` — **adequacy**, Brookes's `M[C] = {(s,s') ∈ T[C]}`.
* `Op.OpCtxLe`, `Op.opCtxLe_iff_ctxLe` — the substitutive preorder with the
  observation read operationally, identified with `SeqCst.CtxLe`.
* `Op.opFullAbstraction : opDen C ≤ opDen C' ↔ OpCtxLe C C'` and its equational
  and fully-spelled-out forms `opFullAbstraction_eq`, `fullAbstraction_op` —
  **full abstraction for the shared-variable parallel language, stated entirely
  operationally**.

## Honest boundary

The machine is *ours*, not a transcription.  Brookes's journal §3 transition
system is over finite partial states with a `dom(s)` discipline, and it
restricts `await` bodies syntactically to make them atomic; `Red`/`Reds` is the
natural total-state reading of it, with `await` bodies left unrestricted, so the
language here is *wider* than his.  `opDen_eq_den` is thus a theorem relating
our machine to the transcribed clauses, not an independent verification of the
transcription against the paper.  The `await` clause in particular holds by
construction: `Red.await` stipulates atomicity for an arbitrary body.

The narrowings inherited from `Brookes/SeqCst/Syntax.lean` — restricted
expressions, total finitely-indexed states, no state traces, finite traces and
partial correctness — are unchanged and are listed in the module docstring of
`Brookes/SeqCst/FullAbstraction.lean`.
-/
