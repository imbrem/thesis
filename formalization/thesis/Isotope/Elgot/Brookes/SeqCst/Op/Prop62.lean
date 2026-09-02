import Isotope.Elgot.Brookes.SeqCst.Op.While
import Isotope.Elgot.Brookes.SeqCst.Op.Par
import Isotope.Elgot.Brookes.SeqCst.FullAbstraction

/-!
# Proposition 6.2, adequacy, and operational full abstraction

> **Proposition 6.2** (Brookes, *Full Abstraction for a Shared-Variable Parallel
> Language*, Inform. and Comput. 127(2):145–163, 1996, journal p. 150).
> *The transition trace semantics `T` satisfies the compositional clauses*
> `T[skip] = T[true]`, `T[I:=E] = …`, `T[C₁;C₂] = T[C₁] ; T[C₂]`,
> `T[C₁ ∥ C₂] = T[C₁] ∥ T[C₂]`, `T[if B then C₁ else C₂] = …`,
> `T[while B do C] = (T[B];T[C])* ; T[¬B]`, `T[await B then C] = …`.

`SeqCst.den` takes those clauses as its *definition*.  `Op.opDen` is the honest
operational `T`: the closure of the set of transition traces of the small-step
machine of `Op/Basic.lean`.  `opDen_eq_den` below is Proposition 6.2 — the two
agree — and it is proved by assembling the per-clause theorems of `Op/Clauses.lean`,
`Op/Seq.lean`, `Op/While.lean` and `Op/Par.lean` by structural induction on the
command.  There is no circularity: `opDen_wh` invokes `opDen_seq` at
`Com.seq C (Com.wh b C)`, but `opDen_seq` is a general theorem about the
operational semantics, not an induction hypothesis.

`obs_iff_opObs` is the second half of the bridge, Brookes's
`M[C] = {(s,s') | (s,s') ∈ T[C]}`: the denotationally-extracted observation
`SeqCst.Obs` coincides with operational termination `opObs`.  It is
`opDen_eq_den` together with the one-pair fragment `opObs_iff` of
`Op/Traces.lean`.

Everything downstream then transfers by rewriting.  `OpCtxLe` is Brookes's
substitutive preorder with the observation read operationally, and
`opCtxLe_iff_ctxLe` identifies it with the existing `SeqCst.CtxLe`, so
`opFullAbstraction` is full abstraction for the shared-variable parallel
language **stated entirely operationally**: on the left, inclusion of the
stutter/mumble closures of the sets of transition traces of a small-step
machine; on the right, preservation of terminating executions under every
program context.  `fullAbstraction_op` is the same theorem with every notion
spelled out.

## What this does and does not vindicate

The small-step machine `Red`/`Reds` is **ours**, not a transcription of
Brookes's journal §3 transition system: his is over finite partial states with a
`dom(s)` discipline and syntactically restricted `await` bodies, and `Red` is
the natural total-state reading of it with `await` bodies left unrestricted (see
the "`await` widens the language" section of `Op/Clauses.lean`).  So
`opDen_eq_den` establishes that the transcribed clauses *are* the transition
trace semantics of a small-step machine — it is not, and cannot be, an
independent check of the transcription against the paper's own machine.
-/

namespace Isotope.Elgot.Brookes

universe u

namespace SeqCst.Op

variable {Loc Val : Type u}

section

variable [DecidableEq Loc] [DecidableEq Val]

/-! ## Proposition 6.2 -/

/-- **Brookes, Proposition 6.2.**  The operational transition trace semantics
`opDen` — the stutter/mumble closure of the set of transition traces of the
small-step machine — coincides with the compositional clauses that `SeqCst.den`
takes as its definition.

Each case is the corresponding clause of `Op/Clauses.lean`, `Op/Seq.lean`,
`Op/While.lean` or `Op/Par.lean`, with the induction hypotheses used only to
replace `opDen Cᵢ` by `den Cᵢ`. -/
theorem opDen_eq_den (C : Com Loc Val) : opDen C = den C := by
  induction C with
  | skip => rw [opDen_skip, den_skip]
  | assign ℓ e => rw [opDen_assign, den_assign]
  | seq C₁ C₂ ih₁ ih₂ => rw [opDen_seq, den_seq, ih₁, ih₂]
  | par C₁ C₂ ih₁ ih₂ => rw [opDen_par, den_parU, ih₁, ih₂]
  | ite b C₁ C₂ ih₁ ih₂ => rw [opDen_ite, den_ite, ih₁, ih₂]
  | wh b C ih => rw [opDen_wh, den_wh, ih]
  | await b C ih => rw [opDen_await, den_await, ih]

/-- Proposition 6.2 read as a description of the trace *set*: the denotation of
`C` is the stutter/mumble closure of its set of transition traces. -/
theorem den_eq_closure_ttrace (C : Com Loc Val) :
    (den C).traces = (rewriting (Store Loc Val)).closure {p | TTrace C p.1} := by
  rw [← opDen_eq_den]; rfl

/-! ## Adequacy -/

/-- **Adequacy**, Brookes's `M[C] = {(s,s') | (s,s') ∈ T[C]}`.  The observation
extracted from the denotation is exactly operational termination: `C` run from
`μ` with no interference reaches a terminated configuration with store `ν`. -/
theorem obs_iff_opObs (C : Com Loc Val) (μ ν : Store Loc Val) :
    SeqCst.Obs C μ ν ↔ opObs C μ ν := by
  change SeqCst.obs (den C) μ ν ↔ _
  rw [← opDen_eq_den]
  exact opObs_iff

/-! ## The operational contextual preorder -/

/-- **Brookes's substitutive preorder, operationally.**  `C` may be replaced by
`C'` in every program context without adding terminating executions of the
small-step machine. -/
def OpCtxLe (C C' : Com Loc Val) : Prop :=
  ∀ P : SeqCst.Ctx Loc Val, ∀ μ ν : Store Loc Val, opObs (P.plug C) μ ν → opObs (P.plug C') μ ν

/-- **Brookes's substitutive equivalence, operationally.** -/
def OpCtxEq (C C' : Com Loc Val) : Prop := OpCtxLe C C' ∧ OpCtxLe C' C

/-- The operational contextual preorder is the denotational one: adequacy holds
in every context, so the two induce the same substitutive preorder. -/
theorem opCtxLe_iff_ctxLe {C C' : Com Loc Val} : OpCtxLe C C' ↔ SeqCst.CtxLe C C' := by
  simp only [OpCtxLe, SeqCst.CtxLe, obs_iff_opObs]

/-- The operational contextual equivalence is the denotational one. -/
theorem opCtxEq_iff_ctxEq {C C' : Com Loc Val} : OpCtxEq C C' ↔ SeqCst.CtxEq C C' :=
  and_congr opCtxLe_iff_ctxLe opCtxLe_iff_ctxLe

/-- Trace refinement, spelled out on raw transition traces: every transition
trace of `C` is a stutter/mumble refinement of some transition trace of `C'`. -/
theorem opDen_le_iff_ttrace {C C' : Com Loc Val} :
    opDen C ≤ opDen C' ↔ ∀ t, TTrace C t →
      ∃ t₀, TTrace C' t₀ ∧ (rewriting (Store Loc Val)).Refines t₀ t :=
  opDen_le_iff.trans (forall_congr' fun _ ↦ imp_congr_right fun _ ↦ mem_opDen_iff)

/-! ## Full abstraction, operationally -/

section

variable [Fintype Loc]

/- `Fintype Loc` does not appear in the *statements* below, only in the proof of
the completeness half they inherit from `SeqCst.fullAbstraction`. -/
set_option linter.unusedFintypeInType false

/-- **Full abstraction for the shared-variable parallel language, stated
operationally** (Brookes, Propositions 6.2 and 7.1 combined).

The left-hand side is inclusion of the stutter/mumble closures of the sets of
transition traces of the small-step machine of `Op/Basic.lean`; the right-hand
side is preservation of terminating machine executions under every program
context.  This is the statement that `Brookes/SeqCst/FullAbstraction.lean` could
only make denotationally. -/
theorem opFullAbstraction {C C' : Com Loc Val} : opDen C ≤ opDen C' ↔ OpCtxLe C C' := by
  rw [opDen_eq_den, opDen_eq_den, opCtxLe_iff_ctxLe]
  exact SeqCst.fullAbstraction

/-- **Equational full abstraction, operationally.** -/
theorem opFullAbstraction_eq {C C' : Com Loc Val} : opDen C = opDen C' ↔ OpCtxEq C C' := by
  rw [opDen_eq_den, opDen_eq_den]
  exact SeqCst.fullAbstraction_eq.trans opCtxEq_iff_ctxEq.symm

/-- **Full abstraction with every notion spelled out operationally.**  No
denotation occurs in the statement -- the only non-machine notion is the
stutter/mumble rewriting: on the left, transition traces
of the small-step machine up to stuttering and mumbling; on the right, the
reflexive-transitive closure of the machine's step relation, under every program
context. -/
theorem fullAbstraction_op {C C' : Com Loc Val} :
    (∀ t, TTrace C t → ∃ t₀, TTrace C' t₀ ∧ (rewriting (Store Loc Val)).Refines t₀ t) ↔
    (∀ (P : SeqCst.Ctx Loc Val) (μ ν : Store Loc Val),
        Relation.ReflTransGen CStep (some (P.plug C), μ) ((none : Option (Com Loc Val)), ν) →
        Relation.ReflTransGen CStep (some (P.plug C'), μ) ((none : Option (Com Loc Val)), ν)) :=
  opDen_le_iff_ttrace.symm.trans opFullAbstraction

end

end

end SeqCst.Op

end Isotope.Elgot.Brookes
