import Isotope.Elgot.Par.Litmus
import Isotope.Elgot.Par.RA
import Isotope.Elgot.Brookes

/-!
# Parallel composition across the models: what holds, and what does not

One place recording which law holds for which parallel-composition operator, and what is
proved about the relationships between the models.  Every positive entry below is checked by
an `example` or a theorem in this file; the negative entries are the honest boundary.

## The operators

| # | operator | carrier | defined in |
|---|---|---|---|
| 1 | `Brookes.par` at a pointwise `c` | `Brookes c A` | `Brookes/TSO/Interleaving.lean` |
| 2 | sequential consistency | `SeqCst.Comp Loc Val A` | operator 1 at `rewriting (Store …)` |
| 3 | store-buffer TSO | `Brookes.TSO.Comp Tid Loc Val A` | operator 1 at `rewriting (St …)` |
| 4 | release/acquire `∥∥∥` | `RA.Comp R Loc Val A` | `RA/Parallel.lean` |
| 5 | pomset `∥` | `Pom A` | `Pomset/Quotient.lean` |

Operators 2 and 3 are *the same operator* at two rewriting systems: the store-buffering
separation of `Brookes/TSO/Litmus.lean` compares two denotations of `write` inside one
parallel composition, not two parallel compositions.

## The law table

| law | 1/2/3 | 4 (RA) | 5 (pomset) |
|---|---|---|---|
| `ParOp` | yes | yes | homogeneous shape |
| `ParMono` (monotone) | yes | yes (Prop. 7.4) | no order on `Pom` |
| `ParSymm` (symmetry) | yes | proved, but not in `<$>` form | yes (`par_comm`) |
| `ParAssoc` | **yes** (new) | open; shuffle half proved | yes (`par_assoc`) |
| `ParUnit` | **yes** (new) | open | yes (`par_one`) |
| `ParNat` (naturality) | **yes** (new) | open | not applicable |
| `ParExchange` | yes | yes at `R = 𝔠` (Prop. E.1) | **false** (`pom_exchange_fails`) |
| `ParInline` (inlining) | yes | yes at `R = 𝔠` | not applicable |
| `⊥` annihilates | yes (`bot_par`) | yes (`Comp.bot_par`) | not applicable |
| commutative monoid on `M PUnit` | yes | no | yes |

The three entries marked **new** are what this track adds, and they come from one hypothesis:
`IsPointwise`, that every rewrite replaces a contiguous block by a single event.  Stuttering
and mumbling are pointwise, so operators 1–3 acquire associativity, both unit laws and
naturality simultaneously.

## The relationships between the models

Three are proved, and they are of three different kinds.

1. **A shared structure.**  `punitParMonoid` turns any typed operator with symmetry,
   associativity, unit and naturality into a commutative monoid on unit-returning
   computations.  Brookes-style parallel composition and the pomset operator are therefore
   commutative monoids of the *same* signature — which is the only sense in which they can be
   compared directly, since `Pom` has no monad under it and `Brookes c` has no single carrier.
2. **A genuine difference.**  The interchange law with sequencing holds for the interleaving
   operators (as `≤`) and is *false* for the pomset operator (`pom_exchange_fails`).
   Interleaving sequences one of many linear orders; a pomset genuinely acquires edges.
3. **Two litmus separations.**
   * sequential consistency versus store-buffer TSO, at store buffering: in
     `Brookes/TSO/Litmus.lean`, restated below as `sc_vs_storeBufferTSO`.
   * sequential consistency versus the pomset TSO model, at `x := v ; read x`:
     `pomsetTSO_strictly_richer` of `Isotope/Elgot/Par/Litmus.lean`.

Neither is a "strictly fewer behaviours" theorem, and neither is claimed to be one.  The
models have different state types and different trace shapes; a litmus separation is what is
available, and it is what is proved.

## Honest boundary

1. **Release/acquire associativity is still open**, and the route that works for Brookes is
   not available: `Step R` rewrites whole chronicles (`Cn` maps every memory through a pull),
   so no `IsPointwise` decomposition exists to pull a rewrite back through a shuffle.  What is
   proved is the shuffle half — `ChroInterleave.assoc`, including the non-obvious part that
   the middle chronicle exists at all.  The memory half, agreement of `inf_{ξ.o}{α₁, α₂}` at
   two different opening memories, cannot even be *stated* as an equation while `inf_μ` is
   characterised (`IsInfMem`) rather than constructed.
2. **The release/acquire unit law and interchange are untouched**, as is Deferral of Closure
   for `|||` (Lemma 8.5); see honest boundary item 8 of `Isotope/Elgot/RA.lean`.
3. **`ParSymm` is not instantiated for release/acquire** even though symmetry is proved: the
   proved statement is an equality of trace sets under `PreTrace.mapRet`, which is *stronger*
   than the `<$>` form at rule sets where the unit laws fail.
4. **There is no parallel composition on the pomset TSO monad.**  `Pom.par` composes
   *effects*; two TSO threads have separate write buffers, and `WS (Buf …) …` threads a single
   state, so `TSO Loc Val A → TSO Loc Val B → TSO Loc Val (A × B)` has no honest definition
   without either a two-buffer state or a drained-composition side condition.  None is
   attempted here.
5. **The pomset litmus separation is not about weak memory.**  The outcome is admitted
   because `readCore` returns an arbitrary value on a buffer miss and the paper's post-filter
   (L4781-4788) is not formalised, not because of store buffering.  Said plainly: it is a
   separation against the model *as transcribed*.
6. **Iteration and parallel composition never meet.**  No law relating `par` to `iter` is
   proved for any of the operators, and none is claimed.
7. **The sequential-consistency-versus-release/acquire separation is a different
   workstream** and is deliberately absent here.
8. **Thread inlining is not proved strict.**  `ParInline` says sequencing refines parallel
   composition; that the refinement is *proper* — that some interleaving is not a sequencing —
   is not proved for any operator here, and it is the natural next litmus: it needs a
   non-membership argument against a closure, of the kind that
   `Isotope/Elgot/Brookes/TSO/Litmus.lean` runs for store buffering.
9. **`Pom` has no refinement order**, so the pomset operator's failures are recorded as
   failures of *equations*.  With the paper's order on pomsets the interchange law would be
   expected to hold as a refinement; that is not formalised and is not claimed.
-/

universe u

namespace Isotope.Elgot.Par

open Isotope.Elgot Isotope.Elgot.Brookes

section Table

variable {E : Type u} {c : Rewriting E} {S Loc Val Tid A : Type u}

/-! ### Operator 1: Brookes-style parallel composition at a pointwise rewriting system -/

example : ParOp (Brookes c) := inferInstance
example : ParMono (Brookes c) := inferInstance
example : ParSymm (Brookes c) := inferInstance
example : ParExchange (Brookes c) := inferInstance
example : ParInline (Brookes c) := inferInstance
example [IsPointwise c] : ParAssoc (Brookes c) := inferInstance
example [IsPointwise c] : ParUnit (Brookes c) := inferInstance
example [IsPointwise c] : ParNat (Brookes c) := inferInstance
example [IsPointwise c] : ParMonoid (Brookes c PUnit.{u + 1}) := inferInstance

/-- **`⊥` annihilates Brookes-style parallel composition**: a thread with no executions
leaves the composition with none. -/
@[simp] theorem par_bot {B : Type u} (x : Brookes c A) :
    Brookes.par x (⊥ : Brookes c B) = ⊥ := by
  refine le_antisymm (Brookes.le_of_mem ?_) bot_le
  rintro t ⟨a, b⟩ hm
  obtain ⟨w₀, t₁, t₂, h₁, h₂, hi, hr⟩ := Brookes.mem_par_iff.1 hm
  exact absurd h₂ (Brookes.not_mem_bot _)

/-- **`⊥` annihilates on the left** as well. -/
@[simp] theorem bot_par {B : Type u} (y : Brookes c B) :
    Brookes.par (⊥ : Brookes c A) y = ⊥ := by
  refine le_antisymm (Brookes.le_of_mem ?_) bot_le
  rintro t ⟨a, b⟩ hm
  obtain ⟨w₀, t₁, t₂, h₁, h₂, hi, hr⟩ := Brookes.mem_par_iff.1 hm
  exact absurd h₁ (Brookes.not_mem_bot _)

/-! ### Operators 2 and 3: sequential consistency and store-buffer TSO

Both are operator 1 at a rewriting system generated by stuttering and mumbling, so all of the
laws are available at both without further work. -/

example : IsPointwise (SeqCst.rewriting S) := inferInstance
example : ParAssoc (SeqCst.Comp Loc Val) := inferInstance
example : ParUnit (SeqCst.Comp Loc Val) := inferInstance
example : ParNat (SeqCst.Comp Loc Val) := inferInstance
example : ParSymm (SeqCst.Comp Loc Val) := inferInstance
example : ParExchange (SeqCst.Comp Loc Val) := inferInstance
example : ParMonoid (SeqCst.Comp Loc Val PUnit.{u + 1}) := inferInstance

example : ParAssoc (Brookes.TSO.Comp Tid Loc Val) := inferInstance
example : ParUnit (Brookes.TSO.Comp Tid Loc Val) := inferInstance
example : ParSymm (Brookes.TSO.Comp Tid Loc Val) := inferInstance
example : ParExchange (Brookes.TSO.Comp Tid Loc Val) := inferInstance

/-! ### Operator 4: release/acquire -/

example {R : RA.RuleSet} {L V : Type} : ParOp (RA.Comp R L V) := inferInstance
example {R : RA.RuleSet} {L V : Type} : ParMono (RA.Comp R L V) := inferInstance
example {L V : Type} : ParExchange (RA.Comp RA.cRules L V) := inferInstance
example {L V : Type} : ParInline (RA.Comp RA.cRules L V) := inferInstance

/-! ### Operator 5: pomsets -/

example [Isotope.Pomset.Tick A] : ParMonoid (Isotope.Pomset.Pom A) := inferInstance

end Table

/-! ## The two litmus separations, restated -/

section Separations

variable {Tid Loc Val : Type u} [DecidableEq Loc] {x y : Loc} {v0 v1 : Val}

/-- **Sequential consistency versus store-buffer TSO**, at store buffering.  A restatement of
`Isotope.Elgot.Brookes.TSO.tso_strictly_richer`, which is proved in
`Isotope/Elgot/Brookes/TSO/Litmus.lean`: both sides use *this* track's parallel operator,
`Brookes.par` at the pointwise rewriting system `SeqCst.rewriting (St Tid Loc Val)`. -/
theorem sc_vs_storeBufferTSO [DecidableEq Tid] {i j : Tid} (hij : i ≠ j) (hxy : x ≠ y)
    (hv : v0 ≠ v1) :
    (∃ (t : Brookes.TSO.Tr Tid Loc Val) (sf : Brookes.TSO.St Tid Loc Val),
        (t, (v0, v0)) ∈ Brookes.par (Brookes.TSO.sbTSO i x y v1) (Brookes.TSO.sbTSO j y x v1) ∧
          Brookes.TSO.Seq (Brookes.TSO.initSt v0) t sf) ∧
      ∀ (t : Brookes.TSO.Tr Tid Loc Val) (sf : Brookes.TSO.St Tid Loc Val),
        Brookes.TSO.Seq (Brookes.TSO.initSt v0) t sf →
        (t, (v0, v0)) ∉ Brookes.par (Brookes.TSO.sbSC x y v1) (Brookes.TSO.sbSC y x v1) :=
  Brookes.TSO.tso_strictly_richer hij hxy hv

/-- **Sequential consistency versus the pomset TSO model**, at `x := v ; read x`.  A
restatement of `pomsetTSO_strictly_richer`.  See the honest boundary above: the outcome is
admitted because the model as transcribed lacks its post-filter. -/
theorem sc_vs_pomsetTSO (v w : Val) (hw : w ≠ v) :
    (∃ e ∈ ((Isotope.Elgot.TSO.write x v >>=
        fun _ ↦ Isotope.Elgot.TSO.read x (⟨⟩ : PUnit.{u + 1}) :
          Isotope.Elgot.TSO Loc Val Val)).runs ([] : Isotope.Elgot.TSO.Buf Loc Val),
      e.value = w) ∧
    (∀ {t : Trace (SeqCst.Store Loc Val × SeqCst.Store Loc Val)}
      {s sf : SeqCst.Store Loc Val}, Seq s t sf →
      (t, w) ∉ (SeqCst.write x v >>= fun _ ↦ SeqCst.read x)) :=
  pomsetTSO_strictly_richer x v w hw

end Separations

end Isotope.Elgot.Par
