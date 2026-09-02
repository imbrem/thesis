import Isotope.Elgot.TSO.Alphabet
import Isotope.Elgot.TSO.Basic
import Isotope.Elgot.TSO.Ops
import Isotope.Elgot.TSO.Validity
import Isotope.Elgot.TSO.PTSO
import Isotope.Elgot.TSO.Examples

/-!
# The SPARC TSO pomset model

A mechanisation of the pomset-based SPARC TSO semantics of Kavanagh and Brookes as presented
in *The Denotational Semantics of SSA* (`papers/isotope/denotational-semantics-of-ssa.tex`,
L4700-5170), in the finite, partial-correctness fragment.

## What is proved

* `Isotope.Pomset` — finite pomsets modulo the `δ`-quotient, with `Monoid (Pom A)` the
  paper's concatenation monoid (L4750-4756), `Pom.par` the parallel monoid, faithfulness of
  the linear embedding (`PrePom.ofList_deq_iff`), and a witness that the quotient is strictly
  richer than the free monoid (`Pom.mk_seq_ne_mk_par`).
* `Isotope.Elgot.WS` — `WS S M`, a monoid-generic nondeterministic state-and-effect monad,
  with `Monad`, `LawfulMonad`, `Iterate` and a full `LawfulElgotMonad` instance.  Since
  `CategoryTheory.Kleisli.Type.strongElgotFreydCategory` is stated for any
  `[Iterate m] [LawfulElgotMonad m]`, this discharges the λ_iter model requirement by
  instance resolution.
* `Act`, `Buf`, `Buf.toPom` — the alphabet `𝒜_TSO` (L4766-4769, L4818-4821) and buffers as
  linear pomsets, with `Buf.toPom_inj`: the embedding of buffers into pomsets is injective.
* `Buf.peek` — the buffer lookup of L4827-4838, with its three defining equations proved in
  the paper's append-at-the-end orientation.
* `pflush`, `read`, `write`, `fence` — L4841-4862, with `pflush_kcomp_pflush` (the
  idempotence L4913-4918 relies on but never states), the sandwich equations
  `pflush ≫ₖ read x = read x` and friends, and `pflush_ne_pure`: the paper's healthiness
  condition `pflush ; f ; pflush = f` genuinely fails for the identity (L4893-4906).
* `Drainable` — the paper's first validity candidate (L4893-4897), with closure under
  sequencing and the two negative facts that keep it out of the carrier.
* `CategoryTheory.Ide` and `PTSO` — the idempotent envelope (L4927-4939) as a genuine
  Mathlib `Category`, and `PTSO = Ide(Set_TSO, pflush)` with `pflush` as its identity.

## Honest boundary

**Finite pomsets only.**  `PrePom`'s carrier is `Fin card` by construction.  The paper's
infinite pomsets, the sum `Σ_n α_n` over an arbitrary poset, and the stream action
`Σ : Pom_fin^ω → Pom` (L4757-4762) are not representable and are not attempted.  `trim`
(L4751) is therefore the identity here, and the side condition that infinite sets are equated
only to other infinite pomsets (L4744-4746) is vacuous.  What is proved is the *finite
specialisation* of the paper's δ-quotient.

**Partial correctness only.**  `iter` collects finite `Runs`; a divergent body denotes ∅
(`iter_forever`).  This is the `𝒫` variant, not the `𝒫⁺` variant the paper uses for PO/TSO
(L4690-4692), and the `f^∞` branch (L4685-4687) is absent.  Nonemptiness must **not** be
added to the carrier: a body that always recurses has no finite run, so a nonemptiness field
makes `Iterate` unfillable (`not_drainable_iter`).  This is a theorem-level constraint, not a
preference.  The concrete entry point for a future divergence branch is a stream-action
module for `Colist`, where the law `Σσ = σ₀ · Σᵢσᵢ₊₁` (L4647-4648) is provable.

**No fork-join parallel composition of morphisms** (L4790-4804, L4868-4880).  `lpar` and the
`Pom.par` laws are proved, and `Pom.mk_seq_ne_mk_par` witnesses that the quotient
distinguishes ordered from concurrent, but nothing here says anything about *concurrent
behaviour*: every claim is about a single thread's emitted pomsets.  The two-thread
store-buffering litmus is not proved; only the single-thread mechanism behind it
(`write_stays_buffered`, `write_fence_drained`).

**What the pomset layer does and does not buy.**  By `PrePom.ofList_deq_iff` the emitted
effects of the operations lie in the linear `δ`-free fragment, on which `Pom` *is* the free
monoid — so within the monad's image this is observationally a trace model.  By
`Pom.mk_seq_ne_mk_par`, `Pom` is strictly richer outside that image.  Both halves hold; the
first must not be sold as the second.

**No validity post-filter.**  Reads emit an arbitrary value on a buffer miss (faithful to
L4845, see `read_admits_any_value`) and no global memory is threaded, so nothing here proves
TSO-correctness of an execution; L4781-4788 is not formalised.

**`PTSO` is the generic envelope only.**  `Ide(𝒞,d)` is a genuine `Category` and `PTSO` is
constructed, but the inheritance chain of L4940-5006 (coproducts, Elgot, premonoidal,
distributive, Freyd) is not — the paper asserts these for `d = pflush` without a displayed
proof.  So this does **not** establish that `PTSO` is an SSA model.

**Paper errata, recorded not repaired.**
* E1: L4823-4825's `TSO = StateT Buf (Trace Σ)` must read `Traces Σ`, since
  `Trace Σ = TraceT Σ Id` is deterministic and cannot carry the set-valued denotations at
  L4845/L4853 or the hom-sets `Set_TSO(A,B)` at L4854.
* E2: L4848's `W_x^TSO` returns `v` where `write_x : ℐ₀^∅(Word, 𝟏)` at L4773 demands `()`.
* E3: L4848 emits the global write `x := v` at write time while simultaneously buffering it,
  coherent only under the post-filter reading.

**A `Quotient` of abstract carriers is foreclosed by design.**  An abstract-carrier pomset
structure sits at `Type (u+1)` and cannot be the effect type of a `Type u → Type u` monad;
the `Fin`-indexed carrier is what keeps everything at `Type u` with no `ULift` and no edit to
`Isotope/Elgot/Basic.lean`.  If infinite carriers are ever needed, the migration path is a
countable skeleton (carrier `Set ℕ`, order and label on `ℕ`), which is `Small.{0}`.

**Relation to `formalization/CLAIM_AUDIT.md`.**  The audit row "SPARC TSO forms a valid SSA
model" stays **contradicted**.  It concerns the paper's full construction — infinite pomsets,
the divergence branch, and the `Ide`/`PTSO` inheritance chain that would make it an SSA model
— none of which this development discharges.  What is added is a separate, strictly narrower
claim, listed under "What is proved" above.
-/
