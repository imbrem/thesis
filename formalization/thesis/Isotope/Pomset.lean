import Isotope.Pomset.Basic
import Isotope.Pomset.PrePom
import Isotope.Pomset.Delta
import Isotope.Pomset.Quotient
import Isotope.Pomset.Linear

/-!
# Finite pomsets

Kavanagh and Brookes' pomsets, in the finite fragment, as used by the SPARC TSO model of
*The Denotational Semantics of SSA*.

* `LPoset` / `LIso` — labelled posets and their isomorphisms.
* `PrePom` — presentations with carrier `Fin card`; finiteness is structural.
* `DIso` — the `δ`-quotient, stated as an isomorphism of *live* subcarriers.
* `Pom` — pomsets, with `Monoid (Pom A)` the paper's concatenation monoid and `Pom.par` the
  parallel monoid (unbundled, since a type carries one `Monoid` instance).
* `PrePom.ofList` — linear pomsets, with `ofList_deq_iff` (faithfulness on the `δ`-free
  fragment) and `Pom.mk_seq_ne_mk_par` (the quotient is not the free monoid).

## Honest boundary

**Finite pomsets only.**  `PrePom`'s carrier is `Fin card` by construction.  The paper's
infinite pomsets, its sum `Σ_n α_n` over an arbitrary index poset, and the stream action
`Σ : Pom_fin^ω → Pom` are not representable here and are not attempted.  Consequently the
paper's `trim` is the identity in this fragment, and its side condition that infinite
carriers are equated only to other infinite ones is vacuous.  What is proved is therefore
the *finite specialisation* of the paper's δ-quotient.

**A quotient of abstract carriers is foreclosed by design.**  A `PomStruct` with an
abstract carrier would sit at `Type (u+1)` and could not be the effect type of a
`Type u → Type u` monad; the `Fin`-indexed carrier is what keeps everything at `Type u`
with no `ULift`.  If infinite carriers are ever wanted, the migration path is a *countable
skeleton* (carrier a `Set ℕ`, order and label on `ℕ`), which is `Small.{0}` and preserves
the universe fit.  Recorded so the expensive route is not re-attempted.

**No order-theoretic refinement.**  The paper's refinement/augmentation order on pomsets is
not formalised; only equality in the quotient is.
-/
