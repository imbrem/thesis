import Isotope.Pomset.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite pomset presentations

A `PrePom A` is a labelled poset whose carrier is `Fin card`: finiteness is structural, and
the type lands in `Type u` whenever the alphabet does.  Pomsets proper are the quotient of
this type by `δ`-isomorphism (`Isotope.Pomset.Pom`).

## Honest boundary

Only *finite* pomsets are representable.  The paper's infinite pomsets, its sum
`Σ_n α_n` over an arbitrary index poset, and the stream action
`Σ : Pom_fin^ω → Pom` are not expressible here and are not attempted.  Consequently the
paper's `trim` is the identity in this fragment, and its side condition that infinite
carriers are equated only to infinite ones is vacuous.
-/

universe u

namespace Isotope.Pomset

/-- A **finite pomset presentation**: `card` events indexed by `Fin card`, labelled in `A`
and partially ordered. -/
structure PrePom (A : Type u) where
  /-- The number of events. -/
  card : ℕ
  /-- The labelled order on those events. -/
  toLPoset : LPoset A (Fin card)

namespace PrePom

variable {A : Type u}

/-- The empty presentation. -/
def empty (A : Type u) : PrePom A :=
  ⟨0, ⟨Fin.elim0, fun i _ => i.elim0, fun {i} => i.elim0, fun {i} => i.elim0, fun {i} => i.elim0⟩⟩

/-- The one-event presentation `{a}`.  At `a = δ` this is the paper's monoidal unit `{δ}`. -/
def single (a : A) : PrePom A :=
  ⟨1, ⟨fun _ => a, fun _ _ => True, fun _ => trivial, fun _ _ => trivial,
    fun _ _ => Subsingleton.elim _ _⟩⟩

/-- Sequential composition `α;β`: the lexicographic sum, reindexed onto `Fin (m + n)`. -/
def seq (p q : PrePom A) : PrePom A :=
  ⟨p.card + q.card, (p.toLPoset.lseq q.toLPoset).comap finSumFinEquiv.symm⟩

/-- Parallel composition `α ∥ β`: the disjoint sum, reindexed onto `Fin (m + n)`. -/
def par (p q : PrePom A) : PrePom A :=
  ⟨p.card + q.card, (p.toLPoset.lpar q.toLPoset).comap finSumFinEquiv.symm⟩

/-- The reindexing in `seq` is invisible up to isomorphism. -/
def seqLIso (p q : PrePom A) : LIso (p.seq q).toLPoset (p.toLPoset.lseq q.toLPoset) :=
  LIso.comap _ _

/-- The reindexing in `par` is invisible up to isomorphism. -/
def parLIso (p q : PrePom A) : LIso (p.par q).toLPoset (p.toLPoset.lpar q.toLPoset) :=
  LIso.comap _ _

end PrePom

end Isotope.Pomset
