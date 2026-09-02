import Isotope.Elgot.Par.Basic
import Isotope.Pomset

/-!
# The pomset parallel operator against the uniform interface

`Isotope.Pomset.Pom.par` is a commutative monoid on the nose: `par_assoc`, `par_comm` and
`par_one` are already proved in `Isotope/Pomset/Quotient.lean`.  This module records that as
a `ParMonoid` instance, and proves the one law that separates it from the interleaving
operators.

## The interchange law fails for pomsets

Brookes-style parallel composition satisfies the interchange law with sequencing, as an
inequality: `(x ∥ y) ; (f ∥ g) ≤ (x ; f) ∥ (y ; g)` (`Isotope/Elgot/Par/Brookes.lean`).  For
pomsets there is no inequality to hide behind — `Pom` carries no refinement order in this
development — and the corresponding *equation* is false: `pom_exchange_fails` exhibits
`(1 ; a) ∥ (b ; 1) = a ∥ b` against `(1 ∥ b) ; (a ∥ 1) = b ; a`, which differ by
`Pom.mk_seq_ne_mk_par`.

This is the precise sense in which the two kinds of parallel composition are different
mathematical objects rather than two presentations of one: the interleaving operators trade
in *sets* of linear orders, where a sequenced interleaving is one of the concurrent ones,
while the pomset operator trades in a single partial order, where sequencing genuinely adds
edges.  A refinement order on `Pom` would be what restores the law; the paper has one and
this development does not (`Isotope/Pomset/Quotient.lean`, honest boundary).
-/

universe u

namespace Isotope.Elgot.Par

open Isotope.Pomset

variable {A : Type u} [Tick A]

/-- **Pomsets under `∥` are a commutative monoid**, on the nose: the laws of
`Isotope/Pomset/Quotient.lean` are exactly the `ParMonoid` fields. -/
instance instParMonoidPom : ParMonoid (Pom A) where
  par := Pom.par
  unit := 1
  par_assoc := Pom.par_assoc
  par_comm := Pom.par_comm
  par_unit := Pom.par_one

@[simp] theorem parMonoid_par_pom (p q : Pom A) : ParMonoid.par p q = Pom.par p q := rfl

@[simp] theorem parMonoid_unit_pom : (ParMonoid.unit : Pom A) = 1 := rfl

/-- **The interchange law fails for the pomset parallel operator.**  With `x = 1`, `y = a`,
`z = b`, `w = 1` the two sides are `a ∥ b` and `b ; a`, and sequencing a pomset is not
shuffling it. -/
theorem pom_exchange_fails {a b : A} (ha : a ≠ tick) (hb : b ≠ tick) :
    ∃ x y z w : Pom A,
      Pom.par (x * y) (z * w) ≠ Pom.par x z * Pom.par y w := by
  refine ⟨1, Pom.mk (PrePom.single a), Pom.mk (PrePom.single b), 1, ?_⟩
  rw [one_mul, mul_one, Pom.one_par, Pom.par_one]
  intro h
  exact Pom.mk_seq_ne_mk_par hb ha (by rw [← h, Pom.par_comm])

end Isotope.Elgot.Par
