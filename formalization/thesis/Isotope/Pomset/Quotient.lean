import Isotope.Pomset.Delta
import Mathlib.Algebra.Group.Defs

/-!
# Pomsets

`Pom A` is `PrePom A` modulo `δ`-isomorphism: the paper's `Pom_fin`.  Sequential
composition makes it a monoid with unit `⟦{δ}⟧ = ⟦∅⟧`; parallel composition makes it a
commutative monoid too, but since a type carries only one `Monoid` instance, `;` owns the
instance and `∥` is an unbundled function with named laws.

## Honest boundary

Finite pomsets only, and no order structure (the paper's refinement order on pomsets is not
formalised).  See `Isotope.Pomset.PrePom` for what finiteness excludes.
-/

universe u

namespace Isotope.Pomset

/-- A **finite pomset** over an alphabet `A` with null action `δ = tick`: a finite pomset
presentation up to `δ`-isomorphism.  This is the paper's `Pom_fin`. -/
def Pom (A : Type u) [Tick A] : Type u := Quotient (PrePom.instSetoid (A := A))

namespace Pom

variable {A : Type u} [Tick A]

/-- The pomset presented by a presentation. -/
def mk (p : PrePom A) : Pom A := Quotient.mk _ p

theorem mk_eq_mk {p q : PrePom A} : mk p = mk q ↔ p ≈ q := Quotient.eq

/-- The paper's concatenation monoid on finite pomsets, with unit `{δ}`. -/
instance instMonoid : Monoid (Pom A) where
  mul := Quotient.map₂ PrePom.seq (fun _ _ hp _ _ hq => PrePom.seq_congr hp hq)
  one := mk (PrePom.empty A)
  mul_assoc := by rintro ⟨p⟩ ⟨q⟩ ⟨r⟩; exact Quotient.sound (PrePom.seq_assoc p q r)
  one_mul := by rintro ⟨p⟩; exact Quotient.sound (PrePom.seq_unit_left p)
  mul_one := by rintro ⟨p⟩; exact Quotient.sound (PrePom.seq_unit_right p)

theorem mk_mul (p q : PrePom A) : mk p * mk q = mk (p.seq q) := rfl

theorem one_def : (1 : Pom A) = mk (PrePom.empty A) := rfl

/-- The paper's `{δ}` is the unit of the concatenation monoid. -/
theorem mk_single_tick : mk (PrePom.single (tick : A)) = 1 :=
  Quotient.sound PrePom.single_tick_equiv_empty

/-- Parallel composition `α ∥ β`, as an unbundled operation: `Pom A` carries only one
`Monoid` instance, and sequential composition owns it. -/
def par : Pom A → Pom A → Pom A :=
  Quotient.map₂ PrePom.par (fun _ _ hp _ _ hq => PrePom.par_congr hp hq)

theorem par_mk (p q : PrePom A) : par (mk p) (mk q) = mk (p.par q) := rfl

theorem par_assoc (a b c : Pom A) : par (par a b) c = par a (par b c) := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  induction c using Quotient.ind
  exact Quotient.sound (PrePom.par_assoc _ _ _)

theorem par_comm (a b : Pom A) : par a b = par b a := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  exact Quotient.sound (PrePom.par_comm _ _)

theorem par_one (a : Pom A) : par a 1 = a := by
  induction a using Quotient.ind
  exact Quotient.sound (PrePom.par_unit_right _)

theorem one_par (a : Pom A) : par 1 a = a := by rw [par_comm, par_one]

end Pom

end Isotope.Pomset
