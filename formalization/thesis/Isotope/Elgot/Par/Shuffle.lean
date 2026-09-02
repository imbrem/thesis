import Isotope.Elgot.Interleave

/-!
# Three-way shuffles

The associativity of the list-shuffle relation `Isotope.Elgot.Interleave`, plus the two
inversion lemmas for a shuffle with an empty operand.  These are the combinatorial half of
associativity for *every* interleaving-style parallel composition in this development:
Brookes-style `par` (`Isotope/Elgot/Par/Brookes.lean`), the store-buffer TSO `par` built on
it, and the release/acquire `∥∥∥` of `Isotope/Elgot/RA/Parallel.lean`
(`Isotope/Elgot/Par/RA.lean`).

Nothing here is from any paper: the shuffle relation is standard and so are these lemmas.
They live in their own namespace `Isotope.Elgot.Par.Shuffle` rather than being added to
`Interleave` itself, so that this file can be merged independently of concurrent work on
`Isotope/Elgot/Interleave.lean`.
-/

universe u

namespace Isotope.Elgot.Par

open Isotope.Elgot (Interleave)

namespace Shuffle

variable {E : Type u}

/-- A shuffle with an empty right operand is the left operand. -/
theorem eq_of_nil_right {t w : List E} (h : Interleave t [] w) : w = t := by
  induction t generalizing w with
  | nil => cases h with | nil => rfl
  | cons e t ih =>
      cases h with
      | left h' => rw [ih h']
/-- A shuffle with an empty left operand is the right operand. -/
theorem eq_of_nil_left {u w : List E} (h : Interleave [] u w) : w = u :=
  eq_of_nil_right h.swap

/-- A shuffle whose right operand is a single event splits around that event. -/
theorem single_right : ∀ {t w : List E} {e : E}, Interleave t [e] w →
    ∃ a b, t = a ++ b ∧ w = a ++ e :: b := by
  intro t
  induction t with
  | nil =>
      intro w e h
      cases h with
      | right h' => cases h'; exact ⟨[], [], rfl, rfl⟩
  | cons f t ih =>
      intro w e h
      cases h with
      | left h' =>
          obtain ⟨a, b, rfl, rfl⟩ := ih h'
          exact ⟨f :: a, b, rfl, rfl⟩
      | right h' =>
          rw [eq_of_nil_right h']
          exact ⟨[], f :: t, rfl, rfl⟩

/-- **Shuffling is associative, left to right.**  A shuffle of a shuffle regroups: if `ab`
merges `a` and `b`, and `w` merges `ab` with `c`, then some `bc` merges `b` and `c` and `w`
merges `a` with it. -/
theorem assoc : ∀ {ab c w : List E}, Interleave ab c w → ∀ {a b : List E},
    Interleave a b ab → ∃ bc, Interleave b c bc ∧ Interleave a bc w := by
  intro ab c w h₂
  induction h₂ with
  | nil =>
      intro a b h₁
      cases h₁
      exact ⟨[], .nil, .nil⟩
  | @left e ab' c w' _ ih =>
      intro a b h₁
      cases h₁ with
      | @left _ a' _ _ h₁' =>
          obtain ⟨bc, hbc, haw⟩ := ih h₁'
          exact ⟨bc, hbc, haw.left⟩
      | @right _ _ b' _ h₁' =>
          obtain ⟨bc, hbc, haw⟩ := ih h₁'
          exact ⟨e :: bc, hbc.left, haw.right⟩
  | @right e ab' c' w' _ ih =>
      intro a b h₁
      obtain ⟨bc, hbc, haw⟩ := ih h₁
      exact ⟨e :: bc, hbc.right, haw.right⟩

/-- **Shuffling is associative, right to left.**  The converse regrouping of `assoc`. -/
theorem assoc' {a b c bc w : List E} (h₁ : Interleave b c bc) (h₂ : Interleave a bc w) :
    ∃ ab, Interleave a b ab ∧ Interleave ab c w := by
  obtain ⟨m, hm, hw⟩ := assoc h₂.swap h₁.swap
  exact ⟨m, hm.swap, hw.swap⟩

end Shuffle

end Isotope.Elgot.Par
