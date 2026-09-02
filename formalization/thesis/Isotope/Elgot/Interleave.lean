import Mathlib.Data.List.Basic

/-!
# Shuffling two lists

`Interleave t u w` says that `w` is a merge of `t` and `u` preserving the order
of each: the standard three-place *shuffle* relation on lists.  Mathlib has no
such relation (its `Interleave` is `Stream'.interleave`), so this is the only
one in reach.

The relation was introduced in `Isotope/Elgot/Brookes/TSO/Interleaving.lean` for
Brookes-style parallel composition and is hoisted here because the
release/acquire development of `Isotope/Elgot/RA/Parallel.lean` needs exactly
the same notion, at the type of *transitions* rather than of Brookes steps.  It
is a three-constructor relation on lists with no dependence on either
development, so sharing it is the kind of "genuinely stable component" that
`AGENTS.md` sanctions.

Nothing here is specific to any paper: the shuffle relation and the four
structural lemmas (`swap`, `appendCompat`, `splitLeft`, `splitRight`) are
standard.  `splitLeft`/`splitRight` are the combinatorial content behind the
`St` and `Mu` cases of Dvir–Kammar–Lahav's Deferral of Closure for `∥∥∥`
(TOPLAS 47(2):7, journal p.49), which decompose a shuffle around a distinguished
transition of one operand.
-/

universe u

namespace Isotope.Elgot

variable {E : Type u}

/-- `Interleave t u w`: the list `w` is a merge of `t` and `u` that preserves
the order of each. -/
inductive Interleave : List E → List E → List E → Prop
  | /-- Two exhausted lists interleave to nothing. -/
    nil : Interleave [] [] []
  | /-- The next element of the merge is the left list's. -/
    left {e : E} {t u w : List E} : Interleave t u w → Interleave (e :: t) u (e :: w)
  | /-- The next element of the merge is the right list's. -/
    right {e : E} {t u w : List E} : Interleave t u w → Interleave t (e :: u) (e :: w)

namespace Interleave

/-- Interleaving is symmetric. -/
theorem swap {t u w : List E} (h : Interleave t u w) : Interleave u t w := by
  induction h with
  | nil => exact .nil
  | left _ ih => exact .right ih
  | right _ ih => exact .left ih

/-- A list interleaved with the empty list is itself. -/
theorem nil_right (t : List E) : Interleave t [] t := by
  induction t with
  | nil => exact .nil
  | cons e t ih => exact .left ih

/-- A list interleaved with the empty list is itself. -/
theorem nil_left (t : List E) : Interleave [] t t := (nil_right t).swap

/-- A merge has the combined length of its two operands. -/
theorem length_eq {t u w : List E} (h : Interleave t u w) :
    w.length = t.length + u.length := by
  induction h with
  | nil => rfl
  | left _ ih => simp only [List.length_cons, ih]; omega
  | right _ ih => simp only [List.length_cons, ih]; omega

/-- The merge of two lists, one of which is non-empty, is non-empty. -/
theorem ne_nil_left {t u w : List E} (h : Interleave t u w) (ht : t ≠ []) : w ≠ [] := by
  intro hw
  subst hw
  have := h.length_eq
  simp only [List.length_nil] at this
  exact ht (List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_add_eq_zero_right this.symm))

/-- The merge of two lists, one of which is non-empty, is non-empty. -/
theorem ne_nil_right {t u w : List E} (h : Interleave t u w) (hu : u ≠ []) : w ≠ [] :=
  h.swap.ne_nil_left hu

/-- The elements of a merge are exactly the elements of its two operands. -/
theorem mem_iff {t u w : List E} (h : Interleave t u w) {x : E} :
    x ∈ w ↔ x ∈ t ∨ x ∈ u := by
  induction h with
  | nil => simp
  | left _ ih => simp only [List.mem_cons, ih]; tauto
  | right _ ih => simp only [List.mem_cons, ih]; tauto

/-- Every element of the left operand occurs in the merge. -/
theorem mem_of_left {t u w : List E} (h : Interleave t u w) {x : E} (hx : x ∈ t) :
    x ∈ w := h.mem_iff.mpr (Or.inl hx)

/-- Every element of the right operand occurs in the merge. -/
theorem mem_of_right {t u w : List E} (h : Interleave t u w) {x : E} (hx : x ∈ u) :
    x ∈ w := h.mem_iff.mpr (Or.inr hx)

/-- Every element of the merge comes from one of the two operands. -/
theorem mem_or {t u w : List E} (h : Interleave t u w) {x : E} (hx : x ∈ w) :
    x ∈ t ∨ x ∈ u := h.mem_iff.mp hx

/-- Shuffles concatenate: merging prefixes and merging suffixes merges the
concatenations. -/
theorem appendCompat {a₁ a₂ a b₁ b₂ b : List E} (ha : Interleave a₁ a₂ a)
    (hb : Interleave b₁ b₂ b) : Interleave (a₁ ++ b₁) (a₂ ++ b₂) (a ++ b) := by
  induction ha with
  | nil => simpa using hb
  | left _ ih => exact ih.left
  | right _ ih => exact ih.right

/-- Running the left list to completion and then the right one is a shuffle. -/
theorem append (t u : List E) : Interleave t u (t ++ u) := by
  simpa using (nil_right t).appendCompat (nil_left u)

/-- A shuffle whose left operand is split splits: the right operand and the
merge split compatibly.  This is the decomposition the `St` and `Mu` cases of
Deferral of Closure perform on a parallel composition. -/
theorem splitLeft {x l₂ l : List E} (h : Interleave x l₂ l) :
    ∀ a₁ b₁ : List E, x = a₁ ++ b₁ →
      ∃ a₂ b₂ a b : List E, l₂ = a₂ ++ b₂ ∧ l = a ++ b ∧
        Interleave a₁ a₂ a ∧ Interleave b₁ b₂ b := by
  induction h with
  | nil =>
      intro a₁ b₁ hx
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hx.symm
      exact ⟨[], [], [], [], rfl, rfl, .nil, .nil⟩
  | @left e t u w h ih =>
      intro a₁ b₁ hx
      cases a₁ with
      | nil =>
          simp only [List.nil_append] at hx
          subst hx
          exact ⟨[], u, [], e :: w, rfl, rfl, .nil, h.left⟩
      | cons f a₁ =>
          simp only [List.cons_append, List.cons.injEq] at hx
          obtain ⟨rfl, hx⟩ := hx
          obtain ⟨a₂, b₂, a, b, h₂, hw, hia, hib⟩ := ih a₁ b₁ hx
          exact ⟨a₂, b₂, e :: a, b, h₂, by rw [hw]; rfl, hia.left, hib⟩
  | @right e t u w h ih =>
      intro a₁ b₁ hx
      obtain ⟨a₂, b₂, a, b, h₂, hw, hia, hib⟩ := ih a₁ b₁ hx
      exact ⟨e :: a₂, b₂, e :: a, b, by rw [h₂]; rfl, by rw [hw]; rfl, hia.right, hib⟩

/-- A shuffle whose right operand is split splits. -/
theorem splitRight {l₁ x l : List E} (h : Interleave l₁ x l) :
    ∀ a₂ b₂ : List E, x = a₂ ++ b₂ →
      ∃ a₁ b₁ a b : List E, l₁ = a₁ ++ b₁ ∧ l = a ++ b ∧
        Interleave a₁ a₂ a ∧ Interleave b₁ b₂ b := by
  intro a₂ b₂ hx
  obtain ⟨a₁, b₁, a, b, h₁, hl, hia, hib⟩ := h.swap.splitLeft a₂ b₂ hx
  exact ⟨a₁, b₁, a, b, h₁, hl, hia.swap, hib.swap⟩

end Interleave

end Isotope.Elgot
