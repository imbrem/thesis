import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Isotope.SExp.Defs

namespace Isotope

namespace SExp

variable {A}

@[simp]
def size : SExp A → ℕ
  | .atom _ => 1
  | .par es => 1 + (∑ i, (es i).size)

@[simp]
theorem size_parL (es : List (SExp A)) : size (parL es) = 1 + (size <$> es).sum := by
  simp [parL]

@[simp]
def atoms : SExp A → ℕ
  | .atom _ => 1
  | .par es => (∑ i, (es i).atoms)

@[simp]
theorem atoms_parL (es : List (SExp A)) : atoms (parL es) = (atoms <$> es).sum := by
  simp [parL]

@[simp]
theorem atoms_le_size (e : SExp A) : e.atoms ≤ e.size := by
  induction e with
  | atom _ => rfl
  | par es ih =>
    simp only [atoms, size]
    apply Nat.le_add_left_of_le
    apply Finset.sum_le_sum
    simp [ih]

@[simp]
def flatten : SExp A → List A
  | .atom a => [a]
  | .par es => List.finRange _ >>= (fun i => (es i).flatten)

-- @[simp]
-- theorem flatten_parL (es : List (SExp A)) : flatten (parL es) = es >>= flatten := by
--   simp only [parL, flatten]
--   have h : (fun i : Fin es.length => (es.get i).flatten) = flatten ∘ (fun i => es.get i) := rfl
--   rw [h]
--   clear h
--   sorry

@[simp]
def flatten_length (e : SExp A) : e.flatten.length = e.atoms := by
  induction e with
  | atom _ => simp
  | par es ih =>
    simp only [flatten, List.finRange, List.bind_eq_flatMap, List.length_flatMap, ih, List.map_ofFn,
      atoms, Finset.sum, Fin.univ_val_map, Multiset.sum_coe]
    rfl

@[simp]
def depth : SExp A → ℕ
  | .atom _ => 0
  | .par es => 1 + (Finset.sup Finset.univ (fun i => (es i).depth))

@[simp]
theorem depth_le_size (e : SExp A) : e.depth ≤ e.size := by
  induction e with
  | atom _ => simp
  | par es ih =>
    simp only [depth, size]
    apply Nat.add_le_add_left
    apply Finset.sup_le
    simp only [Finset.mem_univ, forall_const]
    intro i
    have h := Finset.single_le_sum (a := i) (f := (fun i => (es i).size)) (s := Finset.univ)
      (by simp) (by simp)
    exact le_trans (ih i) h

@[simp]
def minDepth : SExp A → ℕ
  | .atom _ | .par (length := 0) _ => 0
  | .par (length := n + 1) es => 1 + (Finset.inf' Finset.univ (by simp) (fun i => (es i).minDepth))

@[simp]
theorem minDepth_le_depth (e : SExp A) : e.minDepth ≤ e.depth := by
  induction e with
  | atom _ => simp
  | par es ih =>
    rename_i length
    cases length with
    | zero => simp
    | succ n =>
      simp only [minDepth, depth]
      simp only [add_le_add_iff_left, Finset.inf'_le_iff, Finset.mem_univ, true_and]
      exists 0
      if h : 0 < (es 0).minDepth then
        rw [Finset.le_sup_iff h]
        simp only [Finset.mem_univ, true_and]
        exists 0
        apply ih
      else
        omega

@[simp]
theorem minDepth_le_size (e : SExp A) : e.minDepth ≤ e.size
  := le_trans e.minDepth_le_depth e.depth_le_size

end SExp

end Isotope
