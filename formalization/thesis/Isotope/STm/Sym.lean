import Mathlib.Data.Set.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Lattice.Basic

import Isotope.STm.Defs

namespace Isotope

universe uargs uix uval uop ua

open Args

namespace STm

variable {Arity : Type uargs} [instArgs : Args Arity]
         {L : Lang Arity} {A : Type ua}

def use : STm L A -> Set A
  | .sym a => {a}
  | .const _ => ∅
  | .op (arity := arity) _ es => ⋃ i ∈ posFinset arity, use (es i)

@[simp]
theorem use_sym (a : A) : use (.sym a : STm L A) = {a} := rfl

theorem mem_use_sym_iff {a b : A} : a ∈ (.sym b : STm L A).use ↔ a = b := by simp

@[simp]
theorem use_const (c : L.Val) : use (.const c : STm L A) = ∅ := rfl

theorem not_mem_use_const {a : A} {c : L.Val} : a ∉ (.const c : STm L A).use := by simp

theorem use_op {arity} (o : L.Op arity) (es : Ix arity → STm L A) :
  use (.op o es : STm L A) = ⋃ i ∈ posFinset arity, use (es i) := rfl

@[simp]
theorem mem_use_op_iff {a : A} {arity} (o : L.Op arity) (es : Ix arity → STm L A) :
  a ∈ (.op o es : STm L A).use ↔ ∃ i ∈ posFinset arity, a ∈ (es i).use := by simp [use_op]

def subtrees : STm L A -> Set (STm L A)
  | .sym a => {.sym a}
  | .const c => {.const c}
  | .op (arity := arity) o es
    => {(.op o es)} ∪ ⋃ i ∈ posFinset arity, subtrees (es i)

@[simp]
theorem subtrees_sym (a : A) : subtrees (.sym a : STm L A) = {.sym a} := rfl

theorem mem_subtrees_sym_iff {e a} : e ∈ (.sym a : STm L A).subtrees ↔ e = .sym a
  := by simp

@[simp]
theorem subtrees_const (c : L.Val) : subtrees (.const c : STm L A) = {.const c} := rfl

theorem mem_subtrees_const_iff {e c} : e ∈ (.const c : STm L A).subtrees ↔ e = .const c
  := by simp

theorem subtrees_op {arity} (o : L.Op arity) (es : Ix arity → STm L A) :
  subtrees (.op o es : STm L A) = {(.op o es)} ∪ ⋃ i ∈ posFinset arity, subtrees (es i) := rfl

theorem mem_subtrees_op_iff {e arity} (o : L.Op arity) (es : Ix arity → STm L A) :
  e ∈ (.op o es : STm L A).subtrees ↔ e = .op o es ∨ ∃ i ∈ posFinset arity, e ∈ (es i).subtrees
  := by simp [subtrees_op]

@[simp]
theorem mem_subtrees {e : STm L A} : e ∈ e.subtrees
  := by cases e <;> simp [subtrees_op, *]

theorem mem_subtrees_use_iff {a : A} {e : STm L A} : (∃ s ∈ e.subtrees, a ∈ s.use) ↔ a ∈ e.use
  := by induction e <;> simp [subtrees_op, use_op, *]; grind

@[simp]
theorem subtrees_use {e : STm L A} : (⋃ s ∈ e.subtrees, s.use) = e.use := by
  ext i; simp [mem_subtrees_use_iff]

def useL : STm L A -> List A
  | .sym a => [a]
  | .const _ => []
  | .op (arity := arity) _ es => (posList arity).flatMap (fun i => useL (es i))

@[simp]
theorem useL_sym (a : A) : useL (.sym a : STm L A) = [a] := rfl

@[simp]
theorem useL_const (c : L.Val) : useL (.const c : STm L A) = [] := rfl

theorem useL_op {arity} (o : L.Op arity) (es : Ix arity → STm L A) :
  useL (.op o es : STm L A) = (posList arity).flatMap (fun i => useL (es i)) := rfl

@[simp]
theorem mem_useL_iff {a} {e : STm L A} : a ∈ e.useL ↔ a ∈ e.use
  := by induction e <;> simp [useL_op, *]

theorem useL_toSet (e : STm L A) : {a | a ∈ e.useL} = e.use := by simp

section DecidableEq

variable [DecidableEq A]

def useF : STm L A -> Finset A
  | .sym a => {a}
  | .const _ => ∅
  | .op (arity := arity) _ es => (posFinset arity).biUnion (fun i => useF (es i))

@[simp]
theorem mem_useF_iff {a : A} {e : STm L A} : a ∈ e.useF ↔ a ∈ e.use
  := by induction e <;> simp [useF, *]

@[simp]
theorem useL_toFinset (e : STm L A) : e.useL.toFinset = e.useF := by
  ext i; simp

theorem useF_toSet (e : STm L A) : {a | a ∈ e.useF} = e.use := by simp

end DecidableEq

def subtreesL : STm L A -> List (STm L A)
  | .sym a => [.sym a]
  | .const c => [.const c]
  | .op (arity := arity) o es => (.op o es) :: (posList arity).flatMap (fun i => subtreesL (es i))

@[simp]
theorem subtreesL_sym {a} : subtreesL (.sym a : STm L A) = [.sym a] := rfl

@[simp]
theorem subtreesL_const {c} : subtreesL (.const c : STm L A) = [.const c] := rfl

theorem subtreesL_op {arity} (o : L.Op arity) (es : Ix arity → STm L A) :
  subtreesL (.op o es : STm L A)
    = (.op o es) :: (posList arity).flatMap (fun i => subtreesL (es i))
  := rfl

@[simp]
theorem mem_subtreesL_iff {s e : STm L A} : s ∈ e.subtreesL ↔ s ∈ e.subtrees
  := by induction e <;> simp [subtreesL_op, subtrees_op, *]

theorem subtreesL_toSet (e : STm L A) : {s | s ∈ e.subtreesL} = e.subtrees := by simp

section DecidableEq

variable [DecidableEq (STm L A)]

def subtreesF : STm L A -> Finset (STm L A)
  | .sym a => { .sym a }
  | .const c => { .const c }
  | .op (arity := arity) o es
    => {(.op o es)} ∪ (posFinset arity).biUnion (fun i => subtreesF (es i))

@[simp]
theorem subtreesF_sym {a} : subtreesF (.sym a : STm L A) = { .sym a } := rfl

@[simp]
theorem subtreesF_const {c} : subtreesF (.const c : STm L A) = { .const c } := rfl

theorem subtreesF_op {arity} (o : L.Op arity) (es : Ix arity → STm L A) :
  subtreesF (.op o es : STm L A)
    = {(.op o es)} ∪ (posFinset arity).biUnion (fun i => subtreesF (es i))
  := rfl

@[simp]
theorem mem_subtreesF_iff {s e : STm L A} : s ∈ e.subtreesF ↔ s ∈ e.subtrees
  := by induction e <;> simp [subtreesF_op, subtrees_op, *]

@[simp]
theorem subtreesL_toFinset (e : STm L A) : e.subtreesL.toFinset = e.subtreesF := by
  ext s; simp

theorem subtreesF_toSet (e : STm L A) : {s | s ∈ e.subtreesF} = e.subtrees := by simp

end DecidableEq

@[simp]
def children : STm L A -> List (STm L A)
  | .sym _ => []
  | .const _ => []
  | .op (arity := arity) _ es => (posList arity).map (fun i => es i)

def childrenS (e : STm L A) : Set (STm L A) := {c | c ∈ e.children}

@[simp]
theorem childrenS_sym (a : A) : childrenS (.sym a : STm L A) = ∅
  := by simp [childrenS]

@[simp]
theorem childrenS_const (c : L.Val) : childrenS (.const c : STm L A) = ∅
  := by simp [childrenS]

@[simp]
theorem childrenS_op {arity} (o : L.Op arity) (es : Ix arity → STm L A) :
  childrenS (.op o es : STm L A) = {es i | i ∈ posList arity} := by
  simp [childrenS, children]

@[simp]
theorem childrenS_subset_subtrees (e : STm L A) : e.childrenS ⊆ e.subtrees := by
  cases e with
  | op =>
    simp only [
      childrenS_op, mem_posList, subtrees_op, Set.singleton_union
    ]
    intro i h
    simp only [Set.mem_insert_iff, Set.mem_iUnion]
    right
    have ⟨w, h⟩ := h
    exists w
    simp [h]
  | _ => simp

def strictSubtrees : STm L A -> Set (STm L A)
  | .sym _ => ∅
  | .const _ => ∅
  | .op (arity := arity) _ es => ⋃ i ∈ posFinset arity, subtrees (es i)

@[simp]
theorem strictSubtrees_sym (a : A) : strictSubtrees (.sym a : STm L A) = ∅ := rfl

@[simp]
theorem strictSubtrees_const (c : L.Val) : strictSubtrees (.const c : STm L A) = ∅ := rfl

@[simp]
theorem strictSubtrees_subset_subtrees (e : STm L A) : e.strictSubtrees ⊆ e.subtrees := by
  cases e <;> simp [strictSubtrees, subtrees_op]

theorem strictSubtrees_eq_subtrees_children (e : STm L A)
  : e.strictSubtrees = (⋃ c ∈ e.children, c.subtrees) := by
  cases e <;> simp [children, strictSubtrees]

def depth : STm L A → ℕ
  | .sym _ => 0
  | .const _ => 0
  | .op (arity := arity) _ es => 1 + (posList arity).foldl (fun acc i => max acc (depth (es i))) 0

def size : STm L A → ℕ
  | .sym _ => 1
  | .const _ => 1
  | .op (arity := arity) _ es => 1 + (posList arity).foldl (fun acc i => acc + size (es i)) 0

end STm

end Isotope
