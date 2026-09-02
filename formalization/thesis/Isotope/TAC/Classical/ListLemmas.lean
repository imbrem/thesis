import Isotope.TAC.Classical.WellFormed

namespace Isotope.TAC.Classical

universe u v w
variable {Var : Type u} {Op : Type v} {Label : Type w}

theorem mem_take_flatMap_defs_iff {v : Var} {xs : List (Instr Var Op)} {i : Nat} :
    v ∈ (xs.take i).flatMap Instr.defs ↔
      ∃ j, ∃ hj : j < xs.length, j < i ∧ v ∈ Instr.defs xs[j] := by
  constructor
  · intro h
    rw [List.mem_flatMap] at h
    rcases h with ⟨x, hx, hv⟩
    rw [List.mem_iff_getElem] at hx
    rcases hx with ⟨j, hj, rfl⟩
    have hmin : j < min i xs.length := by simpa using hj
    have hji : j < i := (Nat.lt_min.mp hmin).1
    have hjx : j < xs.length := (Nat.lt_min.mp hmin).2
    refine ⟨j, hjx, hji, ?_⟩
    simpa using hv
  · rintro ⟨j, hj, hji, hv⟩
    rw [List.mem_flatMap]
    refine ⟨xs[j], ?_, hv⟩
    rw [List.mem_iff_getElem]
    refine ⟨j, ?_, ?_⟩
    · simpa using (Nat.lt_min.mpr ⟨hji, hj⟩)
    · simp

theorem mem_take_flatMap_defs {v : Var} {xs : List (Instr Var Op)} {i : Nat}
    (h : v ∈ (xs.take i).flatMap Instr.defs) :
    ∃ j, ∃ hj : j < xs.length, j < i ∧ v ∈ Instr.defs xs[j] :=
  mem_take_flatMap_defs_iff.mp h

end Isotope.TAC.Classical
