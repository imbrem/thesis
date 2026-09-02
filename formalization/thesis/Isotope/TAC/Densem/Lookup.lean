import Isotope.TAC.Densem.Phi
import Isotope.TAC.Classical.WellFormed

/-! # Agreement of executable and classical CFG lookup -/

namespace Isotope.TAC.Densem.Lookup

open Isotope.TAC.Classical

theorem phi_lookup_eq [DecidableEq κ]
    (g : Isotope.TAC.Classical.CFG ν φ κ) (label : κ) :
    Isotope.TAC.Densem.Phi.lookup g label = g.lookup (BlockId.named label) := by
  unfold Isotope.TAC.Densem.Phi.lookup Isotope.TAC.Classical.CFG.lookup
  induction g.blocks with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.find?_cons, List.lookup]
      split
      · rename_i h
        have e : p.1 = label := of_decide_eq_true h
        subst label
        simp
      · rename_i h
        have e : p.1 ≠ label := by
          intro e
          subst label
          simp at h
        have en : label ≠ p.1 := fun h => e h.symm
        cases hb : label == p.1
        · exact ih
        · exact (en (LawfulBEq.eq_of_beq hb)).elim

theorem mem_blocks_of_named_lookup [DecidableEq κ]
    (g : Isotope.TAC.Classical.CFG ν φ κ) {label : κ}
    {b : Isotope.TAC.Classical.Block ν φ κ}
    (h : g.lookup (BlockId.named label) = some b) : (label, b) ∈ g.blocks := by
  rw [← phi_lookup_eq g label] at h
  unfold Isotope.TAC.Densem.Phi.lookup at h
  rw [Option.map_eq_some_iff] at h
  rcases h with ⟨p, hp, hsnd⟩
  have hm := List.mem_of_find?_eq_some hp
  have hkey : p.1 = label := by
    have := List.find?_some hp
    simpa using this
  cases p
  simp only at hsnd hkey ⊢
  subst_vars
  exact hm

theorem label_mem_of_named_lookup [DecidableEq κ]
    (g : Isotope.TAC.Classical.CFG ν φ κ) {label : κ}
    {b : Isotope.TAC.Classical.Block ν φ κ}
    (h : g.lookup (BlockId.named label) = some b) :
      label ∈ Isotope.TAC.Classical.CFG.labels g := by
  unfold CFG.labels
  exact List.mem_map.mpr ⟨(label, b), mem_blocks_of_named_lookup g h, rfl⟩

end Isotope.TAC.Densem.Lookup
