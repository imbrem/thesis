import Isotope.Elgot.Brookes.Examples
import Isotope.Elgot.RA.Opt.StoreBuffering
import Isotope.Elgot.RA.Opt.Sequential

/-!
# Two store optimizations, and where they stop transferring

Two of the most elementary transformations of Dvir, Kammar and Lahav's Table 3
(`release-acquire`, TOPLAS 47(2):7, journal p.44), side by side:

| transformation | Brookes SC | RA, `𝔠`-model | RA, Abstract `A` |
|---|---|---|---|
| Write-Read Elimination `ℓ:=v ; ℓ? ↠ ℓ:=v ; v` | sound | **sound** | sound |
| Write-Write Elimination `ℓ:=v ; ℓ:=w ↠ ℓ:=w` | sound | **unsound** | sound, via `Absorb` |

Table 3's own labelling predicts exactly this split: the Write-Read row carries
**no** abstract-rule label, while Write-Write is written `ℓ:=w ; ℓ:=v ↠^Ab ℓ:=v`,
appealing to `Absorb`.

## The honest reading of the second row

This is **not** a separation of sequential consistency from release/acquire.
Dvir et al.'s *Abstract* model `A = 𝔤𝔠𝔞` — their actual semantics — validates
Write-Write Elimination; only the concrete side of the tower does not.  So the
row separates a *level of the release/acquire tower* from sequential
consistency, and must be stated that way.  The moral for the thesis: the Brookes
model of sequential consistency gets Write-Write Elimination for free, by a
single mumble, because its state keeps no intensional record of the superseded
write; release/acquire memories *do* keep such a record, as an extra message,
and a dedicated abstract closure rule has to be added to erase it.

## What is and is not proved here

* The unsoundness is proved for every rule set `R ⊆ 𝔠`, which includes the
  paper's `𝔠`-model but **not** its Concrete model `C = 𝔤𝔠`: the argument runs
  on `Refines.c_sub`, and `Loosen`, `Expel` and `Condense` replace messages in
  the closing memory, so `c_sub` fails for them.  Lifting the result to `C`
  would need a new `𝔤𝔠`-invariant and is not attempted.
* The soundness at the Abstract model is **not** proved here.  It is Prop. E.10
  of the paper, whose proof appeals to `Absorb`; the repository has the required
  `Absorb` rewrite only at one concrete instance
  (`RA.Abstract.absorb_two_writes`), not at the generality Prop. E.10 needs.
  The table row above records the paper's claim, not a theorem of this
  repository.
* The soundness of Write-Read Elimination in the concrete model *is* proved
  here, as `RA.store_pure_le_store_load` (`Isotope/Elgot/RA/Opt/Sequential.lean`).

## Direction

`P ≤ Q` is `P.traces ⊆ Q.traces` and validates the paper's `Q ↠ P`.
-/

namespace Isotope.Elgot.Opt

open Isotope.Elgot

/-! ## The release/acquire invariant: a store leaves its value behind -/

namespace RA

open Isotope.Elgot.RA

variable {Loc Val : Type} [DecidableEq Loc] {R : RuleSet}

/-- **Every trace of `⟦store ℓ,v⟧` closes on a memory containing a message of
value `v` at `ℓ`.**  True for every `R ⊆ 𝔠`: the generating trace's closing
memory contains the written message, and a `𝔠`-rewriting only grows the closing
memory (`Refines.c_sub`).

This fails for the `𝔤` rules, which replace messages in the closing memory —
`Loosen` weakens one, `Expel` splits one, `Condense` merges two and pulls
everything — which is why the unsoundness below is stated at `𝔠`. -/
theorem store_c_has_value (hR : R ⊆ cRules) (ℓ : Loc) (v : Val)
    {τ : PreTrace Loc Val Unit} (h : τ ∈ (store ℓ v : Comp R Loc Val Unit).traces) :
    ∃ ν ∈ τ.ch.c, ν.lc = ℓ ∧ ν.vl = v := by
  obtain ⟨τ₀, ⟨κ, μ, q, t, hqt, rfl, -⟩, hr⟩ := h
  exact ⟨writeMsg ℓ v q t κ hqt, hr.c_sub hR (Set.mem_insert _ _), rfl, rfl⟩

variable [Finite Loc] [Nonempty Loc]

/-- **Write-Write Elimination is unsound in the release/acquire `𝔠`-model.**
Concretely: over the paper's initial memory, in which every location holds `v₀`,
the single store `ℓ:=w` has a trace that is not a trace of `ℓ:=v ; ℓ:=w`,
provided the overwritten value `v` is neither `w` nor `v₀`.

The reason is that a release/acquire memory *keeps* the superseded write: every
trace of the composite closes on a memory containing a message of value `v` at
`ℓ`, whereas the witness closes on the initial memory plus one message of value
`w`.  No `𝔠`-rewriting can delete a message from the closing memory.

Contrast `Brookes.SeqCst.write_le_write_write`, which is the *same*
transformation under sequential consistency and holds by a single mumble; and
contrast the neighbouring row, Write-Read Elimination, which does transfer —
`RA.store_pure_le_store_load`. -/
theorem not_store_le_store_store (hR : R ⊆ cRules) (v₀ v w : Val) (t₀ : ℚ) (ℓ : Loc)
    (hvw : v ≠ w) (hvv₀ : v ≠ v₀) :
    ¬ ((store ℓ w : Comp R Loc Val Unit) ≤ (store ℓ v >>= fun _ ↦ store ℓ w)) := by
  intro hle
  have hmem : (⟨(fun _ ↦ t₀ : View Loc),
      Chro.single ⟨sbMem0 v₀ t₀, sbMem1 v₀ w t₀ ℓ⟩, sbView1 t₀ ℓ, ()⟩ :
        PreTrace Loc Val Unit) ∈ (store ℓ w : Comp R Loc Val Unit).traces :=
    sbStoreX_mem
  have hmem' := hle hmem
  rw [Comp.traces_bind] at hmem'
  obtain ⟨π₀, ⟨τ, υ, hs, hτ, hυ, -, rfl⟩, hr⟩ := hmem'
  obtain ⟨ν, hνc, hνlc, hνvl⟩ := store_c_has_value hR ℓ v hτ
  have hυt : IsTrace υ := (store ℓ w : Comp R Loc Val Unit).isTrace _ hυ
  have hπc : ν ∈ (τ.seam υ hs).ch.c := by
    rw [PreTrace.seam_ch, Chro.append_c]
    exact hυt.o_sub_c (hs hνc)
  have hfin : ν ∈ sbMem1 (Loc := Loc) v₀ w t₀ ℓ := hr.c_sub hR hπc
  rcases hfin with rfl | hfin
  · exact hvw (hνvl.symm.trans (storedMsg_vl t₀ ℓ w))
  · rw [sbMem0, mem_initialMem_iff] at hfin
    exact hvv₀ (hνvl.symm.trans (by rw [hfin]; rfl))

end RA

/-! ## The two rows, side by side -/

section Contrast

open Isotope.Elgot.RA

variable {Loc Val : Type} [DecidableEq Loc] [Finite Loc] [Nonempty Loc]

omit [Finite Loc] [Nonempty Loc] in
/-- **Write-Read Elimination transfers from sequential consistency to the
release/acquire concrete model.**  Both halves are `≤`, i.e. both models
validate `ℓ:=v ; ℓ? ↠ ℓ:=v ; v`.

The sequentially consistent half is `Brookes.SeqCst.write_pure_le_write_read`
(already in the repository); the release/acquire half is
`RA.store_pure_le_store_load`, proved at the Concrete model `C = 𝔤𝔠`.  Table 3
(journal p.44) lists this row with **no** abstract-rule label, which is exactly
what the two proofs show. -/
theorem write_read_elim_transfers (ℓ : Loc) (v : Val) :
    (Brookes.SeqCst.write ℓ v >>= fun _ ↦ (Pure.pure v : Brookes.SeqCst.Comp Loc Val Val))
        ≤ (Brookes.SeqCst.write ℓ v >>= fun _ ↦ Brookes.SeqCst.read ℓ)
      ∧ (store ℓ v >>= fun _ ↦ (Pure.pure v : Comp gcRules Loc Val Val))
        ≤ (store ℓ v >>= fun _ ↦ load ℓ) :=
  ⟨Brookes.SeqCst.write_pure_le_write_read ℓ v,
    RA.store_pure_le_store_load cRules_subset_gcRules gcRules_subset_gcTiAbRules ℓ v⟩

/-- **Write-Write Elimination does not.**  It is sound under sequential
consistency by a single mumble, and unsound in the release/acquire `𝔠`-model.

⚠ This separates a *level of the release/acquire tower* from sequential
consistency, **not** release/acquire from sequential consistency: the paper's
Abstract model `A` validates Write-Write Elimination, using the abstract rule
`Absorb` (Table 3, journal p.44, and Prop. E.10, p.60).  See the module
docstring. -/
theorem write_write_elim_fails_in_cRules (v₀ v w : Val) (t₀ : ℚ) (ℓ : Loc)
    (hvw : v ≠ w) (hvv₀ : v ≠ v₀) :
    (Brookes.SeqCst.write ℓ w
        ≤ (Brookes.SeqCst.write ℓ v >>= fun _ ↦ Brookes.SeqCst.write ℓ w))
      ∧ ¬ ((store ℓ w : Comp cRules Loc Val Unit) ≤ (store ℓ v >>= fun _ ↦ store ℓ w)) :=
  ⟨Brookes.SeqCst.write_le_write_write ℓ v w,
    RA.not_store_le_store_store (subset_refl _) v₀ v w t₀ ℓ hvw hvv₀⟩

end Contrast

end Isotope.Elgot.Opt
