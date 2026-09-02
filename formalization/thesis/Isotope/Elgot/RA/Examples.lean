import Isotope.Elgot.RA.Memory
import Isotope.Elgot.RA.Iteration
import Mathlib.Tactic.Linarith

/-!
# Worked examples: separating computations, and loops

The results here are proved theorems distinguishing genuinely different
computations, not stubs.  Two ingredients do the separating work:

* the returned value is a rewriting invariant (`Refines.ret_eq`), and
* the local messages `ξ.own` are a rewriting invariant (`Refines.own_eq`), so
  `return` — which has no local messages — is distinguishable from `store`.

For the memory examples we need one concrete well-formed memory with two
messages at the same location; `storedMem` is the paper's initial memory with a
single extra write.
-/

universe u

namespace Isotope.Elgot.RA

open Isotope.Elgot

variable {Loc Val : Type} {A B : Type u}

/-! ## `return` -/

theorem mem_pure_ret {r : A} {τ : PreTrace Loc Val A}
    (h : τ ∈ (pure r : Comp cRules Loc Val A).traces) : τ.ret = r := by
  obtain ⟨τ₀, ⟨κ, μ, -, -, rfl⟩, hr⟩ := h
  exact hr.ret_eq.symm

theorem mem_pure_own {r : A} {τ : PreTrace Loc Val A}
    (h : τ ∈ (pure r : Comp cRules Loc Val A).traces) : τ.ch.own = ∅ := by
  obtain ⟨τ₀, hτ₀, hr⟩ := h
  obtain ⟨κ, μ, hwf, hpd, rfl⟩ := hτ₀
  rw [← hr.own_eq (subset_refl _) (pureGen_isTrace r _ ⟨κ, μ, hwf, hpd, rfl⟩)]
  simp [Transition.own]

/-- `return r` is non-empty: it contains the trace built from the paper's
initial memory. -/
theorem pure_nonempty [Finite Loc] [Nonempty Loc] (v₀ : Val) (t₀ : ℚ) (r : A) :
    (⟨(fun _ ↦ t₀ : View Loc), Chro.single ⟨initialMem v₀ t₀, initialMem v₀ t₀⟩,
      (fun _ ↦ t₀), r⟩ : PreTrace Loc Val A) ∈ (pure r : Comp cRules Loc Val A).traces :=
  subset_closure ⟨_, _, initialMem_wellFormed v₀ t₀, pointsDownInto_initialMem v₀ t₀, rfl⟩

theorem pure_ne_pure [Finite Loc] [Nonempty Loc] (v₀ : Val) (t₀ : ℚ) {r s : A}
    (h : r ≠ s) : (pure r : Comp cRules Loc Val A) ≠ pure s := by
  intro hrs
  exact h (((mem_pure_ret (pure_nonempty v₀ t₀ r)).symm.trans
    (mem_pure_ret (hrs ▸ pure_nonempty (Loc := Loc) v₀ t₀ r))))

theorem bot_ne_pure [Finite Loc] [Nonempty Loc] (v₀ : Val) (t₀ : ℚ) (r : A) :
    (⊥ : Comp cRules Loc Val A) ≠ pure r := by
  intro h
  have := pure_nonempty (Loc := Loc) (Val := Val) v₀ t₀ r
  rw [← h] at this
  exact absurd this (by simp)

/-! ## A memory with two messages at one location -/

section Store

variable [DecidableEq Loc]

/-- The message a `store` of `v` at `ℓ` adds to the initial memory: value `v`
on the segment `[t₀, t₀+1)`, carrying the initial view advanced at `ℓ`. -/
def storedMsg (t₀ : ℚ) (ℓ : Loc) (v : Val) : Msg Loc Val :=
  writeMsg ℓ v t₀ (t₀ + 1) (fun _ ↦ t₀) (by linarith)

/-- The paper's initial memory with one extra write at `ℓ`. -/
def storedMem (v₀ : Val) (t₀ : ℚ) (ℓ : Loc) (v : Val) : Memory Loc Val :=
  insert (storedMsg t₀ ℓ v) (initialMem v₀ t₀)

@[simp] theorem storedMsg_lc (t₀ : ℚ) (ℓ : Loc) (v : Val) :
    (storedMsg (Val := Val) t₀ ℓ v).lc = ℓ := rfl

@[simp] theorem storedMsg_vl (t₀ : ℚ) (ℓ : Loc) (v : Val) :
    (storedMsg (Loc := Loc) t₀ ℓ v).vl = v := rfl

@[simp] theorem storedMsg_i (t₀ : ℚ) (ℓ : Loc) (v : Val) :
    (storedMsg (Loc := Loc) t₀ ℓ v).i = t₀ := rfl

@[simp] theorem storedMsg_vw (t₀ : ℚ) (ℓ : Loc) (v : Val) :
    (storedMsg (Loc := Loc) t₀ ℓ v).vw = setView (fun _ ↦ t₀) ℓ (t₀ + 1) := rfl

@[simp] theorem storedMsg_t (t₀ : ℚ) (ℓ : Loc) (v : Val) :
    (storedMsg (Loc := Loc) t₀ ℓ v).t = t₀ + 1 := by simp [Msg.t]

theorem storedMsg_not_mem_initialMem (v₀ : Val) (t₀ : ℚ) (ℓ : Loc) (v : Val) :
    storedMsg t₀ ℓ v ∉ initialMem (Loc := Loc) v₀ t₀ := by
  intro h
  rw [mem_initialMem_iff] at h
  have hi := congrArg Msg.i h
  simp only [storedMsg_i, initialMsg_i] at hi
  linarith

theorem initialMem_subset_storedMem (v₀ : Val) (t₀ : ℚ) (ℓ : Loc) (v : Val) :
    initialMem (Loc := Loc) v₀ t₀ ⊆ storedMem v₀ t₀ ℓ v := Set.subset_insert _ _

theorem storedMsg_mem (v₀ : Val) (t₀ : ℚ) (ℓ : Loc) (v : Val) :
    storedMsg t₀ ℓ v ∈ storedMem (Loc := Loc) v₀ t₀ ℓ v := Set.mem_insert _ _

theorem initialView_le_storedMsg_vw (t₀ : ℚ) (ℓ : Loc) (v : Val) :
    (fun _ ↦ t₀ : View Loc) ≤ (storedMsg (Loc := Loc) t₀ ℓ v).vw := by
  rw [storedMsg_vw]
  exact le_setView (by simp)

theorem storedMsg_pointsTo_self (t₀ : ℚ) (ℓ : Loc) (v : Val) :
    PointsTo (storedMsg (Loc := Loc) t₀ ℓ v).vw (storedMsg t₀ ℓ v) := by
  simp [PointsTo]

theorem storedMsg_pointsTo_initial {t₀ : ℚ} {ℓ ℓ' : Loc} (v₀ v : Val) (h : ℓ' ≠ ℓ) :
    PointsTo (storedMsg (Loc := Loc) t₀ ℓ v).vw (initialMsg v₀ t₀ ℓ') := by
  simp [PointsTo, setView_of_ne _ h]

variable [Finite Loc] [Nonempty Loc]

theorem storedMem_wellFormed (v₀ : Val) (t₀ : ℚ) (ℓ : Loc) (v : Val) :
    WellFormed (storedMem (Loc := Loc) v₀ t₀ ℓ v) := by
  have hinit := initialMem_wellFormed (Loc := Loc) v₀ t₀
  refine ⟨Set.Finite.insert _ hinit.finite, ⟨_, Set.mem_insert _ _⟩, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- scattered
    rintro ν hν ρ hρ hlc ⟨x, hx1, hx2⟩
    rcases hν with rfl | hν
    · rcases hρ with rfl | hρ
      · rfl
      · rw [mem_initialMem_iff] at hρ
        rw [hρ] at hx2
        simp only [Msg.seg, initialMsg_t, initialMsg_i, Set.mem_Ioc] at hx2
        simp only [Msg.seg, storedMsg_t, storedMsg_i, Set.mem_Ioc] at hx1
        linarith [hx1.1, hx2.2]
    · rcases hρ with rfl | hρ
      · rw [mem_initialMem_iff] at hν
        rw [hν] at hx1
        simp only [Msg.seg, initialMsg_t, initialMsg_i, Set.mem_Ioc] at hx1
        simp only [Msg.seg, storedMsg_t, storedMsg_i, Set.mem_Ioc] at hx2
        linarith [hx2.1, hx1.2]
      · exact hinit.scattered ν hν ρ hρ hlc ⟨x, hx1, hx2⟩
  · -- connected
    rintro ν hν ℓ''
    rcases hν with rfl | hν
    · by_cases hl : ℓ'' = ℓ
      · subst hl
        exact ⟨_, Set.mem_insert _ _, rfl, storedMsg_pointsTo_self t₀ ℓ'' v⟩
      · exact ⟨initialMsg v₀ t₀ ℓ'', Set.mem_insert_of_mem _ ⟨ℓ'', rfl⟩, rfl,
          storedMsg_pointsTo_initial v₀ v hl⟩
    · rw [mem_initialMem_iff] at hν
      refine ⟨initialMsg v₀ t₀ ℓ'', Set.mem_insert_of_mem _ ⟨ℓ'', rfl⟩, rfl, ?_⟩
      rw [hν]; rfl
  · -- causally connected
    rintro ν hν ℓ''
    rcases hν with rfl | hν
    · by_cases hl : ℓ'' = ℓ
      · subst hl
        exact ⟨_, Set.mem_insert _ _, rfl, storedMsg_pointsTo_self t₀ ℓ'' v, le_refl _⟩
      · exact ⟨initialMsg v₀ t₀ ℓ'', Set.mem_insert_of_mem _ ⟨ℓ'', rfl⟩, rfl,
          storedMsg_pointsTo_initial v₀ v hl, initialView_le_storedMsg_vw t₀ ℓ v⟩
    · rw [mem_initialMem_iff] at hν
      refine ⟨initialMsg v₀ t₀ ℓ'', Set.mem_insert_of_mem _ ⟨ℓ'', rfl⟩, rfl, ?_, ?_⟩
      · rw [hν]; rfl
      · rw [hν]; exact le_refl _
  · -- cycles
    rintro ν hν hcyc
    rcases hν with rfl | hν
    · -- nothing points to the new message, so it lies on no cycle
      exfalso
      obtain ⟨b, -, hbmem, -, hbne, hbpt⟩ := Relation.TransGen.tail'_iff.mp hcyc
      rcases hbmem with rfl | hbmem
      · exact hbne rfl
      · rw [mem_initialMem_iff] at hbmem
        rw [hbmem] at hbpt
        simp only [PointsTo, initialMsg_vw, storedMsg_lc, storedMsg_t] at hbpt
        linarith
    · rw [mem_initialMem_iff] at hν
      refine ⟨Set.mem_insert_of_mem _ (by rw [hν]; exact ⟨ν.lc, rfl⟩), ?_⟩
      rintro x hx hlc
      have hνt : ν.t = t₀ := by rw [hν]; rfl
      rcases hx with rfl | hx
      · rw [hνt, storedMsg_t]; linarith
      · rw [mem_initialMem_iff] at hx
        rw [hνt, hx, initialMsg_t]

/-! ## `store` is not `return` -/

/-- One concrete trace of `⟦store ℓ,v⟧`. -/
theorem mem_store (v₀ : Val) (t₀ : ℚ) (ℓ : Loc) (v : Val) :
    (⟨(fun _ ↦ t₀ : View Loc), Chro.single ⟨initialMem v₀ t₀, storedMem v₀ t₀ ℓ v⟩,
      setView (fun _ ↦ t₀) ℓ (t₀ + 1), ()⟩ : PreTrace Loc Val Unit)
      ∈ (store ℓ v : Comp cRules Loc Val Unit).traces := by
  refine subset_closure ⟨(fun _ ↦ t₀), initialMem v₀ t₀, t₀, t₀ + 1, by linarith, rfl, ?_⟩
  have hstored : WellFormed (storedMem (Loc := Loc) v₀ t₀ ℓ v) := storedMem_wellFormed v₀ t₀ ℓ v
  have hle : (fun _ ↦ t₀ : View Loc) ≤ setView (fun _ ↦ t₀) ℓ (t₀ + 1) :=
    le_setView (by simp)
  refine ⟨?_, pointsDownInto_initialMem v₀ t₀, hle, ?_, ?_⟩
  · intro T hT
    simp only [Chro.single_toList, List.mem_singleton] at hT
    subst hT
    exact ⟨initialMem_wellFormed v₀ t₀, hstored, initialMem_subset_storedMem v₀ t₀ ℓ v⟩
  · intro ℓ''
    by_cases hl : ℓ'' = ℓ
    · subst hl
      exact ⟨_, storedMsg_mem v₀ t₀ ℓ'' v, rfl, storedMsg_pointsTo_self t₀ ℓ'' v, le_refl _⟩
    · exact ⟨initialMsg v₀ t₀ ℓ'', Set.mem_insert_of_mem _ ⟨ℓ'', rfl⟩, rfl,
        storedMsg_pointsTo_initial v₀ v hl, le_setView (by simp)⟩
  · intro ν hν
    simp only [Chro.single_own, Transition.own, storedMem, Set.mem_diff,
      Set.mem_insert_iff] at hν
    obtain ⟨hν1 | hν1, hν2⟩ := hν
    · subst hν1
      exact ⟨initialView_le_storedMsg_vw t₀ ℓ v, le_refl _, by simp⟩
    · exact absurd hν1 hν2

theorem store_ne_pure (v₀ : Val) (t₀ : ℚ) (ℓ : Loc) (v : Val) :
    (store ℓ v : Comp cRules Loc Val Unit) ≠ pure () := by
  intro h
  have hmem := mem_store v₀ t₀ ℓ v
  rw [h] at hmem
  have hown := mem_pure_own hmem
  simp only [Chro.single_own, Transition.own, storedMem] at hown
  have hcontra : storedMsg t₀ ℓ v ∈ (∅ : Memory Loc Val) := by
    rw [← hown]
    exact ⟨Set.mem_insert _ _, storedMsg_not_mem_initialMem v₀ t₀ ℓ v⟩
  exact absurd hcontra (by simp)

theorem store_ne_bot (v₀ : Val) (t₀ : ℚ) (ℓ : Loc) (v : Val) :
    (store ℓ v : Comp cRules Loc Val Unit) ≠ ⊥ := by
  intro h
  have hmem := mem_store v₀ t₀ ℓ v
  rw [h] at hmem
  exact absurd hmem (by simp)

/-! ## A load may return a value that a later write has already superseded

This is the characteristic release/acquire shape: the trace below is a run of
`⟦load ℓ⟧` returning `v₀`, whose *closing memory* already contains a message at
`ℓ` with value `v` and a strictly greater timestamp.  A load is not obliged to
observe the latest write, only the one its initial view points at. -/

theorem load_stale (v₀ : Val) (t₀ : ℚ) (ℓ : Loc) (v : Val) :
    ∃ τ : PreTrace Loc Val Val,
      τ ∈ (load ℓ : Comp cRules Loc Val Val).traces ∧ τ.ret = v₀ ∧
      ∃ ν ∈ τ.ch.c, ν.lc = ℓ ∧ ν.vl = v ∧ t₀ < ν.t := by
  have hwf : WellFormed (storedMem (Loc := Loc) v₀ t₀ ℓ v) := storedMem_wellFormed v₀ t₀ ℓ v
  have hpd : PointsDownInto (fun _ ↦ t₀ : View Loc) (storedMem (Loc := Loc) v₀ t₀ ℓ v) :=
    (pointsDownInto_initialMem v₀ t₀).mono (initialMem_subset_storedMem v₀ t₀ ℓ v)
  refine ⟨⟨(fun _ ↦ t₀ : View Loc),
    Chro.single ⟨storedMem v₀ t₀ ℓ v, storedMem v₀ t₀ ℓ v⟩, (fun _ ↦ t₀), v₀⟩, ?_, rfl, ?_⟩
  · refine subset_closure (Or.inl ⟨(fun _ ↦ t₀), storedMem v₀ t₀ ℓ v, initialMsg v₀ t₀ ℓ,
      Set.mem_insert_of_mem _ ⟨ℓ, rfl⟩, rfl, rfl, rfl, rfl, ?_⟩)
    refine ⟨?_, hpd, le_refl _, hpd, ?_⟩
    · intro T hT
      simp only [Chro.single_toList, List.mem_singleton] at hT
      subst hT
      exact ⟨hwf, hwf, subset_refl _⟩
    · intro ν hν
      simp only [Chro.single_own, Transition.own, Set.diff_self] at hν
      exact absurd hν (by simp)
  · exact ⟨storedMsg t₀ ℓ v, storedMsg_mem v₀ t₀ ℓ v, rfl, rfl, by simp⟩

end Store

/-! ## Loops

Divergence is discarded: an always-diverging loop denotes `∅`. -/

theorem iter_diverge (a : A) :
    iter (fun _ : A ↦ (pure (Sum.inr a) : Comp cRules Loc Val (B ⊕ A))) a = ⊥ := by
  have h : ∀ n : ℕ,
      Comp.approx (fun _ : A ↦ (pure (Sum.inr a) : Comp cRules Loc Val (B ⊕ A))) n a = ⊥ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Comp.approx_succ, pure_bind]; exact ih
  exact le_antisymm (Comp.iterate_le (fun n ↦ (h n).le)) bot_le

theorem iter_exit (g : A → B) (a : A) :
    iter (fun x : A ↦ (pure (Sum.inl (g x)) : Comp cRules Loc Val (B ⊕ A))) a = pure (g a) := by
  have h : ∀ n : ℕ,
      Comp.approx (fun x : A ↦ (pure (Sum.inl (g x)) : Comp cRules Loc Val (B ⊕ A))) (n + 1) a
        = pure (g a) := by
    intro n; rw [Comp.approx_succ, pure_bind]; rfl
  refine le_antisymm (Comp.iterate_le (fun n ↦ ?_)) ?_
  · cases n with
    | zero => exact bot_le
    | succ n => exact (h n).le
  · exact le_trans (h 0).ge (Comp.approx_le_iterate _ 1 a)

/-- A loop whose body writes and then repeats denotes `∅`: the divergent
observations are thrown away, so nothing of the writes survives. -/
theorem iter_store_diverge [DecidableEq Loc] (ℓ : Loc) (v : Val) :
    iter (fun _ : Unit ↦
        (store ℓ v >>= fun _ ↦ pure (Sum.inr ()) : Comp cRules Loc Val (Unit ⊕ Unit))) () = ⊥ := by
  have h : ∀ n : ℕ,
      Comp.approx (fun _ : Unit ↦
        (store ℓ v >>= fun _ ↦ pure (Sum.inr ()) :
          Comp cRules Loc Val (Unit ⊕ Unit))) n () = ⊥ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Comp.approx_succ, bind_assoc]
        simp only [pure_bind, Sum.elim_inr, ih]
        exact Comp.bind_bot _
  exact le_antisymm (Comp.iterate_le (fun n ↦ (h n).le)) bot_le

end Isotope.Elgot.RA
