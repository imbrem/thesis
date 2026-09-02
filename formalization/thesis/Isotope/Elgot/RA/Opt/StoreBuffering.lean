import Isotope.Elgot.RA.Opt.Basic
import Isotope.Elgot.RA.Abstract
import Isotope.Elgot.RA.Examples
import Mathlib.Tactic.Linarith

/-!
# Store buffering in the release/acquire model

An explicit trace witnessing that

```
(x := v₁ ; y?)  ∥  (y := v₁ ; x?)
```

can return `⟨v₀, v₀⟩` from the paper's initial memory, in a **single
transition** `⟨μ₀, μ₀ ⊎ {ν_x, ν_y}⟩` — i.e. an interference-free whole-program
execution in exactly the sense of Dvir, Kammar and Lahav's own Soundness
theorem (`release-acquire`, TOPLAS 47(2):7, Thm. 8.12, journal p.42), which
sends an operational evaluation `⟨T,μ⟩, M ⇓ V` to a trace
`inf_μ T ⟨μ,μ'⟩ ω ◁ V ∈ ⟦M⟧_C`.

This is the denotational counterpart of the paper's Example 5.3 (journal p.19),
`x:=0; y:=0; ((x:=1; y?) ∥ (y:=1; x?)) ⇓_RA ⟨0,0⟩`, which the paper states
*operationally* and never computes denotationally, remarking only that
impossible outcomes "can be shown indirectly by calculating its denotation"
(p.42).  **Original work.**

## Why the loads return the stale value

`PointsTo κ ν` is `κ ν.lc = ν.t`.  Thread 1's view after its own store is
`κ₀[x ↦ t₀+1]`, which at `y` still reads `t₀` — the timestamp of the *initial*
message there — even though `ν_y` (value `v₁`, timestamp `t₀+1`) is already in
the memory.  Scatteredness makes the choice unique.  Symmetrically for thread 2.
That is the whole content of the separation from sequential consistency, where
a read returns the one current value `μ ℓ`.

## Uniformity in the rule set

The four-transition witness uses only `subset_closure`, so it lies in the
parallel composition at *every* rule set.  The collapse to a single transition
uses only `Mumble`, so the final witness is valid at `𝔠`, at the Concrete model
`𝔤𝔠`, at `𝔤𝔠 ∪ {Ti, Ab}` and at the Abstract model `𝔤𝔠𝔞` alike.  Closures only
grow, so an *existence* witness lifts up the tower.

## Scope

Everything here is denotational.  "Release/acquire admits store buffering" as an
*operational* statement would need the adequacy theorem, which is not
formalized in this repository; the honest statement is the one proved.
-/

namespace Isotope.Elgot.RA

open Isotope.Elgot (Interleave)

variable {Loc Val : Type} [DecidableEq Loc]

/-! ## The three memories and the three views -/

section Defs

variable (v₀ v₁ : Val) (t₀ : ℚ) (x y : Loc)

/-- The initial memory of the litmus test: every location holds `v₀`. -/
def sbMem0 : Memory Loc Val := initialMem v₀ t₀

/-- The memory after thread 1's store to `x`. -/
def sbMem1 : Memory Loc Val := insert (storedMsg t₀ x v₁) (sbMem0 v₀ t₀)

/-- The memory after both stores. -/
def sbMem2 : Memory Loc Val := insert (storedMsg t₀ y v₁) (sbMem1 v₀ v₁ t₀ x)

/-- Thread 1's view after its own store: advanced at `x` only. -/
def sbView1 : View Loc := setView (fun _ ↦ t₀) x (t₀ + 1)

/-- Thread 2's view after its own store: advanced at `y` only. -/
def sbView2 : View Loc := setView (fun _ ↦ t₀) y (t₀ + 1)

end Defs

section Basic

variable {v₀ v₁ : Val} {t₀ : ℚ} {x y : Loc}

@[simp] theorem sbView1_self : sbView1 (Loc := Loc) t₀ x x = t₀ + 1 := setView_self ..

theorem sbView1_of_ne {ℓ : Loc} (h : ℓ ≠ x) : sbView1 (Loc := Loc) t₀ x ℓ = t₀ :=
  setView_of_ne _ h

@[simp] theorem sbView2_self : sbView2 (Loc := Loc) t₀ y y = t₀ + 1 := setView_self ..

theorem sbView2_of_ne {ℓ : Loc} (h : ℓ ≠ y) : sbView2 (Loc := Loc) t₀ y ℓ = t₀ :=
  setView_of_ne _ h

theorem initView_le_sbView1 : (fun _ ↦ t₀ : View Loc) ≤ sbView1 t₀ x :=
  le_setView (by simp)

theorem initView_le_sbView2 : (fun _ ↦ t₀ : View Loc) ≤ sbView2 t₀ y :=
  le_setView (by simp)

theorem sbMem0_subset_sbMem1 : sbMem0 (Loc := Loc) v₀ t₀ ⊆ sbMem1 v₀ v₁ t₀ x :=
  Set.subset_insert _ _

theorem sbMem1_subset_sbMem2 : sbMem1 (Loc := Loc) v₀ v₁ t₀ x ⊆ sbMem2 v₀ v₁ t₀ x y :=
  Set.subset_insert _ _

theorem sbMem0_subset_sbMem2 : sbMem0 (Loc := Loc) v₀ t₀ ⊆ sbMem2 v₀ v₁ t₀ x y :=
  subset_trans sbMem0_subset_sbMem1 sbMem1_subset_sbMem2

theorem sbMsgX_mem : storedMsg t₀ x v₁ ∈ sbMem2 (Loc := Loc) v₀ v₁ t₀ x y :=
  Set.mem_insert_of_mem _ (Set.mem_insert _ _)

theorem sbMsgY_mem : storedMsg t₀ y v₁ ∈ sbMem2 (Loc := Loc) v₀ v₁ t₀ x y :=
  Set.mem_insert _ _

theorem initialMsg_mem_sbMem2 (ℓ : Loc) :
    initialMsg v₀ t₀ ℓ ∈ sbMem2 (Loc := Loc) v₀ v₁ t₀ x y :=
  sbMem0_subset_sbMem2 ⟨ℓ, rfl⟩

/-- The two written messages are the only local messages of the witness. -/
theorem sbMem2_diff_sbMem0 {ν : Msg Loc Val} (h : ν ∈ sbMem2 v₀ v₁ t₀ x y)
    (h0 : ν ∉ sbMem0 v₀ t₀) : ν = storedMsg t₀ x v₁ ∨ ν = storedMsg t₀ y v₁ := by
  rcases h with rfl | h
  · exact Or.inr rfl
  · rcases h with rfl | h
    · exact Or.inl rfl
    · exact absurd h h0

end Basic

/-! ## Well-formedness -/

section WF

variable [Finite Loc] [Nonempty Loc] (v₀ v₁ : Val) (t₀ : ℚ) {x y : Loc}

/-- The memory after both stores is well formed.  The two extra messages sit at
*different* locations, so the paper's scatteredness condition is vacuous between
them, and neither is pointed at by the shared initial view, so neither lies on a
cycle of the points-to digraph. -/
theorem sbMem2_wellFormed (hxy : x ≠ y) :
    WellFormed (sbMem2 (Loc := Loc) v₀ v₁ t₀ x y) := by
  have hset : sbMem2 (Loc := Loc) v₀ v₁ t₀ x y
      = {storedMsg t₀ x v₁, storedMsg t₀ y v₁} ∪ initialMem v₀ t₀ := by
    rw [sbMem2, sbMem1, sbMem0, Set.insert_union, Set.singleton_union]
    exact Set.insert_comm _ _ _
  rw [hset]
  refine union_initialMem_wellFormed v₀ t₀ (fun _ ↦ t₀) _
    ((Set.finite_singleton _).insert _) ?_ ?_ ?_
    (fun ℓ ↦ ⟨initialMsg v₀ t₀ ℓ, Or.inr ⟨ℓ, rfl⟩, rfl, rfl, le_refl _⟩) ?_ ?_
  · rintro χ (rfl | rfl) <;> simp
  · rintro χ (rfl | rfl) <;> simp
  · rintro χ (rfl | rfl) <;> simp
  · rintro χ (rfl | rfl) χ' (rfl | rfl) hlc hov <;> first
      | rfl
      | (exact absurd hlc (by simpa using hxy))
      | (exact absurd hlc (by simpa using hxy.symm))
  · rintro χ (rfl | rfl) χ' (rfl | rfl) hpt hpt' <;> simp only [storedMsg_lc,
      storedMsg_t] at hpt hpt' <;> first | rfl | linarith

theorem sbMem1_wellFormed : WellFormed (sbMem1 (Loc := Loc) v₀ v₁ t₀ x) :=
  storedMem_wellFormed v₀ t₀ x v₁

theorem sbMem0_wellFormed : WellFormed (sbMem0 (Loc := Loc) v₀ t₀) :=
  initialMem_wellFormed v₀ t₀

end WF

/-! ## The delimiting views point downwards where they must -/

section Points

variable {v₀ v₁ : Val} {t₀ : ℚ} {x y : Loc}

theorem pointsDownInto_sbMem0 :
    PointsDownInto (fun _ ↦ t₀ : View Loc) (sbMem0 (Loc := Loc) v₀ t₀) :=
  pointsDownInto_initialMem v₀ t₀

theorem pointsDownInto_sbMem1 :
    PointsDownInto (fun _ ↦ t₀ : View Loc) (sbMem1 (Loc := Loc) v₀ v₁ t₀ x) :=
  pointsDownInto_sbMem0.mono sbMem0_subset_sbMem1

theorem pointsDownInto_sbMem2 :
    PointsDownInto (fun _ ↦ t₀ : View Loc) (sbMem2 (Loc := Loc) v₀ v₁ t₀ x y) :=
  pointsDownInto_sbMem0.mono sbMem0_subset_sbMem2

/-- Thread 1's view points downwards into the final memory — at `x` to its own
write, and *at `y` to the initial message*, which is why its load of `y` returns
the stale `v₀`. -/
theorem sbView1_pointsDownInto :
    PointsDownInto (sbView1 t₀ x) (sbMem2 (Loc := Loc) v₀ v₁ t₀ x y) := by
  intro ℓ
  by_cases hl : ℓ = x
  · subst hl
    exact ⟨storedMsg t₀ ℓ v₁, sbMsgX_mem, rfl, by simp [PointsTo], le_refl _⟩
  · exact ⟨initialMsg v₀ t₀ ℓ, initialMsg_mem_sbMem2 ℓ, rfl,
      by simp [PointsTo, sbView1_of_ne hl], initView_le_sbView1⟩

theorem sbView2_pointsDownInto :
    PointsDownInto (sbView2 t₀ y) (sbMem2 (Loc := Loc) v₀ v₁ t₀ x y) := by
  intro ℓ
  by_cases hl : ℓ = y
  · subst hl
    exact ⟨storedMsg t₀ ℓ v₁, sbMsgY_mem, rfl, by simp [PointsTo], le_refl _⟩
  · exact ⟨initialMsg v₀ t₀ ℓ, initialMsg_mem_sbMem2 ℓ, rfl,
      by simp [PointsTo, sbView2_of_ne hl], initView_le_sbView2⟩

/-- The final view of the whole composition, `ω = σ₁ ⊔ σ₂`, points downwards
into the final memory: at `x` to `ν_x`, at `y` to `ν_y`, elsewhere to the
initial message. -/
theorem sbSup_pointsDownInto (hxy : x ≠ y) :
    PointsDownInto (sbView1 t₀ x ⊔ sbView2 t₀ y) (sbMem2 (Loc := Loc) v₀ v₁ t₀ x y) := by
  intro ℓ
  by_cases hl : ℓ = x
  · subst hl
    refine ⟨storedMsg t₀ ℓ v₁, sbMsgX_mem, rfl, ?_, le_sup_left⟩
    have h : (sbView1 t₀ ℓ ⊔ sbView2 t₀ y) ℓ = sbView1 t₀ ℓ ℓ ⊔ sbView2 t₀ y ℓ := rfl
    simp only [PointsTo, storedMsg_lc, storedMsg_t, h, sbView1_self, sbView2_of_ne hxy]
    exact sup_eq_left.mpr (by linarith)
  · by_cases hl' : ℓ = y
    · subst hl'
      refine ⟨storedMsg t₀ ℓ v₁, sbMsgY_mem, rfl, ?_, le_sup_right⟩
      have h : (sbView1 t₀ x ⊔ sbView2 t₀ ℓ) ℓ = sbView1 t₀ x ℓ ⊔ sbView2 t₀ ℓ ℓ := rfl
      simp only [PointsTo, storedMsg_lc, storedMsg_t, h, sbView2_self, sbView1_of_ne hl]
      exact sup_eq_right.mpr (by linarith)
    · refine ⟨initialMsg v₀ t₀ ℓ, initialMsg_mem_sbMem2 ℓ, rfl, ?_,
        le_trans initView_le_sbView1 le_sup_left⟩
      have h : (sbView1 t₀ x ⊔ sbView2 t₀ y) ℓ = sbView1 t₀ x ℓ ⊔ sbView2 t₀ y ℓ := rfl
      simp only [PointsTo, initialMsg_lc, initialMsg_t, h, sbView1_of_ne hl,
        sbView2_of_ne hl']
      exact sup_idem _

theorem initView_le_sbSup :
    (fun _ ↦ t₀ : View Loc) ≤ sbView1 t₀ x ⊔ sbView2 t₀ y :=
  le_trans initView_le_sbView1 le_sup_left

/-- Thread 1's view points downwards into the memory after its own store, which
is the `closePts` condition of its store trace. -/
theorem sbView1_pointsDownInto_sbMem1 :
    PointsDownInto (sbView1 t₀ x) (sbMem1 (Loc := Loc) v₀ v₁ t₀ x) := by
  intro ℓ
  by_cases hl : ℓ = x
  · subst hl
    exact ⟨storedMsg t₀ ℓ v₁, Set.mem_insert _ _, rfl, by simp [PointsTo], le_refl _⟩
  · exact ⟨initialMsg v₀ t₀ ℓ, Set.mem_insert_of_mem _ ⟨ℓ, rfl⟩, rfl,
      by simp [PointsTo, sbView1_of_ne hl], initView_le_sbView1⟩

end Points

/-! ## The chronicles of the witness -/

section Chronicles

variable (v₀ v₁ : Val) (t₀ : ℚ) (x y : Loc)

/-- The four-transition chronicle of the interleaved witness:
`⟨μ₀,μ₁⟩⟨μ₁,μ₂⟩⟨μ₂,μ₂⟩⟨μ₂,μ₂⟩`. -/
def sbChro4 : Chro Loc Val where
  first := ⟨sbMem0 v₀ t₀, sbMem1 v₀ v₁ t₀ x⟩
  rest := [⟨sbMem1 v₀ v₁ t₀ x, sbMem2 v₀ v₁ t₀ x y⟩,
           ⟨sbMem2 v₀ v₁ t₀ x y, sbMem2 v₀ v₁ t₀ x y⟩,
           ⟨sbMem2 v₀ v₁ t₀ x y, sbMem2 v₀ v₁ t₀ x y⟩]
  chain := by
    refine List.isChain_cons_cons.mpr ⟨subset_refl _, ?_⟩
    refine List.isChain_cons_cons.mpr ⟨subset_refl _, ?_⟩
    exact List.isChain_cons_cons.mpr ⟨subset_refl _, List.isChain_singleton _⟩

/-- After the first `Mumble`. -/
def sbChro3 : Chro Loc Val where
  first := ⟨sbMem0 v₀ t₀, sbMem2 v₀ v₁ t₀ x y⟩
  rest := [⟨sbMem2 v₀ v₁ t₀ x y, sbMem2 v₀ v₁ t₀ x y⟩,
           ⟨sbMem2 v₀ v₁ t₀ x y, sbMem2 v₀ v₁ t₀ x y⟩]
  chain := by
    refine List.isChain_cons_cons.mpr ⟨subset_refl _, ?_⟩
    exact List.isChain_cons_cons.mpr ⟨subset_refl _, List.isChain_singleton _⟩

/-- After the second `Mumble`. -/
def sbChro2 : Chro Loc Val where
  first := ⟨sbMem0 v₀ t₀, sbMem2 v₀ v₁ t₀ x y⟩
  rest := [⟨sbMem2 v₀ v₁ t₀ x y, sbMem2 v₀ v₁ t₀ x y⟩]
  chain := List.isChain_cons_cons.mpr ⟨subset_refl _, List.isChain_singleton _⟩

end Chronicles

/-! ## The trace conditions -/

section IsTraceSection

variable [Finite Loc] [Nonempty Loc] {v₀ v₁ : Val} {t₀ : ℚ} {x y : Loc}

/-- Every transition of the witness is well formed. -/
theorem sbTransition_wf (hxy : x ≠ y) {T : Transition Loc Val}
    (h : T = ⟨sbMem0 v₀ t₀, sbMem1 v₀ v₁ t₀ x⟩ ∨ T = ⟨sbMem1 v₀ v₁ t₀ x, sbMem2 v₀ v₁ t₀ x y⟩ ∨
      T = ⟨sbMem2 v₀ v₁ t₀ x y, sbMem2 v₀ v₁ t₀ x y⟩ ∨
      T = ⟨sbMem0 v₀ t₀, sbMem2 v₀ v₁ t₀ x y⟩) : T.WF := by
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨sbMem0_wellFormed v₀ t₀, sbMem1_wellFormed v₀ v₁ t₀, sbMem0_subset_sbMem1⟩
  · exact ⟨sbMem1_wellFormed v₀ v₁ t₀, sbMem2_wellFormed v₀ v₁ t₀ hxy,
      sbMem1_subset_sbMem2⟩
  · exact ⟨sbMem2_wellFormed v₀ v₁ t₀ hxy, sbMem2_wellFormed v₀ v₁ t₀ hxy, subset_refl _⟩
  · exact ⟨sbMem0_wellFormed v₀ t₀, sbMem2_wellFormed v₀ v₁ t₀ hxy, sbMem0_subset_sbMem2⟩

/-- **The trace conditions, once and for all.**  Any chronicle running from the
initial memory to the final one, with well-formed transitions and no local
messages beyond the two writes, delimited by the initial view and by
`σ₁ ⊔ σ₂`, is a trace. -/
theorem sbIsTrace {A : Type} (r : A) (hxy : x ≠ y) (ξ : Chro Loc Val)
    (hT : ∀ T ∈ ξ.toList, T.WF)
    (ho : ξ.o = sbMem0 v₀ t₀) (hc : ξ.c = sbMem2 v₀ v₁ t₀ x y)
    (hown : ξ.own ⊆ sbMem2 v₀ v₁ t₀ x y \ sbMem0 v₀ t₀) :
    IsTrace (⟨(fun _ ↦ t₀ : View Loc), ξ, sbView1 t₀ x ⊔ sbView2 t₀ y, r⟩ :
      PreTrace Loc Val A) where
  wf := hT
  openPts := by rw [ho]; exact pointsDownInto_sbMem0
  mono := initView_le_sbSup
  closePts := by rw [hc]; exact sbSup_pointsDownInto hxy
  own := by
    intro ν hν
    obtain ⟨hν2, hν0⟩ := hown hν
    rcases sbMem2_diff_sbMem0 hν2 hν0 with rfl | rfl
    · refine ⟨le_trans initView_le_sbView1 (le_refl _), le_sup_left, ?_⟩
      simp only [storedMsg_lc, storedMsg_t]
      linarith
    · refine ⟨le_trans initView_le_sbView2 (le_refl _), le_sup_right, ?_⟩
      simp only [storedMsg_lc, storedMsg_t]
      linarith

end IsTraceSection

/-! ## The four generating traces, the two threads, and the interleaving -/

section Witness

variable [Finite Loc] [Nonempty Loc] {R : RuleSet} {v₀ v₁ : Val} {t₀ : ℚ} {x y : Loc}

/-- Thread 1's store: `κ₀ ⟨μ₀, μ₁⟩ κ₀[x↦t₀+1] ◁ ⟨⟩`. -/
theorem sbStoreX_isTrace :
    IsTrace (⟨(fun _ ↦ t₀ : View Loc), Chro.single ⟨sbMem0 v₀ t₀, sbMem1 v₀ v₁ t₀ x⟩,
      sbView1 t₀ x, ()⟩ : PreTrace Loc Val Unit) where
  wf := by
    intro T hT
    simp only [Chro.single_toList, List.mem_singleton] at hT
    subst hT
    exact ⟨sbMem0_wellFormed v₀ t₀, sbMem1_wellFormed v₀ v₁ t₀, sbMem0_subset_sbMem1⟩
  openPts := pointsDownInto_sbMem0
  mono := initView_le_sbView1
  closePts := sbView1_pointsDownInto_sbMem1
  own := by
    intro ν hν
    simp only [Chro.single_own, Transition.own, sbMem1, Set.mem_diff,
      Set.mem_insert_iff] at hν
    obtain ⟨hν1 | hν1, hν2⟩ := hν
    · subst hν1
      refine ⟨initView_le_sbView1, le_refl _, ?_⟩
      simp only [storedMsg_lc, storedMsg_t]
      linarith
    · exact absurd hν1 hν2

theorem sbStoreX_mem :
    (⟨(fun _ ↦ t₀ : View Loc), Chro.single ⟨sbMem0 v₀ t₀, sbMem1 v₀ v₁ t₀ x⟩,
      sbView1 t₀ x, ()⟩ : PreTrace Loc Val Unit)
      ∈ (store x v₁ : Comp R Loc Val Unit).traces :=
  subset_closure ⟨(fun _ ↦ t₀), sbMem0 v₀ t₀, t₀, t₀ + 1, by linarith, rfl, sbStoreX_isTrace⟩

/-- Thread 2's store: `κ₀ ⟨μ₁, μ₂⟩ κ₀[y↦t₀+1] ◁ ⟨⟩`.  Its rely memory is `μ₁`,
i.e. it runs after thread 1's store has landed. -/
theorem sbStoreY_isTrace (hxy : x ≠ y) :
    IsTrace (⟨(fun _ ↦ t₀ : View Loc),
      Chro.single ⟨sbMem1 v₀ v₁ t₀ x, sbMem2 v₀ v₁ t₀ x y⟩,
      sbView2 t₀ y, ()⟩ : PreTrace Loc Val Unit) where
  wf := by
    intro T hT
    simp only [Chro.single_toList, List.mem_singleton] at hT
    subst hT
    exact ⟨sbMem1_wellFormed v₀ v₁ t₀, sbMem2_wellFormed v₀ v₁ t₀ hxy, sbMem1_subset_sbMem2⟩
  openPts := pointsDownInto_sbMem1
  mono := initView_le_sbView2
  closePts := sbView2_pointsDownInto
  own := by
    intro ν hν
    simp only [Chro.single_own, Transition.own, sbMem2, Set.mem_diff,
      Set.mem_insert_iff] at hν
    obtain ⟨hν1 | hν1, hν2⟩ := hν
    · subst hν1
      refine ⟨initView_le_sbView2, le_refl _, ?_⟩
      simp only [storedMsg_lc, storedMsg_t]
      linarith
    · exact absurd hν1 hν2

theorem sbStoreY_mem (hxy : x ≠ y) :
    (⟨(fun _ ↦ t₀ : View Loc), Chro.single ⟨sbMem1 v₀ v₁ t₀ x, sbMem2 v₀ v₁ t₀ x y⟩,
      sbView2 t₀ y, ()⟩ : PreTrace Loc Val Unit)
      ∈ (store y v₁ : Comp R Loc Val Unit).traces :=
  subset_closure ⟨(fun _ ↦ t₀), sbMem1 v₀ v₁ t₀ x, t₀, t₀ + 1, by linarith, rfl,
    sbStoreY_isTrace hxy⟩

/-- **Thread 1's load of `y` returns the stale `v₀`.**  Its view is `σ₁`, which
at `y` still reads `t₀`, the timestamp of the *initial* message — even though
`ν_y`, with value `v₁` and timestamp `t₀+1`, is already in the memory `μ₂`. -/
theorem sbLoadY_mem (hxy : x ≠ y) :
    (⟨sbView1 t₀ x, Chro.single ⟨sbMem2 v₀ v₁ t₀ x y, sbMem2 v₀ v₁ t₀ x y⟩,
      sbView1 t₀ x, v₀⟩ : PreTrace Loc Val Val)
      ∈ (load y : Comp R Loc Val Val).traces := by
  refine subset_closure (Or.inl ⟨sbView1 t₀ x, sbMem2 v₀ v₁ t₀ x y, initialMsg v₀ t₀ y,
    initialMsg_mem_sbMem2 y, rfl, ?_, rfl, rfl, ?_⟩)
  · simp only [PointsTo, initialMsg_lc, initialMsg_t]
    exact sbView1_of_ne (Ne.symm hxy)
  · exact pureGen_isTrace v₀ _ ⟨sbView1 t₀ x, sbMem2 v₀ v₁ t₀ x y,
      sbMem2_wellFormed v₀ v₁ t₀ hxy, sbView1_pointsDownInto, rfl⟩

/-- Symmetrically, thread 2's load of `x` returns `v₀`. -/
theorem sbLoadX_mem (hxy : x ≠ y) :
    (⟨sbView2 t₀ y, Chro.single ⟨sbMem2 v₀ v₁ t₀ x y, sbMem2 v₀ v₁ t₀ x y⟩,
      sbView2 t₀ y, v₀⟩ : PreTrace Loc Val Val)
      ∈ (load x : Comp R Loc Val Val).traces := by
  refine subset_closure (Or.inl ⟨sbView2 t₀ y, sbMem2 v₀ v₁ t₀ x y, initialMsg v₀ t₀ x,
    initialMsg_mem_sbMem2 x, rfl, ?_, rfl, rfl, ?_⟩)
  · simp only [PointsTo, initialMsg_lc, initialMsg_t]
    exact sbView2_of_ne hxy
  · exact pureGen_isTrace v₀ _ ⟨sbView2 t₀ y, sbMem2 v₀ v₁ t₀ x y,
      sbMem2_wellFormed v₀ v₁ t₀ hxy, sbView2_pointsDownInto, rfl⟩

/-- Thread 1's chronicle `⟨μ₀,μ₁⟩⟨μ₂,μ₂⟩`. -/
def sbThreadX (v₀ v₁ : Val) (t₀ : ℚ) (x y : Loc) : Chro Loc Val where
  first := ⟨sbMem0 v₀ t₀, sbMem1 v₀ v₁ t₀ x⟩
  rest := [⟨sbMem2 v₀ v₁ t₀ x y, sbMem2 v₀ v₁ t₀ x y⟩]
  chain := List.isChain_cons_cons.mpr ⟨sbMem1_subset_sbMem2, List.isChain_singleton _⟩

/-- Thread 2's chronicle `⟨μ₁,μ₂⟩⟨μ₂,μ₂⟩`. -/
def sbThreadY (v₀ v₁ : Val) (t₀ : ℚ) (x y : Loc) : Chro Loc Val where
  first := ⟨sbMem1 v₀ v₁ t₀ x, sbMem2 v₀ v₁ t₀ x y⟩
  rest := [⟨sbMem2 v₀ v₁ t₀ x y, sbMem2 v₀ v₁ t₀ x y⟩]
  chain := List.isChain_cons_cons.mpr ⟨subset_refl _, List.isChain_singleton _⟩

theorem sbThreadX_mem (hxy : x ≠ y) :
    (⟨(fun _ ↦ t₀ : View Loc), sbThreadX v₀ v₁ t₀ x y, sbView1 t₀ x, v₀⟩ :
      PreTrace Loc Val Val)
      ∈ (store x v₁ >>= fun _ ↦ (load y : Comp R Loc Val Val)).traces := by
  exact subset_closure
    ⟨⟨(fun _ ↦ t₀ : View Loc), Chro.single ⟨sbMem0 v₀ t₀, sbMem1 v₀ v₁ t₀ x⟩,
        sbView1 t₀ x, ()⟩,
      ⟨sbView1 t₀ x, Chro.single ⟨sbMem2 v₀ v₁ t₀ x y, sbMem2 v₀ v₁ t₀ x y⟩,
        sbView1 t₀ x, v₀⟩,
      sbMem1_subset_sbMem2, sbStoreX_mem, sbLoadY_mem hxy, le_refl _, rfl⟩

theorem sbThreadY_mem (hxy : x ≠ y) :
    (⟨(fun _ ↦ t₀ : View Loc), sbThreadY v₀ v₁ t₀ x y, sbView2 t₀ y, v₀⟩ :
      PreTrace Loc Val Val)
      ∈ (store y v₁ >>= fun _ ↦ (load x : Comp R Loc Val Val)).traces := by
  exact subset_closure
    ⟨⟨(fun _ ↦ t₀ : View Loc), Chro.single ⟨sbMem1 v₀ v₁ t₀ x, sbMem2 v₀ v₁ t₀ x y⟩,
        sbView2 t₀ y, ()⟩,
      ⟨sbView2 t₀ y, Chro.single ⟨sbMem2 v₀ v₁ t₀ x y, sbMem2 v₀ v₁ t₀ x y⟩,
        sbView2 t₀ y, v₀⟩,
      subset_refl _, sbStoreY_mem hxy, sbLoadX_mem hxy, le_refl _, rfl⟩

/-- The four-transition interleaving is a trace of the parallel composition, at
**every** rule set: only `subset_closure` is used. -/
theorem sbPar4_mem (hxy : x ≠ y) :
    (⟨(fun _ ↦ t₀ : View Loc), sbChro4 v₀ v₁ t₀ x y, sbView1 t₀ x ⊔ sbView2 t₀ y,
      (v₀, v₀)⟩ : PreTrace Loc Val (Val × Val))
      ∈ ((store x v₁ >>= fun _ ↦ load y).par
          (store y v₁ >>= fun _ ↦ load x) : Comp R Loc Val (Val × Val)).traces := by
  refine subset_closure
    ⟨⟨(fun _ ↦ t₀ : View Loc), sbThreadX v₀ v₁ t₀ x y, sbView1 t₀ x, v₀⟩,
      sbThreadX_mem hxy,
      ⟨(fun _ ↦ t₀ : View Loc), sbThreadY v₀ v₁ t₀ x y, sbView2 t₀ y, v₀⟩,
      sbThreadY_mem hxy, ?_, ?_, rfl, rfl⟩
  · exact Interleave.left (Interleave.right (Interleave.left (Interleave.right
      Interleave.nil)))
  · exact isInfMem_pair_self pointsDownInto_sbMem0

/-! ## Collapsing to a single transition -/

theorem sbChro4_isTrace (hxy : x ≠ y) :
    IsTrace (⟨(fun _ ↦ t₀ : View Loc), sbChro4 v₀ v₁ t₀ x y,
      sbView1 t₀ x ⊔ sbView2 t₀ y, (v₀, v₀)⟩ : PreTrace Loc Val (Val × Val)) := by
  refine sbIsTrace _ hxy _ ?_ rfl rfl ?_
  · intro T hT
    simp only [sbChro4, Chro.toList, List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl | rfl | rfl <;> exact sbTransition_wf hxy (by tauto)
  · intro ν hν
    simp only [sbChro4, Chro.own_eq_listOwn, Chro.toList, listOwn_cons, listOwn_nil,
      Transition.own, Set.union_empty, Set.mem_union, Set.mem_diff, Set.diff_self,
      Set.mem_empty_iff_false, or_false] at hν
    rcases hν with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨sbMem1_subset_sbMem2 h1, h2⟩
    · exact ⟨h1, fun h ↦ h2 (sbMem0_subset_sbMem1 h)⟩

theorem sbChro3_isTrace (hxy : x ≠ y) :
    IsTrace (⟨(fun _ ↦ t₀ : View Loc), sbChro3 v₀ v₁ t₀ x y,
      sbView1 t₀ x ⊔ sbView2 t₀ y, (v₀, v₀)⟩ : PreTrace Loc Val (Val × Val)) := by
  refine sbIsTrace _ hxy _ ?_ rfl rfl ?_
  · intro T hT
    simp only [sbChro3, Chro.toList, List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl | rfl <;> exact sbTransition_wf hxy (by tauto)
  · intro ν hν
    simp only [sbChro3, Chro.own_eq_listOwn, Chro.toList, listOwn_cons, listOwn_nil,
      Transition.own, Set.union_empty, Set.mem_union, Set.diff_self,
      Set.mem_empty_iff_false, or_false] at hν
    exact hν

theorem sbChro2_isTrace (hxy : x ≠ y) :
    IsTrace (⟨(fun _ ↦ t₀ : View Loc), sbChro2 v₀ v₁ t₀ x y,
      sbView1 t₀ x ⊔ sbView2 t₀ y, (v₀, v₀)⟩ : PreTrace Loc Val (Val × Val)) := by
  refine sbIsTrace _ hxy _ ?_ rfl rfl ?_
  · intro T hT
    simp only [sbChro2, Chro.toList, List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl <;> exact sbTransition_wf hxy (by tauto)
  · intro ν hν
    simp only [sbChro2, Chro.own_eq_listOwn, Chro.toList, listOwn_cons, listOwn_nil,
      Transition.own, Set.union_empty, Set.mem_union, Set.diff_self,
      Set.mem_empty_iff_false, or_false] at hν
    exact hν

theorem sbChro1_isTrace (hxy : x ≠ y) :
    IsTrace (⟨(fun _ ↦ t₀ : View Loc), Chro.single ⟨sbMem0 v₀ t₀, sbMem2 v₀ v₁ t₀ x y⟩,
      sbView1 t₀ x ⊔ sbView2 t₀ y, (v₀, v₀)⟩ : PreTrace Loc Val (Val × Val)) := by
  refine sbIsTrace _ hxy _ ?_ rfl rfl ?_
  · intro T hT
    simp only [Chro.single_toList, List.mem_singleton] at hT
    subst hT
    exact sbTransition_wf hxy (by tauto)
  · intro ν hν
    simpa [Chro.single_own, Transition.own] using hν

/-- **Release/acquire admits store buffering.**  The outcome `⟨v₀, v₀⟩` of

```
(x := v₁ ; y?)  ∥  (y := v₁ ; x?)
```

is realised by a **single-transition** trace `κ₀ ⟨μ₀, μ₀ ⊎ {ν_x, ν_y}⟩ ω ◁ ⟨v₀,v₀⟩`
from the paper's initial memory `μ₀` and initial view `κ₀` — an interference-free
whole-program execution in the sense of the paper's own Soundness theorem
(journal Thm. 8.12, p.42).

Valid at **every** rule set containing `Mumble`: the `𝔠`-model, the Concrete
model `𝔤𝔠`, `𝔤𝔠 ∪ {Ti, Ab}` and the Abstract model `𝔤𝔠𝔞`.

This is the denotational form of the paper's Example 5.3 (journal p.19), which
the paper states only operationally.  **Original work.** -/
theorem ra_admits_store_buffering (hMu : Rule.Mu ∈ R) (hxy : x ≠ y) :
    (⟨(fun _ ↦ t₀ : View Loc), Chro.single ⟨sbMem0 v₀ t₀, sbMem2 v₀ v₁ t₀ x y⟩,
        sbView1 t₀ x ⊔ sbView2 t₀ y, (v₀, v₀)⟩ : PreTrace Loc Val (Val × Val))
      ∈ ((store x v₁ >>= fun _ ↦ load y).par
          (store y v₁ >>= fun _ ↦ load x) : Comp R Loc Val (Val × Val)).traces := by
  have hclosed := ((store x v₁ >>= fun _ ↦ (load y : Comp R Loc Val Val)).par
    (store y v₁ >>= fun _ ↦ (load x : Comp R Loc Val Val))).closed
  refine hclosed.mem_of_refines
    (sbPar4_mem (R := R) (v₀ := v₀) (v₁ := v₁) (t₀ := t₀) hxy) ?_
  set ω : View Loc := sbView1 t₀ x ⊔ sbView2 t₀ y with hω
  have s1 : TStep R
      (⟨(fun _ ↦ t₀ : View Loc), sbChro4 v₀ v₁ t₀ x y, ω, (v₀, v₀)⟩ :
        PreTrace Loc Val (Val × Val))
      ⟨(fun _ ↦ t₀ : View Loc), sbChro3 v₀ v₁ t₀ x y, ω, (v₀, v₀)⟩ :=
    ⟨Step.chro hMu (ChroStep.mumble _ _ [] _ (sbMem0 v₀ t₀) (sbMem1 v₀ v₁ t₀ x)
      (sbMem2 v₀ v₁ t₀ x y) rfl rfl), sbChro3_isTrace hxy⟩
  have s2 : TStep R
      (⟨(fun _ ↦ t₀ : View Loc), sbChro3 v₀ v₁ t₀ x y, ω, (v₀, v₀)⟩ :
        PreTrace Loc Val (Val × Val))
      ⟨(fun _ ↦ t₀ : View Loc), sbChro2 v₀ v₁ t₀ x y, ω, (v₀, v₀)⟩ :=
    ⟨Step.chro hMu (ChroStep.mumble _ _ [] _ (sbMem0 v₀ t₀) (sbMem2 v₀ v₁ t₀ x y)
      (sbMem2 v₀ v₁ t₀ x y) rfl rfl), sbChro2_isTrace hxy⟩
  have s3 : TStep R
      (⟨(fun _ ↦ t₀ : View Loc), sbChro2 v₀ v₁ t₀ x y, ω, (v₀, v₀)⟩ :
        PreTrace Loc Val (Val × Val))
      ⟨(fun _ ↦ t₀ : View Loc), Chro.single ⟨sbMem0 v₀ t₀, sbMem2 v₀ v₁ t₀ x y⟩, ω,
        (v₀, v₀)⟩ :=
    ⟨Step.chro hMu (ChroStep.mumble _ _ [] [] (sbMem0 v₀ t₀) (sbMem2 v₀ v₁ t₀ x y)
      (sbMem2 v₀ v₁ t₀ x y) rfl rfl), sbChro1_isTrace hxy⟩
  exact ((Refines.single s1).trans (Refines.single s2)).trans (Refines.single s3)

/-- …in particular, the parallel composition is not the empty computation. -/
theorem sb_par_ne_bot (v₀ : Val) (t₀ : ℚ) (hMu : Rule.Mu ∈ R) (hxy : x ≠ y) :
    ((store x v₁ >>= fun _ ↦ load y).par
      (store y v₁ >>= fun _ ↦ load x) : Comp R Loc Val (Val × Val)) ≠ ⊥ := by
  intro h
  have hmem := ra_admits_store_buffering (R := R) (v₀ := v₀) (v₁ := v₁) (t₀ := t₀) hMu hxy
  rw [h] at hmem
  exact absurd hmem (by simp)

end Witness

end Isotope.Elgot.RA
