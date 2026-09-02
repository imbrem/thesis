import Isotope.Elgot.RA.Pull
import Isotope.Elgot.RA.Rewrite

/-!
# When the target of a `𝔤`-rewrite is a trace

Dvir, Kammar and Lahav's **Lemma F.1** (journal p.61) characterizes, for each
closure rule, when the target of a rewrite is again a trace, given that the
source is.  The paper needs it because Rewrite Castling produces a *new*
intermediate pre-trace whose trace-hood must be checked.

This file proves what that use actually needs, which is slightly different from
Lemma F.1 and slightly stronger in one respect: for each of the three `𝔤` rules
we show that if the source is a trace **and every memory of the target is
well-formed**, then the target is a trace.  Well-formedness of the target's
memories is left as a hypothesis rather than derived, because at every site
where these lemmas are used it is already available — the target memories are
memories of a trace that is given.  Deriving it instead (the paper's `Ls✓`,
`Ex✓`, `Cn✓`) would require re-proving causal connectedness and the cycle
condition from scratch, which nothing here needs.

So: **this is not a transcription of Lemma F.1**, but the reusable part of it.
The statements and proofs are ours.

The `Condense` case is the substantial one.  It rests on Lemma 7.6 in the form
`View.pull_le_pull_of_scattered`, and on the "free segment" invariant
(`Scattered.segFree_of_pull`, `Scattered.notMem_of_pull`) that carries the
trace condition `α ν.lc < ν.t` on local messages through a pull.
-/

universe u

namespace Isotope.Elgot.RA

variable {Loc Val : Type}

/-! ## Two list lemmas -/

/-- The closing memory of a mapped list is the image of the closing memory's
transition. -/
theorem listC_map {h : Transition Loc Val → Transition Loc Val}
    (l : List (Transition Loc Val)) (hl : l ≠ []) :
    ∃ T ∈ l, listC l = T.closing ∧ listC (l.map h) = (h T).closing := by
  obtain ⟨l', T, rfl, hc⟩ := listC_concat l hl
  refine ⟨T, by simp, hc, ?_⟩
  rw [List.map_append, List.map_cons, List.map_nil, listC_append, listC_singleton]

/-- Membership in the local messages of a mapped list. -/
theorem mem_listOwn_map {h : Transition Loc Val → Transition Loc Val}
    {l : List (Transition Loc Val)} {ν : Msg Loc Val} (hν : ν ∈ listOwn (l.map h)) :
    ∃ T ∈ l, ν ∈ (h T).own := by
  obtain ⟨S, hS, hνS⟩ := hν
  obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hS
  exact ⟨T, hT, hνS⟩

/-! ## `Loosen` and `Expel`: a pointwise substitution on a suffix

Both rules leave the delimiting views alone and replace each transition `f T`
of a chronicle suffix by `g T`.  All that is needed of the substitution is that
it preserves pointing downwards into the two memories and does not create local
messages. -/

/-- The target of a pointwise substitution on a chronicle suffix is a trace,
given that its memories are well-formed.  This covers `Loosen` and `Expel`. -/
theorem isTrace_of_map {A : Type u} {α ω : View Loc} {r : A} {c₁ c₂ : Chro Loc Val}
    {l m : List (Transition Loc Val)} {f g : Transition Loc Val → Transition Loc Val}
    (h₁ : c₁.toList = l ++ m.map f) (h₂ : c₂.toList = l ++ m.map g)
    (ho : ∀ S ∈ m, ∀ κ : View Loc, PointsDownInto κ (f S).opening →
      PointsDownInto κ (g S).opening)
    (hc : ∀ S ∈ m, ∀ κ : View Loc, PointsDownInto κ (f S).closing →
      PointsDownInto κ (g S).closing)
    (hown : ∀ S ∈ m, (g S).own ⊆ (f S).own)
    (hτ : IsTrace (⟨α, c₁, ω, r⟩ : PreTrace Loc Val A))
    (hwf : ∀ T ∈ c₂.toList, T.WF) :
    IsTrace (⟨α, c₂, ω, r⟩ : PreTrace Loc Val A) where
  wf := hwf
  mono := hτ.mono
  openPts := by
    have hop := hτ.openPts
    change PointsDownInto α (Chro.o c₁) at hop
    change PointsDownInto α (Chro.o c₂)
    rw [Chro.o, h₁] at hop
    rw [Chro.o, h₂]
    cases l with
    | cons T l' => simpa using hop
    | nil =>
        cases m with
        | nil => exact absurd (by simp [h₁]) c₁.toList_ne_nil
        | cons S m' =>
            simp only [List.nil_append, List.map_cons, listO_cons] at hop ⊢
            exact ho S (by simp) α hop
  closePts := by
    have hcl := hτ.closePts
    change PointsDownInto ω (Chro.c c₁) at hcl
    change PointsDownInto ω (Chro.c c₂)
    rw [Chro.c, h₁] at hcl
    rw [Chro.c, h₂]
    rcases List.eq_nil_or_concat' m with rfl | ⟨m', S, rfl⟩
    · simpa using hcl
    · rw [List.map_append, List.map_cons, List.map_nil, ← List.append_assoc,
        listC_append, listC_singleton] at hcl ⊢
      exact hc S (by simp) ω hcl
  own := by
    intro ν hν
    refine hτ.own ν ?_
    rw [Chro.own_eq_listOwn, h₂, listOwn_append] at hν
    rw [Chro.own_eq_listOwn, h₁, listOwn_append]
    rcases hν with hν | hν
    · exact Or.inl hν
    · obtain ⟨S, hS, hνS⟩ := mem_listOwn_map hν
      exact Or.inr ⟨f S, List.mem_map_of_mem hS, hown S hS hνS⟩

/-- **Loosen** takes traces to traces, given that the target's memories are
well-formed. -/
theorem isTrace_loosen {A : Type u} {α ω : View Loc} {r : A} {c₁ c₂ : Chro Loc Val}
    {l m : List (Transition Loc Val)} {ν ε : Msg Loc Val}
    (hle : Msg.LeVw ν ε) (hfε : listFree ε m) (hfν : listFree ν m)
    (h₁ : c₁.toList = l ++ m.map (Transition.insertMsg ε))
    (h₂ : c₂.toList = l ++ m.map (Transition.insertMsg ν))
    (hτ : IsTrace (⟨α, c₁, ω, r⟩ : PreTrace Loc Val A))
    (hwf : ∀ T ∈ c₂.toList, T.WF) :
    IsTrace (⟨α, c₂, ω, r⟩ : PreTrace Loc Val A) :=
  isTrace_of_map h₁ h₂
    (fun _ _ κ hκ ↦ hκ.subst_insert hle.lc_eq hle.t_eq hle.vw_le)
    (fun _ _ κ hκ ↦ hκ.subst_insert hle.lc_eq hle.t_eq hle.vw_le)
    (fun S hS ↦ by
      rw [Transition.insertMsg_own (hfν S hS).2, Transition.insertMsg_own (hfε S hS).2])
    hτ hwf

/-- **Expel** takes traces to traces, given that the target's memories are
well-formed. -/
theorem isTrace_expel {A : Type u} {α ω : View Loc} {r : A} {c₁ c₂ : Chro Loc Val}
    {l m : List (Transition Loc Val)} {ν ε : Msg Loc Val}
    (hdt : Msg.Dovetail ν ε) (hfs : listFree (ε.setI ν.i hdt.i_lt_t) m)
    (hfν : listFree ν m) (hfε : listFree ε m)
    (h₁ : c₁.toList = l ++ m.map (Transition.insertMsg (ε.setI ν.i hdt.i_lt_t)))
    (h₂ : c₂.toList = l ++ m.map (fun T ↦ (T.insertMsg ε).insertMsg ν))
    (hτ : IsTrace (⟨α, c₁, ω, r⟩ : PreTrace Loc Val A))
    (hwf : ∀ T ∈ c₂.toList, T.WF) :
    IsTrace (⟨α, c₂, ω, r⟩ : PreTrace Loc Val A) := by
  have hne : ν ≠ ε := fun hc ↦ by
    rw [hc] at hdt; exact absurd hdt.2.1 (ne_of_gt ε.i_lt_t)
  refine isTrace_of_map h₁ h₂ (fun _ _ κ hκ ↦ ?_) (fun _ _ κ hκ ↦ ?_) (fun S hS ↦ ?_) hτ hwf
  · simp only [Transition.insertMsg_opening] at hκ ⊢
    exact (PointsDownInto.subst_insert (ν := ε) hκ rfl rfl (le_refl _)).mono
      (Set.subset_insert _ _)
  · simp only [Transition.insertMsg_closing] at hκ ⊢
    exact (PointsDownInto.subst_insert (ν := ε) hκ rfl rfl (le_refl _)).mono
      (Set.subset_insert _ _)
  · rw [Transition.insertMsg_own (by
      simp only [Transition.insertMsg_closing, Set.mem_insert_iff, not_or]
      exact ⟨hne, (hfν S hS).2⟩), Transition.insertMsg_own (hfε S hS).2,
      Transition.insertMsg_own (hfs S hS).2]

/-! ## `Condense`

The only rule of the paper that is not local to the chronicle: `ε` is deleted
from the suffix and the *whole* pre-trace is pulled along it.  Three separate
facts are needed, each supplied by `Isotope/Elgot/RA/Pull.lean`: Lemma 7.6 for
the delimiting views (`View.pull_le_pull_of_scattered`), the transport of
pointing downwards into the pulled memories (`PointsDownInto.pull`,
`PointsDownInto.pull_all`), and the free-segment invariant for the trace
condition on local messages (`Scattered.segFree_of_pull`,
`Scattered.notMem_of_pull`). -/

/-- **Condense** takes traces to traces, given that the target's memories are
well-formed. -/
theorem isTrace_condense {A : Type u} {α ω : View Loc} {r : A} {c₁ c₂ : Chro Loc Val}
    {l m : List (Transition Loc Val)} {ν ε : Msg Loc Val}
    (hde : Msg.DovetailEq ν ε) (hfν : listFree ν m) (hfε : listFree ε m)
    (h₁ : c₁.toList = l ++ m.map (fun T ↦ (T.insertMsg ε).insertMsg ν))
    (h₂ : c₂.toList = (l ++ m.map (Transition.insertMsg ν)).map (Transition.pull ε))
    (hτ : IsTrace (⟨α, c₁, ω, r⟩ : PreTrace Loc Val A))
    (hwf : ∀ T ∈ c₂.toList, T.WF) :
    IsTrace (⟨View.pull ε α, c₂, View.pull ε ω, r⟩ : PreTrace Loc Val A) := by
  have hνne : ν ≠ ε := fun hc ↦ by
    rw [hc] at hde; exact absurd hde.1.2.1 (ne_of_gt ε.i_lt_t)
  have h₂' : c₂.toList = l.map (Transition.pull ε)
      ++ m.map (fun T ↦ (T.insertMsg ν).pull ε) := by
    rw [h₂, List.map_append, List.map_map]; rfl
  have hsc₂ : Scattered c₂.c := scattered_c_of_wf hwf
  have hα : PointsInto α c₁.c := hτ.openPts.toPointsInto.mono hτ.o_sub_c
  have hω : PointsInto ω c₁.c := hτ.closePts.toPointsInto
  have hwf₁ : WellFormed c₁.c := by
    obtain ⟨T, hT, hc⟩ := listC_mem c₁.toList c₁.toList_ne_nil
    change WellFormed (listC c₁.toList); rw [hc]; exact (hτ.wf T hT).closing
  -- the closing memories, split on whether the rewritten suffix is empty
  have hlast : (∃ T ∈ l, c₁.c = T.closing ∧ c₂.c = Memory.pull ε T.closing) ∨
      (∃ S ∈ m, c₁.c = insert ν (insert ε S.closing) ∧
        c₂.c = Memory.pull ε (insert ν S.closing)) := by
    rcases List.eq_nil_or_concat' m with rfl | ⟨m', S, rfl⟩
    · have hl : l ≠ [] := by
        intro hc; exact c₁.toList_ne_nil (by rw [h₁, hc]; rfl)
      obtain ⟨T, hT, hc1, hc2⟩ := listC_map (h := Transition.pull ε) l hl
      refine Or.inl ⟨T, hT, ?_, ?_⟩
      · change listC c₁.toList = _; rw [h₁]; simpa using hc1
      · change listC c₂.toList = _; rw [h₂']; simpa using hc2
    · refine Or.inr ⟨S, by simp, ?_, ?_⟩
      · change listC c₁.toList = _
        rw [h₁]
        simp only [List.map_append, List.map_cons, List.map_nil, ← List.append_assoc,
          listC_append, listC_singleton]
        rfl
      · change listC c₂.toList = _
        rw [h₂']
        simp only [List.map_append, List.map_cons, List.map_nil, ← List.append_assoc,
          listC_append, listC_singleton]
        rfl
  have hkey : Memory.pull ε (c₁.c \ {ε}) ⊆ c₂.c := by
    rcases hlast with ⟨T, hT, hc1, hc2⟩ | ⟨S, hS, hc1, hc2⟩
    · rw [hc1, hc2]; exact Memory.pull_mono (fun _ hx ↦ hx.1)
    · rw [hc1, hc2, Set.insert_insert_diff hνne (hfε S hS).2]
  have hmono : ∀ κ σ : View Loc, PointsInto κ c₁.c → PointsInto σ c₁.c → κ ≤ σ →
      View.pull ε κ ≤ View.pull ε σ := fun _ _ hκ hσ hle ↦
    View.pull_le_pull_of_scattered hsc₂ hkey hκ hσ hle
  refine ⟨hwf, ?_, hmono α ω hα hω hτ.mono, ?_, ?_⟩
  · -- the opening memory
    have hop := hτ.openPts
    change PointsDownInto α (Chro.o c₁) at hop
    change PointsDownInto (View.pull ε α) (Chro.o c₂)
    have hwfo : WellFormed (Chro.o c₁) := (hτ.wf c₁.first c₁.first_mem).opening
    cases l with
    | cons T l' =>
        have hc1 : Chro.o c₁ = T.opening := by rw [Chro.o, h₁]; rfl
        have hc2 : Chro.o c₂ = Memory.pull ε T.opening := by rw [Chro.o, h₂']; rfl
        rw [hc2]
        refine PointsDownInto.pull_all (by rw [← hc1]; exact hwfo) ?_ (by rw [← hc1]; exact hop)
        have : (Transition.pull ε T) ∈ c₂.toList := by rw [h₂']; simp
        exact (hwf _ this).opening.scattered
    | nil =>
        cases m with
        | nil => exact absurd (by simp [h₁]) c₁.toList_ne_nil
        | cons S m' =>
            have hc1 : Chro.o c₁ = insert ν (insert ε S.opening) := by
              rw [Chro.o, h₁]; rfl
            have hc2 : Chro.o c₂ = Memory.pull ε (insert ν S.opening) := by
              rw [Chro.o, h₂']; rfl
            rw [hc2, ← Set.insert_insert_diff hνne (hfε S (by simp)).1, ← hc1]
            refine PointsDownInto.pull hwfo hsc₂ ?_ ?_ hop
            · exact subset_trans (Memory.pull_mono
                (Set.diff_subset_diff_left hτ.o_sub_c)) hkey
            · exact fun _ ↦ ⟨ν, by rw [hc1]; exact Set.mem_insert _ _, hde.1⟩
  · -- the closing memory
    have hcl := hτ.closePts
    change PointsDownInto ω (Chro.c c₁) at hcl
    change PointsDownInto (View.pull ε ω) (Chro.c c₂)
    rcases hlast with ⟨T, hT, hc1, hc2⟩ | ⟨S, hS, hc1, hc2⟩
    · change Chro.c c₂ = _ at hc2
      rw [hc2]
      refine PointsDownInto.pull_all ?_ ?_ (by rw [← hc1] at *; exact hcl)
      · rw [← hc1]; exact hwf₁
      · rw [← hc2]; exact hsc₂
    · rw [hc2, ← Set.insert_insert_diff hνne (hfε S hS).2, ← hc1]
      refine PointsDownInto.pull hwf₁ hsc₂ hkey (fun _ ↦ ?_) hcl
      exact ⟨ν, by rw [hc1]; exact Set.mem_insert _ _, hde.1⟩
  · -- the local messages
    have hownsub : Chro.own c₂ ⊆ Memory.pull ε (Chro.own c₁) := by
      rw [Chro.own_eq_listOwn, Chro.own_eq_listOwn, h₁, h₂', listOwn_append, listOwn_append]
      rintro x (hx | hx)
      · obtain ⟨T, hT, hxT⟩ := mem_listOwn_map hx
        obtain ⟨y, hy, rfl⟩ := Transition.pull_own_sub ε T hxT
        exact ⟨y, Or.inl ⟨T, hT, hy⟩, rfl⟩
      · obtain ⟨S, hS, hxS⟩ := mem_listOwn_map hx
        obtain ⟨y, hy, rfl⟩ := Transition.pull_own_sub ε (S.insertMsg ν) hxS
        rw [Transition.insertMsg_own (hfν S hS).2] at hy
        refine ⟨y, Or.inr ⟨(S.insertMsg ε).insertMsg ν, List.mem_map_of_mem hS, ?_⟩, rfl⟩
        rw [Transition.insertMsg_own (by
          simp only [Transition.insertMsg_closing, Set.mem_insert_iff, not_or]
          exact ⟨hνne, (hfν S hS).2⟩), Transition.insertMsg_own (hfε S hS).2]
        exact hy
    intro x hx
    obtain ⟨ϑ, hϑ, rfl⟩ := hownsub hx
    obtain ⟨h1, h2, h3⟩ := hτ.own ϑ hϑ
    change α ≤ ϑ.vw at h1
    change ϑ.vw ≤ ω at h2
    change α ϑ.lc < ϑ.t at h3
    have hϑc : ϑ ∈ c₁.c := hτ.own_sub_c hϑ
    have hϑp : PointsInto ϑ.vw c₁.c := hwf₁.causal.1.2 ϑ hϑc
    refine ⟨hmono α ϑ.vw hα hϑp h1, hmono ϑ.vw ω hϑp hω h2, ?_⟩
    -- the strict inequality: this is where the free segment is used
    change View.pull ε α (Msg.pull ε ϑ).lc < (Msg.pull ε ϑ).t
    rw [Msg.pull_lc]
    by_cases hlc : ϑ.lc = ε.lc
    · by_cases hk : α ε.lc = ε.i
      · rw [hlc, View.pull_lc_of_eq hk]
        obtain ⟨ϖ, hϖ, hlcϖ, hpϖ⟩ := hα ε.lc
        have htϖ : ϖ.t = ε.i := by rw [← hpϖ, hlcϖ, hk]
        have hϖne : ϖ ≠ ε := fun hcc ↦ by
          rw [hcc] at htϖ; exact absurd htϖ (ne_of_gt ε.i_lt_t)
        have hϑne : ϑ ≠ ε := by
          intro hc
          refine Scattered.notMem_of_pull hsc₂ (hkey ⟨ϖ, ⟨hϖ, hϖne⟩, rfl⟩) hlcϖ htϖ ?_
          have hmem : Msg.pull ε ϑ ∈ Chro.own c₂ := hx
          rw [hc, Msg.pull_self] at hmem
          exact own_sub_c_of_wf hwf hmem
        have hfree := Scattered.segFree_of_pull hwf₁.scattered hsc₂ hkey hϖ hlcϖ htϖ
          hϑc hlc hϑne
        have hgt : ε.i < ϑ.t := by rw [← hk, ← hlc]; exact h3
        have hne : ϑ.t ≠ ε.i := ne_of_gt hgt
        rw [Msg.pull_t_of_ne_i hlc hne]
        rcases lt_or_ge ε.t ϑ.t with h | h
        · exact h
        · exact absurd ⟨hgt, h⟩ hfree
      · rw [hlc, View.pull_lc_of_ne hk, ← hlc]
        exact lt_of_lt_of_le h3 (Msg.le_pull_t ε ϑ)
    · rw [View.pull_of_ne hlc]
      exact lt_of_lt_of_le h3 (Msg.le_pull_t ε ϑ)

end Isotope.Elgot.RA
