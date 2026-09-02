import Isotope.Elgot.RA.Trace

/-!
# Substitution and pulling: the toolbox for the `𝔤` rules

The three `𝔤` rules of Dvir, Kammar and Lahav (`release-acquire`, journal
§7.3, pp.30–33) rewrite a trace by *substituting* for an environment message:
`Loosen` replaces `ε` by a weaker `ν ≤vw ε`, `Expel` replaces `ε[i↦ν.i]` by the
dovetailing pair `ν, ε`, and `Condense` deletes `ε` and pulls the whole
pre-trace along it.  Reasoning about any of them — Proposition 7.5, Rewrite
Castling (Lemma 8.3), Lemma F.1 — needs the same handful of facts about how
the trace conditions survive such a substitution.  This file collects them.

## What is transcribed and what is ours

* `View.pull_le_pull_of_scattered` is the paper's **Lemma 7.6** (journal p.33)
  together with the argument the paper gives for *why its hypotheses hold in
  practice* — "neither `κ` nor `σ` point into the interior of `ε.seg`, because
  no message has a timestamp there" (journal p.34).  We fold the two into one
  statement, since the side condition is never available on its own.  The
  bare form of Lemma 7.6 is `View.pull_le_pull` in
  `Isotope/Elgot/RA/State.lean`.
* Everything else here is **ours**: the paper states no memory-level lemmas.

None of these lemmas mentions a rewrite rule, so nothing here depends on the
reconstruction of the paper's chronicle notation `η ⊎ {ε}`.
-/

universe u

namespace Isotope.Elgot.RA

variable {Loc Val : Type}

/-! ## Messages a view cannot tell apart

`Loosen` and `Expel` both replace a message by one with the same location and
final timestamp and a smaller carried view.  A view that points downwards to
the old message points downwards to the new one. -/

namespace Msg

theorem LeVw.lc_eq {ν ε : Msg Loc Val} (h : LeVw ν ε) : ν.lc = ε.lc := h.1

theorem LeVw.t_eq {ν ε : Msg Loc Val} (h : LeVw ν ε) : ν.t = ε.t :=
  (seg_eq_iff.mp h.2.2.1).2

theorem LeVw.vw_le {ν ε : Msg Loc Val} (h : LeVw ν ε) : ν.vw ≤ ε.vw := h.2.2.2

end Msg

/-- A view that points downwards to `ε` points downwards to any message with
the same location and final timestamp and a smaller view. -/
theorem PointsDownTo.subst {κ : View Loc} {ν ε : Msg Loc Val} (h : PointsDownTo κ ε)
    (hlc : ν.lc = ε.lc) (ht : ν.t = ε.t) (hvw : ν.vw ≤ ε.vw) : PointsDownTo κ ν :=
  ⟨show κ ν.lc = ν.t by rw [hlc, ht]; exact h.1, le_trans hvw h.2⟩

/-- Pointing downwards into a memory survives replacing one of its messages by
a weaker one at the same location and final timestamp: the fact the paper
appeals to as "pointing downwards into a memory is stable under 'loosening' a
message within the memory" (journal Appendix F, p.62). -/
theorem PointsDownInto.subst_insert {κ : View Loc} {X : Memory Loc Val} {ν ε : Msg Loc Val}
    (h : PointsDownInto κ (insert ε X)) (hlc : ν.lc = ε.lc) (ht : ν.t = ε.t)
    (hvw : ν.vw ≤ ε.vw) : PointsDownInto κ (insert ν X) := by
  intro ℓ
  obtain ⟨ϑ, hϑ, hl, hp⟩ := h ℓ
  rcases hϑ with rfl | hϑ
  · exact ⟨ν, Set.mem_insert _ _, by rw [hlc]; exact hl, hp.subst hlc ht hvw⟩
  · exact ⟨ϑ, Set.mem_insert_of_mem _ hϑ, hl, hp⟩

/-! ## Free interiors

A scattered memory has at most one message per location per segment, so no
message's timestamp can lie in the *interior* `ε.seg \ {ε.t}` of another's
segment.  This is the "no message has a timestamp there" of journal p.34. -/

/-- In a scattered memory, a message's timestamp never lies in the interior of
another message's segment. -/
theorem Scattered.t_notMem_interior {μ : Memory Loc Val} (h : Scattered μ)
    {ε ϑ : Msg Loc Val} (hε : ε ∈ μ) (hϑ : ϑ ∈ μ) (hlc : ϑ.lc = ε.lc)
    (hne : ϑ.t ≠ ε.t) : ϑ.t ∉ ε.seg := fun hmem ↦
  hne (congrArg Msg.t (h ϑ hϑ ε hε hlc ⟨ϑ.t, ϑ.t_mem_seg, hmem⟩))

/-! ## Pulling a message -/

namespace Msg

@[simp] theorem pull_t_of_ne {ε ϑ : Msg Loc Val} (h : ϑ.lc ≠ ε.lc) :
    (Msg.pull ε ϑ).t = ϑ.t := View.pull_of_ne h

theorem vw_lc_of_eq {ε ϑ : Msg Loc Val} (h : ϑ.lc = ε.lc) : ϑ.vw ε.lc = ϑ.t := by
  rw [← h]; rfl

theorem pull_t_of_eq_i {ε ϑ : Msg Loc Val} (h : ϑ.lc = ε.lc) (h₂ : ϑ.t = ε.i) :
    (Msg.pull ε ϑ).t = ε.t := by
  change View.pull ε ϑ.vw ϑ.lc = ε.t
  rw [h]
  exact View.pull_lc_of_eq (by rw [vw_lc_of_eq h, h₂])

theorem pull_t_of_ne_i {ε ϑ : Msg Loc Val} (h : ϑ.lc = ε.lc) (h₂ : ϑ.t ≠ ε.i) :
    (Msg.pull ε ϑ).t = ϑ.t := by
  change View.pull ε ϑ.vw ϑ.lc = ϑ.t
  rw [h]
  rw [View.pull_lc_of_ne (by rw [vw_lc_of_eq h]; exact h₂), vw_lc_of_eq h]

/-- A message whose view does not point at `ε`'s initial timestamp is fixed by
pulling along `ε`. -/
theorem pull_eq_self {ε ϑ : Msg Loc Val} (h : ϑ.vw ε.lc ≠ ε.i) : Msg.pull ε ϑ = ϑ := by
  cases ϑ with
  | mk lc vl i vw lt => simp only [Msg.pull, View.pull_eq_self h]

/-- Pulling fixes the message being pulled along. -/
@[simp] theorem pull_self (ε : Msg Loc Val) : Msg.pull ε ε = ε :=
  pull_eq_self (by rw [vw_lc_of_eq rfl]; exact ne_of_gt ε.i_lt_t)

end Msg

/-- **Lemma 7.6** (journal p.33), in the form the model uses it.

The paper's statement carries the side condition that neither view points into
the *interior* of `ε.seg`; it then argues (p.34) that the condition holds
"because no message has a timestamp there".  Here the two are combined: it
suffices that both views point into a memory `μ` whose messages other than `ε`
survive the pull into some scattered memory `ρ` — which is exactly what the
target of a `Condense` rewrite supplies.  The bare form of the paper's lemma is
`View.pull_le_pull`. -/
theorem View.pull_le_pull_of_scattered {ε : Msg Loc Val} {μ ρ : Memory Loc Val}
    (hsc : Scattered ρ) (hsub : Memory.pull ε (μ \ {ε}) ⊆ ρ)
    {κ σ : View Loc} (hκ : PointsInto κ μ) (hσ : PointsInto σ μ) (h : κ ≤ σ) :
    View.pull ε κ ≤ View.pull ε σ := by
  intro ℓ
  by_cases hℓ : ℓ = ε.lc
  · subst hℓ
    by_cases hk : κ ε.lc = ε.i
    · rw [View.pull_lc_of_eq hk]
      by_cases hs : σ ε.lc = ε.i
      · rw [View.pull_lc_of_eq hs]
      · rw [View.pull_lc_of_ne hs]
        by_contra hlt
        rw [not_le] at hlt
        have hgt : ε.i < σ ε.lc := lt_of_le_of_ne (hk ▸ h ε.lc) (Ne.symm hs)
        obtain ⟨ϑ, hϑ, hϑl, hϑp⟩ := hσ ε.lc
        obtain ⟨ϑ', hϑ', hϑl', hϑp'⟩ := hκ ε.lc
        have hϑt : ϑ.t = σ ε.lc := by rw [← hϑp, hϑl]
        have hϑt' : ϑ'.t = ε.i := by rw [← hϑp', hϑl', hk]
        have hne : ϑ ≠ ε := fun hc ↦ by
          rw [hc] at hϑt; exact absurd hϑt (ne_of_gt hlt)
        have hne' : ϑ' ≠ ε := fun hc ↦ by
          rw [hc] at hϑt'; exact absurd hϑt'.symm (ne_of_lt ε.i_lt_t)
        have hmem : Msg.pull ε ϑ ∈ ρ := hsub ⟨ϑ, ⟨hϑ, hne⟩, rfl⟩
        have hmem' : Msg.pull ε ϑ' ∈ ρ := hsub ⟨ϑ', ⟨hϑ', hne'⟩, rfl⟩
        have ht : (Msg.pull ε ϑ).t = ϑ.t :=
          Msg.pull_t_of_ne_i hϑl (by rw [hϑt]; exact ne_of_gt hgt)
        have ht' : (Msg.pull ε ϑ').t = ε.t := Msg.pull_t_of_eq_i hϑl' hϑt'
        have hseg' : ϑ.t ∈ (Msg.pull ε ϑ').seg := by
          refine ⟨?_, ?_⟩
          · change (Msg.pull ε ϑ').i < ϑ.t
            exact lt_trans (by simpa [hϑt'] using ϑ'.i_lt_t) (by rw [hϑt]; exact hgt)
          · rw [ht']; exact le_of_lt (hϑt ▸ hlt)
        have heq : Msg.pull ε ϑ = Msg.pull ε ϑ' :=
          hsc _ hmem _ hmem' (by simp [hϑl, hϑl']) ⟨ϑ.t, ht ▸ (Msg.pull ε ϑ).t_mem_seg, hseg'⟩
        have hfin : ϑ.t = ε.t := by rw [← ht, heq, ht']
        rw [hϑt] at hfin
        exact absurd hfin (ne_of_lt hlt)
    · rw [View.pull_lc_of_ne hk]
      by_cases hs : σ ε.lc = ε.i
      · rw [View.pull_lc_of_eq hs]
        exact le_trans (hs ▸ h ε.lc) (le_of_lt ε.i_lt_t)
      · rw [View.pull_lc_of_ne hs]; exact h ε.lc
  · rw [View.pull_of_ne hℓ, View.pull_of_ne hℓ]; exact h ℓ

/-- Pointing downwards into a memory survives a `Condense`: the pulled view
points downwards into the pulled memory with `ε` deleted.  A view that pointed
to `ε` ends up pointing to the pull of a message `ν` that dovetails into it —
which is why the `Condense` rule may only delete a message that something
dovetails into. -/
theorem PointsDownInto.pull {ε : Msg Loc Val} {μ ρ : Memory Loc Val}
    (hwf : WellFormed μ) (hsc : Scattered ρ) (hsub : Memory.pull ε (μ \ {ε}) ⊆ ρ)
    (hν : ε ∈ μ → ∃ ν ∈ μ, Msg.Dovetail ν ε) {κ : View Loc} (h : PointsDownInto κ μ) :
    PointsDownInto (View.pull ε κ) (Memory.pull ε (μ \ {ε})) := by
  have key : ∀ ϑ ∈ μ, ϑ.vw ≤ κ → View.pull ε ϑ.vw ≤ View.pull ε κ := fun ϑ hϑ hle ↦
    View.pull_le_pull_of_scattered hsc hsub (hwf.causal.1.2 ϑ hϑ) h.toPointsInto hle
  have hpt : ∀ ϑ : Msg Loc Val, PointsTo κ ϑ →
      View.pull ε κ (Msg.pull ε ϑ).lc = (Msg.pull ε ϑ).t := by
    intro ϑ hp
    have hϑt : ϑ.t = κ ϑ.lc := hp.symm
    rw [Msg.pull_lc]
    by_cases hℓ : ϑ.lc = ε.lc
    · rw [hℓ]
      by_cases hk : κ ε.lc = ε.i
      · rw [View.pull_lc_of_eq hk, Msg.pull_t_of_eq_i hℓ (by rw [hϑt, hℓ]; exact hk)]
      · rw [View.pull_lc_of_ne hk,
          Msg.pull_t_of_ne_i hℓ (by rw [hϑt, hℓ]; exact hk), hϑt, hℓ]
    · rw [View.pull_of_ne hℓ, Msg.pull_t_of_ne hℓ, hϑt]
  intro ℓ
  obtain ⟨ϑ, hϑ, hϑl, hϑp, hϑv⟩ := h ℓ
  by_cases he : ϑ = ε
  · obtain ⟨ν, hνμ, hdt⟩ := hν (he ▸ hϑ)
    have hκ : κ ε.lc = ε.t := by rw [← he]; exact hϑp
    have hεv : ε.vw ≤ κ := by rw [← he]; exact hϑv
    have hνne : ν ≠ ε := fun hc ↦ by
      rw [hc] at hdt; exact absurd hdt.2.1 (ne_of_gt ε.i_lt_t)
    refine ⟨Msg.pull ε ν, ⟨ν, ⟨hνμ, hνne⟩, rfl⟩, by rw [Msg.pull_lc, hdt.1, ← he, hϑl], ?_, ?_⟩
    · change View.pull ε κ (Msg.pull ε ν).lc = (Msg.pull ε ν).t
      rw [Msg.pull_lc, hdt.1,
        View.pull_lc_of_ne (by rw [hκ]; exact ne_of_gt ε.i_lt_t),
        Msg.pull_t_of_eq_i hdt.1 hdt.2.1, hκ]
    · exact key ν hνμ (le_trans hdt.2.2 hεv)
  · exact ⟨Msg.pull ε ϑ, ⟨ϑ, ⟨hϑ, he⟩, rfl⟩, by rw [Msg.pull_lc, hϑl],
      hpt ϑ hϑp, key ϑ hϑ hϑv⟩

/-! ## Well-formedness of an intermediate memory

Castling constructs memories that are *sandwiched* between memories of the
traces at either end of the rewrite sequence.  Scatteredness, finiteness and
the cycle condition all descend to subsets; only causal connectedness has to be
supplied. -/

/-- A subset of a well-formed memory into which all of its own messages point
downwards is well-formed.  Note that the cycle condition descends to subsets:
a cycle of the smaller memory is a cycle of the larger, and minimality at a
location is inherited. -/
theorem WellFormed.of_subset {Y Z : Memory Loc Val} (hZ : WellFormed Z) (hYZ : Y ⊆ Z)
    (hne : Y.Nonempty) (hpd : ∀ ν ∈ Y, PointsDownInto ν.vw Y) : WellFormed Y where
  finite := hZ.finite.subset hYZ
  nonempty := hne
  causal := ⟨⟨fun ν hν ε hε hlc hi ↦ hZ.scattered ν (hYZ hν) ε (hYZ hε) hlc hi,
    fun ν hν ↦ (hpd ν hν).toPointsInto⟩, hpd⟩
  cycles := by
    intro ν hν hcyc
    have hcyc' : Relation.TransGen (Gph Z) ν ν :=
      hcyc.mono (fun a b hab ↦ ⟨hYZ hab.1, hYZ hab.2.1, hab.2.2⟩)
    exact ⟨hν, fun ε hε hlc ↦ (hZ.cycles ν (hYZ hν) hcyc').2 ε (hYZ hε) hlc⟩

/-! ## Every memory of a trace is contained in its closing memory

The transitions of a trace satisfy `μ ⊆ ρ` and the chronicle is adjacent, so
the memories of a chronicle form a `⊆`-chain.  This is what makes the closing
memory the right place to check scatteredness. -/

theorem listC_sup : ∀ (l : List (Transition Loc Val)), List.IsChain Adj l →
    (∀ T ∈ l, T.opening ⊆ T.closing) → ∀ T ∈ l, T.closing ⊆ listC l
  | [], _, _, _, hT => absurd hT (by simp)
  | [S], _, _, T, hT => by
      rw [List.mem_singleton] at hT; subst hT; exact subset_refl _
  | S :: U :: r, hc, hsub, T, hT => by
      have ih := listC_sup (U :: r) (List.isChain_cons_cons.mp hc).2
        (fun V hV ↦ hsub V (by simp [hV]))
      rw [listC_cons_cons]
      rcases List.mem_cons.mp hT with rfl | hT
      · exact subset_trans (List.isChain_cons_cons.mp hc).1
          (subset_trans (hsub U (by simp)) (ih U (by simp)))
      · exact ih T hT

/-- Every memory of a trace's chronicle is contained in its closing memory. -/
theorem IsTrace.closing_sub_c {A : Type u} {τ : PreTrace Loc Val A} (hτ : IsTrace τ)
    {T : Transition Loc Val} (hT : T ∈ τ.ch.toList) : T.closing ⊆ τ.ch.c :=
  listC_sup τ.ch.toList τ.ch.chain_toList (fun S hS ↦ (hτ.wf S hS).sub) T hT

theorem IsTrace.opening_sub_c {A : Type u} {τ : PreTrace Loc Val A} (hτ : IsTrace τ)
    {T : Transition Loc Val} (hT : T ∈ τ.ch.toList) : T.opening ⊆ τ.ch.c :=
  subset_trans (hτ.wf T hT).sub (hτ.closing_sub_c hT)

/-- The closing memory of a trace is well-formed, and hence scattered: this is
the memory against which the interior-freeness arguments are run. -/
theorem IsTrace.scattered_c {A : Type u} {τ : PreTrace Loc Val A} (hτ : IsTrace τ) :
    Scattered τ.ch.c := by
  obtain ⟨T, hT, hc⟩ := listC_mem τ.ch.toList τ.ch.toList_ne_nil
  change Scattered (listC τ.ch.toList)
  rw [hc]
  exact (hτ.wf T hT).closing.scattered

end Isotope.Elgot.RA
