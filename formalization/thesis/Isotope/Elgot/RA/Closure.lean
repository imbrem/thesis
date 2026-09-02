import Isotope.Elgot.RA.Rewrite

/-!
# `★`-closed sets of traces

Following Dvir, Kammar and Lahav (`release-acquire`), §7.2 of the journal
version: a set `U` of traces is `★`-closed when `τ ∈ U` and `τ →★ π ∈ Trace X`
imply `π ∈ U` — note the guard `π ∈ Trace X`, so rewriting out of the traces is
simply ignored.  `U★` is the least `★`-closed superset, here realized as
reachability under `TStep R`.

Everything in this file is uniform in the rule set `R`.  Closedness is a Horn
condition, so closed sets are stable under arbitrary unions and intersections;
`closure_iUnion` records the union case, which is what makes the
union-of-approximants iteration operator land in the carrier without re-closing.

The section on invariants is where the rule sets separate: the returned value is
preserved by every rule, `ξ.own` is preserved *exactly* only by `𝔠`, and
`ξ.own = ∅` is preserved by all of `𝔤𝔠` — the last is what the unit laws of
`Isotope/Elgot/RA/Monad.lean` run on.
-/

universe u

namespace Isotope.Elgot.RA

variable {Loc Val : Type} {R : RuleSet} {A : Type u}

/-- A set of pre-traces all of which are traces. -/
def IsTraceSet (S : Set (PreTrace Loc Val A)) : Prop := ∀ τ ∈ S, IsTrace τ

/-- `★`-closedness, for `★ = R`. -/
def Closed (R : RuleSet) (U : Set (PreTrace Loc Val A)) : Prop :=
  ∀ τ ∈ U, ∀ π, TStep R τ π → π ∈ U

/-- The `★`-closure `S★`: everything reachable from `S` by trace-preserving
`R`-rewrites. -/
def closure (R : RuleSet) (S : Set (PreTrace Loc Val A)) : Set (PreTrace Loc Val A) :=
  {π | ∃ τ ∈ S, Refines R τ π}

theorem mem_closure_iff {S : Set (PreTrace Loc Val A)} {π : PreTrace Loc Val A} :
    π ∈ closure R S ↔ ∃ τ ∈ S, Refines R τ π := Iff.rfl

theorem subset_closure {S : Set (PreTrace Loc Val A)} : S ⊆ closure R S :=
  fun τ hτ ↦ ⟨τ, hτ, Refines.refl τ⟩

theorem closure_mono {S T : Set (PreTrace Loc Val A)} (h : S ⊆ T) :
    closure R S ⊆ closure R T := fun _ ⟨τ, hτ, hr⟩ ↦ ⟨τ, h hτ, hr⟩

/-- Enlarging the rule set enlarges the closure: this is the whole content of
the paper's `G X ⊇ C X ⊇ A X` (journal §8.2, p.41). -/
theorem closure_mono_rules {R R' : RuleSet} (hR : R ⊆ R')
    (S : Set (PreTrace Loc Val A)) : closure R S ⊆ closure R' S :=
  fun _ ⟨τ, hτ, hr⟩ ↦ ⟨τ, hτ, hr.mono hR⟩

theorem Closed.mem_of_refines {U : Set (PreTrace Loc Val A)} (hU : Closed R U)
    {τ π : PreTrace Loc Val A} (hτ : τ ∈ U) (hr : Refines R τ π) : π ∈ U := by
  induction hr with
  | refl => exact hτ
  | tail _ hstep ih => exact hU _ ih _ hstep

theorem closure_subset_of_closed {S U : Set (PreTrace Loc Val A)} (hU : Closed R U)
    (h : S ⊆ U) : closure R S ⊆ U := fun _ ⟨_, hτ, hr⟩ ↦ hU.mem_of_refines (h hτ) hr

theorem closure_closed (R : RuleSet) (S : Set (PreTrace Loc Val A)) :
    Closed R (closure R S) :=
  fun _ ⟨τ, hτ, hr⟩ _ hstep ↦ ⟨τ, hτ, hr.tail hstep⟩

theorem Closed.closure_eq {U : Set (PreTrace Loc Val A)} (hU : Closed R U) :
    closure R U = U :=
  Set.Subset.antisymm (closure_subset_of_closed hU (subset_refl U)) subset_closure

theorem closure_idem (S : Set (PreTrace Loc Val A)) :
    closure R (closure R S) = closure R S := (closure_closed R S).closure_eq

theorem closed_empty : Closed R (∅ : Set (PreTrace Loc Val A)) :=
  fun _ h ↦ absurd h (by simp)

@[simp] theorem closure_empty : closure R (∅ : Set (PreTrace Loc Val A)) = ∅ := by
  ext π; simp [closure]

theorem closed_iUnion {ι : Sort*} {U : ι → Set (PreTrace Loc Val A)}
    (h : ∀ i, Closed R (U i)) : Closed R (⋃ i, U i) := by
  rintro τ hτ π hstep
  rw [Set.mem_iUnion] at hτ ⊢
  obtain ⟨i, hi⟩ := hτ
  exact ⟨i, h i _ hi _ hstep⟩

theorem closure_iUnion {ι : Sort*} (S : ι → Set (PreTrace Loc Val A)) :
    closure R (⋃ i, S i) = ⋃ i, closure R (S i) := by
  ext π
  simp only [mem_closure_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨τ, ⟨i, hi⟩, hr⟩; exact ⟨i, τ, hi, hr⟩
  · rintro ⟨i, τ, hi, hr⟩; exact ⟨τ, ⟨i, hi⟩, hr⟩

/-- Rewriting preserves trace-hood, by the guard in `TStep`. -/
theorem Refines.isTrace {τ π : PreTrace Loc Val A} (hr : Refines R τ π)
    (hτ : IsTrace τ) : IsTrace π := by
  induction hr with
  | refl => exact hτ
  | tail _ hstep _ => exact hstep.2

theorem IsTraceSet.closure {S : Set (PreTrace Loc Val A)} (h : IsTraceSet S) :
    IsTraceSet (_root_.Isotope.Elgot.RA.closure R S) :=
  fun _ ⟨_, hτ, hr⟩ ↦ hr.isTrace (h _ hτ)

/-! ## The returned value is preserved by every rule

Journal Table 2, p.30: "in presenting these closure rules we omit the return
value, because they all maintain it". -/

theorem Step.ret_eq {τ π : PreTrace Loc Val A} (h : Step R τ π) : τ.ret = π.ret := by
  cases h <;> rfl

theorem Refines.ret_eq {τ π : PreTrace Loc Val A} (h : Refines R τ π) : τ.ret = π.ret := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans hstep.1.ret_eq

/-! ## The local messages are a `𝔠`-rewriting invariant

Every `𝔠`-rewrite preserves `ξ.own` exactly.  `Stutter` inserts a transition
`⟨μ,μ⟩`, whose contribution is `μ \ μ = ∅`; `Mumble` replaces `⟨μ,ρ⟩⟨ρ,θ⟩` by
`⟨μ,θ⟩`, and `(ρ \ μ) ∪ (θ \ ρ) = θ \ μ` whenever `μ ⊆ ρ ⊆ θ`, which holds
because the transitions of a trace are well-formed.

⚠ This is **false** for the `𝔤` rules: `Loosen` and `Expel` change which
environment messages occur, and `Condense` maps every message through the pull.
What survives at `𝔤𝔠` is `own = ∅`; see the next section. -/

theorem ChroStep.own_eq {x : Rule} {c₁ c₂ : Chro Loc Val} (hx : x ∈ cRules)
    (h : ChroStep x c₁ c₂) (hwf : ∀ T ∈ c₁.toList, T.WF) : c₁.own = c₂.own := by
  cases h with
  | stutter _ _ l r μ h₁ h₂ =>
      simp only [Chro.own_eq_listOwn, h₁, h₂, listOwn_append, listOwn_cons,
        Transition.own, Set.diff_self, Set.empty_union]
  | mumble _ _ l r μ ρ θ h₁ h₂ =>
      have hμρ : μ ⊆ ρ := (hwf ⟨μ, ρ⟩ (by rw [h₁]; simp)).sub
      have hρθ : ρ ⊆ θ := (hwf ⟨ρ, θ⟩ (by rw [h₁]; simp)).sub
      simp only [Chro.own_eq_listOwn, h₁, h₂, listOwn_append, listOwn_cons,
        Transition.own]
      congr 1
      rw [← Set.union_assoc]
      congr 1
      ext ν
      simp only [Set.mem_union, Set.mem_diff]
      constructor
      · rintro (⟨hν, hn⟩ | ⟨hν, hn⟩)
        · exact ⟨hρθ hν, hn⟩
        · exact ⟨hν, fun hc ↦ hn (hμρ hc)⟩
      · rintro ⟨hν, hn⟩
        by_cases hr : ν ∈ ρ
        · exact Or.inl ⟨hr, hn⟩
        · exact Or.inr ⟨hν, hr⟩
  | loosen => simp at hx
  | expel => simp at hx
  | tighten => simp at hx
  | absorb => simp at hx

theorem Step.own_eq (hR : R ⊆ cRules) {τ π : PreTrace Loc Val A} (h : Step R τ π)
    (hτ : IsTrace τ) : τ.ch.own = π.ch.own := by
  cases h with
  | chro hx hc => exact hc.own_eq (hR hx) hτ.wf
  | forward _ _ => rfl
  | rewind _ _ => rfl
  | condense hx => exact absurd (hR hx) (by simp)
  | dilute hx => exact absurd (hR hx) (by simp)

theorem Refines.own_eq (hR : R ⊆ cRules) {τ π : PreTrace Loc Val A} (h : Refines R τ π)
    (hτ : IsTrace τ) : τ.ch.own = π.ch.own := by
  induction h with
  | refl => rfl
  | @tail b c hab hbc ih =>
      exact ih.trans (hbc.1.own_eq hR (Refines.isTrace hab hτ))

/-! ## Having no local messages is a `𝔤𝔠`-rewriting invariant

`ξ.own = ∅` says every transition of the chronicle is a *stutter*: `ρ ⊆ μ`, and
hence `ρ = μ` for a trace.  Each of the seven rules preserves it.  For the `𝔤`
rules this is exactly where the disjointness in the paper's `⊎` does the work:
the messages the rules manipulate are *environment* messages, absent from the
memories of the suffix they act on.

This invariant is what makes both unit laws of the monad go through uniformly
in `R`; the paper argues neither of them. -/

/-- Cancelling a message that is absent from the smaller memory. -/
theorem sub_of_insert_sub {ε : Msg Loc Val} {ρ μ : Memory Loc Val}
    (h : insert ε ρ ⊆ insert ε μ) (hε : ε ∉ ρ) : ρ ⊆ μ := by
  intro x hx
  rcases h (Set.mem_insert_of_mem _ hx) with rfl | hx'
  · exact absurd hx hε
  · exact hx'

theorem ChroStep.own_empty {x : Rule} {c₁ c₂ : Chro Loc Val} (hx : x ∈ gcTiAbRules)
    (h : ChroStep x c₁ c₂) (hown : c₁.own = ∅) : c₂.own = ∅ := by
  rw [Chro.own_eq_listOwn, listOwn_eq_empty_iff] at hown ⊢
  cases h with
  | stutter _ _ l r μ h₁ h₂ =>
      rw [h₁] at hown
      rw [h₂]
      intro T hT
      rcases List.mem_append.mp hT with hT | hT
      · exact hown T (List.mem_append.mpr (Or.inl hT))
      · rcases List.mem_cons.mp hT with rfl | hT
        · exact subset_refl _
        · exact hown T (List.mem_append.mpr (Or.inr hT))
  | mumble _ _ l r μ ρ θ h₁ h₂ =>
      rw [h₁] at hown
      rw [h₂]
      have hmr : (⟨μ, ρ⟩ : Transition Loc Val) ∈ l ++ (⟨μ, ρ⟩ : Transition Loc Val) ::
          (⟨ρ, θ⟩ : Transition Loc Val) :: r := by simp
      have hrt : (⟨ρ, θ⟩ : Transition Loc Val) ∈ l ++ (⟨μ, ρ⟩ : Transition Loc Val) ::
          (⟨ρ, θ⟩ : Transition Loc Val) :: r := by simp
      intro T hT
      rcases List.mem_append.mp hT with hT | hT
      · exact hown T (List.mem_append.mpr (Or.inl hT))
      · rcases List.mem_cons.mp hT with rfl | hT
        · exact (hown _ hrt).trans (hown _ hmr)
        · exact hown T (by simp [hT])
  | loosen _ _ l m ν ε hle hfε hfν h₁ h₂ =>
      rw [h₁] at hown
      rw [h₂]
      intro T hT
      rcases List.mem_append.mp hT with hT | hT
      · exact hown T (List.mem_append.mpr (Or.inl hT))
      · obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hT
        have hsrc := hown (S.insertMsg ε) (List.mem_append.mpr (Or.inr (List.mem_map_of_mem hS)))
        exact Set.insert_subset_insert (sub_of_insert_sub hsrc (hfε S hS).2)
  | expel _ _ l m ν ε hdt hfs hfν hfε h₁ h₂ =>
      rw [h₁] at hown
      rw [h₂]
      intro T hT
      rcases List.mem_append.mp hT with hT | hT
      · exact hown T (List.mem_append.mpr (Or.inl hT))
      · obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hT
        have hsrc := hown (S.insertMsg (ε.setI ν.i hdt.i_lt_t))
          (List.mem_append.mpr (Or.inr (List.mem_map_of_mem hS)))
        exact Set.insert_subset_insert
          (Set.insert_subset_insert (sub_of_insert_sub hsrc (hfs S hS).2))
  | tighten _ _ l m μ ρ ν ε _ hνμ _ _ _ _ _ h₁ h₂ =>
      rw [h₁] at hown
      exact absurd (hown ⟨μ, insert ν ρ⟩ (by simp) (Set.mem_insert _ _)) hνμ
  | absorb _ _ l m μ ρ ν ε _ hνμ _ _ _ _ _ _ _ _ h₁ h₂ =>
      rw [h₁] at hown
      exact absurd (hown ⟨μ, insert ν (insert ε ρ)⟩ (by simp) (Set.mem_insert _ _)) hνμ

/-- `Condense` merges a dovetailing pair, so its two messages are distinct. -/
theorem Msg.DovetailEq.ne {ν ε : Msg Loc Val} (h : Msg.DovetailEq ν ε) : ν ≠ ε := by
  rintro rfl
  exact absurd h.1.2.1 (ne_of_gt ν.i_lt_t)

theorem Step.own_empty (hR : R ⊆ gcTiAbRules) {τ π : PreTrace Loc Val A}
    (h : Step R τ π) (hown : τ.ch.own = ∅) : π.ch.own = ∅ := by
  cases h with
  | chro hx hc => exact hc.own_empty (hR hx) hown
  | forward _ _ => exact hown
  | rewind _ _ => exact hown
  | condense hx l m ν ε hde hfν hfε h₁ h₂ =>
      rw [Chro.own_eq_listOwn, listOwn_eq_empty_iff] at hown ⊢
      rw [h₁] at hown
      rw [h₂]
      have key : ∀ T ∈ l ++ m.map (Transition.insertMsg ν), T.closing ⊆ T.opening := by
        intro T hT
        rcases List.mem_append.mp hT with hT | hT
        · exact hown T (List.mem_append.mpr (Or.inl hT))
        · obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hT
          have hsrc := hown ((S.insertMsg ε).insertMsg ν)
            (List.mem_append.mpr (Or.inr (List.mem_map_of_mem hS)))
          have hν : ν ∉ insert ε S.closing := by
            simp only [Set.mem_insert_iff, not_or]
            exact ⟨hde.ne, (hfν S hS).2⟩
          exact Set.insert_subset_insert
            (sub_of_insert_sub (sub_of_insert_sub hsrc hν) (hfε S hS).2)
      intro T hT
      obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hT
      exact Memory.pull_mono (key S hS)
  | dilute hx => exact absurd (hR hx) (by simp)

theorem Refines.own_empty (hR : R ⊆ gcTiAbRules) {τ π : PreTrace Loc Val A}
    (h : Refines R τ π) (hown : τ.ch.own = ∅) : π.ch.own = ∅ := by
  induction h with
  | refl => exact hown
  | tail _ hstep ih => exact hstep.1.own_empty hR ih

/-! ## The `𝔤` rules preserve the length of the chronicle

Journal p.30 observes that the Null model invalidates both identity axioms,
"because only the traces from the left side of the inequation have two
transitions"; by Proposition 7.5 the same holds for the Generating model.  The
observation is exactly this length invariant, and
`Isotope/Elgot/RA/Concrete.lean` turns it into a formal counterexample. -/

theorem Step.length_eq (hR : R ⊆ gRules) {τ π : PreTrace Loc Val A} (h : Step R τ π) :
    τ.ch.toList.length = π.ch.toList.length := by
  cases h with
  | chro hx hc => exact hc.length_eq (hR hx)
  | forward hx _ => exact absurd (hR hx) (by simp)
  | rewind hx _ => exact absurd (hR hx) (by simp)
  | condense hx l m ν ε hde hfν hfε h₁ h₂ => rw [h₁, h₂]; simp
  | dilute hx => exact absurd (hR hx) (by simp)

theorem Refines.length_eq (hR : R ⊆ gRules) {τ π : PreTrace Loc Val A}
    (h : Refines R τ π) : τ.ch.toList.length = π.ch.toList.length := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (hstep.1.length_eq hR)


end Isotope.Elgot.RA
