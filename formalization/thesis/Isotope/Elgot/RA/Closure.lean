import Isotope.Elgot.RA.Rewrite

/-!
# `𝔠`-closed sets of traces

Following Dvir, Kammar and Lahav (`release-acquire`), §7.1 of the journal
version: a set `U` of traces is `★`-closed when `τ ∈ U` and `τ →★ π ∈ Trace X`
imply `π ∈ U` — note the guard `π ∈ Trace X`, so rewriting out of the traces is
simply ignored.  `U★` is the least `★`-closed superset, here realized as
reachability under `TStep`.

Closedness is a Horn condition, so closed sets are stable under arbitrary
unions and intersections; `closure_iUnion` records the union case, which is what
makes the union-of-approximants iteration operator land in the carrier without
re-closing.
-/

universe u

namespace Isotope.Elgot.RA

variable {Loc Val : Type} {A : Type u}

/-- A set of pre-traces all of which are traces. -/
def IsTraceSet (S : Set (PreTrace Loc Val A)) : Prop := ∀ τ ∈ S, IsTrace τ

/-- `𝔠`-closedness. -/
def Closed (U : Set (PreTrace Loc Val A)) : Prop := ∀ τ ∈ U, ∀ π, TStep τ π → π ∈ U

/-- The `𝔠`-closure `S★`: everything reachable from `S` by trace-preserving
rewrites. -/
def closure (S : Set (PreTrace Loc Val A)) : Set (PreTrace Loc Val A) :=
  {π | ∃ τ ∈ S, Refines τ π}

theorem mem_closure_iff {S : Set (PreTrace Loc Val A)} {π : PreTrace Loc Val A} :
    π ∈ closure S ↔ ∃ τ ∈ S, Refines τ π := Iff.rfl

theorem subset_closure {S : Set (PreTrace Loc Val A)} : S ⊆ closure S :=
  fun τ hτ ↦ ⟨τ, hτ, Refines.refl τ⟩

theorem closure_mono {S T : Set (PreTrace Loc Val A)} (h : S ⊆ T) :
    closure S ⊆ closure T := fun _ ⟨τ, hτ, hr⟩ ↦ ⟨τ, h hτ, hr⟩

theorem Closed.mem_of_refines {U : Set (PreTrace Loc Val A)} (hU : Closed U)
    {τ π : PreTrace Loc Val A} (hτ : τ ∈ U) (hr : Refines τ π) : π ∈ U := by
  induction hr with
  | refl => exact hτ
  | tail _ hstep ih => exact hU _ ih _ hstep

theorem closure_subset_of_closed {S U : Set (PreTrace Loc Val A)} (hU : Closed U)
    (h : S ⊆ U) : closure S ⊆ U := fun _ ⟨_, hτ, hr⟩ ↦ hU.mem_of_refines (h hτ) hr

theorem closure_closed (S : Set (PreTrace Loc Val A)) : Closed (closure S) :=
  fun _ ⟨τ, hτ, hr⟩ _ hstep ↦ ⟨τ, hτ, hr.tail hstep⟩

theorem Closed.closure_eq {U : Set (PreTrace Loc Val A)} (hU : Closed U) :
    closure U = U :=
  Set.Subset.antisymm (closure_subset_of_closed hU (subset_refl U)) subset_closure

theorem closure_idem (S : Set (PreTrace Loc Val A)) :
    closure (closure S) = closure S := (closure_closed S).closure_eq

theorem closed_empty : Closed (∅ : Set (PreTrace Loc Val A)) := fun _ h ↦ absurd h (by simp)

@[simp] theorem closure_empty : closure (∅ : Set (PreTrace Loc Val A)) = ∅ := by
  ext π; simp [closure]

theorem closed_iUnion {ι : Sort*} {U : ι → Set (PreTrace Loc Val A)}
    (h : ∀ i, Closed (U i)) : Closed (⋃ i, U i) := by
  rintro τ hτ π hstep
  rw [Set.mem_iUnion] at hτ ⊢
  obtain ⟨i, hi⟩ := hτ
  exact ⟨i, h i _ hi _ hstep⟩

theorem closure_iUnion {ι : Sort*} (S : ι → Set (PreTrace Loc Val A)) :
    closure (⋃ i, S i) = ⋃ i, closure (S i) := by
  ext π
  simp only [mem_closure_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨τ, ⟨i, hi⟩, hr⟩; exact ⟨i, τ, hi, hr⟩
  · rintro ⟨i, τ, hi, hr⟩; exact ⟨τ, ⟨i, hi⟩, hr⟩

/-- Rewriting preserves trace-hood, by the guard in `TStep`. -/
theorem Refines.isTrace {τ π : PreTrace Loc Val A} (hr : Refines τ π)
    (hτ : IsTrace τ) : IsTrace π := by
  induction hr with
  | refl => exact hτ
  | tail _ hstep _ => exact hstep.2

theorem IsTraceSet.closure {S : Set (PreTrace Loc Val A)} (h : IsTraceSet S) :
    IsTraceSet (_root_.Isotope.Elgot.RA.closure S) :=
  fun _ ⟨_, hτ, hr⟩ ↦ hr.isTrace (h _ hτ)

/-- Rewriting preserves the returned value. -/
theorem Step.ret_eq {τ π : PreTrace Loc Val A} (h : Step τ π) : τ.ret = π.ret := by
  cases h <;> rfl

theorem Refines.ret_eq {τ π : PreTrace Loc Val A} (h : Refines τ π) : τ.ret = π.ret := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans hstep.1.ret_eq

/-! ## The local messages are a rewriting invariant

Every `𝔠`-rewrite preserves `ξ.own` exactly.  `Stutter` inserts a transition
`⟨μ,μ⟩`, whose contribution is `μ \ μ = ∅`; `Mumble` replaces `⟨μ,ρ⟩⟨ρ,θ⟩` by
`⟨μ,θ⟩`, and `(ρ \ μ) ∪ (θ \ ρ) = θ \ μ` whenever `μ ⊆ ρ ⊆ θ`, which holds
because the transitions of a trace are well-formed.  This is the separation
invariant that lets us tell computations apart. -/

theorem ChroStep.own_eq {c₁ c₂ : Chro Loc Val} (h : ChroStep c₁ c₂)
    (hwf : ∀ T ∈ c₁.toList, T.WF) : c₁.own = c₂.own := by
  cases h with
  | stutter l r μ h₁ h₂ =>
      simp only [Chro.own_eq_listOwn, h₁, h₂, listOwn_append, listOwn_cons,
        Transition.own, Set.diff_self, Set.empty_union]
  | mumble l r μ ρ θ h₁ h₂ =>
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

theorem Step.own_eq {τ π : PreTrace Loc Val A} (h : Step τ π) (hτ : IsTrace τ) :
    τ.ch.own = π.ch.own := by
  cases h with
  | chro hc => exact hc.own_eq hτ.wf
  | forward _ => rfl
  | rewind _ => rfl

theorem Refines.own_eq {τ π : PreTrace Loc Val A} (h : Refines τ π) (hτ : IsTrace τ) :
    τ.ch.own = π.ch.own := by
  induction h with
  | refl => rfl
  | @tail b c hab hbc ih =>
      exact ih.trans (hbc.1.own_eq (Refines.isTrace hab hτ))

end Isotope.Elgot.RA
