import Isotope.Elgot.RA.Trace

/-!
# Delimiting views for parallel composition: `sup_μ`, `inf_μ`, and memory growth

Support for `Isotope/Elgot/RA/Parallel.lean`.  Dvir, Kammar and Lahav
(`release-acquire`, TOPLAS 47(2):7) delimit a parallel composition by the
*greatest lower bound of the initial views* and the *least upper bound of the
final views*, and define both in the poset of views pointing downwards into a
fixed memory (journal §7.2, p.29):

> denote the set of views pointing downward into a well-formed memory `μ` by
> `↠μ := {κ ∈ View | κ ↠ μ}`.  This set is finite since `Loc` and `μ` are
> finite, and each `κ` mentions only timestamps that appear in `μ`; and it has a
> minimum: the view that points to all the initial messages `λℓ. min μ_ℓ.t`.
> Consider a non-empty subset of views `U ⊆ ↠μ`.  Since `↠μ` is finite and
> closed under `⊔`, the subset `U` has a least upper bound `sup_μ U := ⊔U`.
> Since `↠μ` has a minimal element — the view pointing to the minimal messages —
> `U` also has a greatest lower bound `inf_μ U := ⊔{κ ∈ View | ⊓U ⊒ κ ↠ μ}`.
> Though `⊓U` bounds `U` below, it may not be in `↠μ`.

## `sup_μ` is the pointwise join; `inf_μ` is not the pointwise meet

`sup_μ U = ⊔U` **by definition**, so it is literally Lean's `⊔` on
`View Loc = Loc → ℚ`; the subscript records only that `↠μ` is closed under `⊔`,
which is `PointsDownInto.sup` below.  The paper itself drops the subscript when
it computes (journal p.57: "`sup_{ξ.c}{ω₁,ω₂} = ω₁ ⊔ ω₂`").

`inf_μ U` is **not** `⊓U`: it is the greatest element of `↠μ` below `⊓U`, and
the paper's own Example 7.3 exhibits the gap.  We give it as the characterising
predicate `IsInfMem` rather than as a construction.

## Deviations, flagged

1. **Characterisation, not construction.**  `IsInfMem μ U κ` says exactly that
   `κ` is the greatest view pointing downwards into `μ` and below every element
   of `U` — i.e. that the `⊔` in the paper's formula is *attained*.  Everything
   `Parallel.lean` needs follows from the characterisation.  The paper's
   existence argument (`↠μ` is finite and has a minimum) is **not** formalized,
   so `IsInfMem` is carried as a hypothesis rather than produced; see the honest
   boundary in `Isotope/Elgot/RA.lean`.
2. **Domain.**  The paper defines `inf_μ U` only for `U ⊆ ↠μ`, but applies it in
   the definition of `∥∥∥` at `U = {α₁,α₂}`, `μ = ξ.o`, where `α₂ ↠ ξ.o` can
   fail (`ξ.o` is contained in, but need not equal, `ξ₂.o`).  Its own Appendix A
   proof (p.49) also uses the general reading.  `IsInfMem` therefore imposes no
   condition relating `U` to `μ`, matching the formula rather than the stated
   domain.

## Memory growth along a chronicle

The remaining lemmas are the elementary consequence of chronicle adjacency
`ρⱼ ⊆ μⱼ₊₁` together with `μ ⊆ ρ` for well-formed transitions: the memories of a
chronicle form a `⊆`-chain.  These are used to move a view that points downwards
into one thread's memory into the shuffled chronicle's memory, and to prove the
separation theorem `Interleave.own_disjoint`.  They are not stated in the paper;
`Isotope/Elgot/RA/Monad.lean` has the analogous facts for the special case of an
all-stutter chronicle.
-/

namespace Isotope.Elgot.RA

variable {Loc Val : Type}

/-! ## `↠μ` is closed under the pointwise join -/

/-- **`↠μ` is closed under `⊔`** (journal §7.2, p.29, asserted; also p.24, "the
pointwise maximum `⊔` preserves pointing downwards").  This is what makes
`sup_μ U = ⊔U` land back in `↠μ`, and it is the only property of `sup_μ` that
the definition of `∥∥∥` uses. -/
theorem PointsDownInto.sup {κ σ : View Loc} {μ : Memory Loc Val}
    (hκ : PointsDownInto κ μ) (hσ : PointsDownInto σ μ) : PointsDownInto (κ ⊔ σ) μ := by
  intro ℓ
  obtain ⟨ν, hν, hνl, hνp, hνv⟩ := hκ ℓ
  obtain ⟨ε, hε, hεl, hεp, hεv⟩ := hσ ℓ
  have hκℓ : κ ℓ = ν.t := by rw [← hνl]; exact hνp
  have hσℓ : σ ℓ = ε.t := by rw [← hεl]; exact hεp
  have hsupℓ : (κ ⊔ σ) ℓ = κ ℓ ⊔ σ ℓ := rfl
  rcases le_total ν.t ε.t with hle | hle
  · refine ⟨ε, hε, hεl, ?_, le_trans hεv le_sup_right⟩
    change (κ ⊔ σ) ε.lc = ε.t
    rw [hεl, hsupℓ, hκℓ, hσℓ]
    exact sup_eq_right.mpr hle
  · refine ⟨ν, hν, hνl, ?_, le_trans hνv le_sup_left⟩
    change (κ ⊔ σ) ν.lc = ν.t
    rw [hνl, hsupℓ, hκℓ, hσℓ]
    exact sup_eq_left.mpr hle

/-! ## `inf_μ`, characterised -/

/-- `IsInfMem μ U κ`: `κ` is the paper's `inf_μ U`, i.e. the greatest view that
points downwards into `μ` and lies below every element of `U` (journal §7.2,
p.29).  Characterised rather than constructed: see the module docstring. -/
structure IsInfMem (μ : Memory Loc Val) (U : Set (View Loc)) (κ : View Loc) : Prop where
  /-- `κ ↠ μ`: the candidate is in `↠μ`. -/
  pointsDown : PointsDownInto κ μ
  /-- `κ ⊑ ⊓U`: the candidate bounds `U` below. -/
  lb : ∀ α ∈ U, κ ≤ α
  /-- `κ` is the greatest such view: the `⊔` of the paper's formula is
  attained. -/
  greatest : ∀ σ : View Loc, PointsDownInto σ μ → (∀ α ∈ U, σ ≤ α) → σ ≤ κ

namespace IsInfMem

/-- `inf_μ U` is unique when it exists. -/
theorem unique {μ : Memory Loc Val} {U : Set (View Loc)} {κ σ : View Loc}
    (hκ : IsInfMem μ U κ) (hσ : IsInfMem μ U σ) : κ = σ :=
  le_antisymm (hσ.greatest κ hκ.pointsDown hκ.lb) (hκ.greatest σ hσ.pointsDown hσ.lb)

/-- **`inf_μ` is monotone in `μ`** (journal p.49, `St` case: "We have
`ξ.o ⊆ ξ'.o`, so `inf_{ξ.o}{α₁,α₂} ⊑ inf_{ξ'.o}{α₁,α₂}`").  Enlarging the memory
enlarges `↠μ`, hence the set whose join is taken. -/
theorem mono_memory {μ μ' : Memory Loc Val} {U : Set (View Loc)} {κ κ' : View Loc}
    (hκ : IsInfMem μ U κ) (hκ' : IsInfMem μ' U κ') (h : μ ⊆ μ') : κ ≤ κ' :=
  hκ'.greatest κ (hκ.pointsDown.mono h) hκ.lb

/-- `inf_μ` depends on `U` only as a set, so it is symmetric in a pair. -/
theorem pair_comm {μ : Memory Loc Val} {α β κ : View Loc} (h : IsInfMem μ {α, β} κ) :
    IsInfMem μ {β, α} κ := by
  rw [Set.pair_comm] at h; exact h

end IsInfMem

/-- A view that points downwards into `μ` is its own `inf_μ` over the singleton
`{α}` — the case that makes thread inlining work, where both threads start from
the same view. -/
theorem isInfMem_singleton {μ : Memory Loc Val} {α : View Loc}
    (h : PointsDownInto α μ) : IsInfMem μ {α} α where
  pointsDown := h
  lb := by rintro β rfl; exact le_refl _
  greatest := fun _ _ hlb ↦ hlb α rfl

/-- …and over the doubleton `{α, α}`, which is how it arises from the definition
of `∥∥∥`. -/
theorem isInfMem_pair_self {μ : Memory Loc Val} {α : View Loc}
    (h : PointsDownInto α μ) : IsInfMem μ {α, α} α := by
  rw [Set.pair_eq_singleton]; exact isInfMem_singleton h

/-! ## The memories of a chronicle grow -/

/-- In an adjacent list of transitions each of which only grows its memory, the
closing memory of any transition is contained in the list's closing memory. -/
theorem chain_closing_sub_listC : ∀ (l : List (Transition Loc Val)), List.IsChain Adj l →
    (∀ T ∈ l, T.opening ⊆ T.closing) → ∀ T ∈ l, T.closing ⊆ listC l
  | [], _, _, _, hT => absurd hT (by simp)
  | [S], _, _, T, hT => by
      simp only [List.mem_singleton] at hT
      subst hT
      rw [listC_singleton]
  | S :: U :: r, hc, hsub, T, hT => by
      rw [listC_cons_cons]
      have ih := chain_closing_sub_listC (U :: r) (List.isChain_cons_cons.mp hc).2
        (fun V hV ↦ hsub V (by simp [hV]))
      rcases List.mem_cons.mp hT with rfl | hT
      · exact subset_trans (List.isChain_cons_cons.mp hc).1
          (subset_trans (hsub U (by simp)) (ih U (by simp)))
      · exact ih T hT

/-- In such a list, the closing memory of the head is contained in the opening
memory of *every* later transition.  This is the fact that turns one thread's
guarantee into the other thread's rely. -/
theorem chain_head_closing_sub : ∀ (T : Transition Loc Val) (l : List (Transition Loc Val)),
    List.IsChain Adj (T :: l) → (∀ U ∈ l, U.opening ⊆ U.closing) →
    ∀ S ∈ l, T.closing ⊆ S.opening
  | _, [], _, _, _, hS => absurd hS (by simp)
  | T, U :: r, hc, hsub, S, hS => by
      have h1 : T.closing ⊆ U.opening := (List.isChain_cons_cons.mp hc).1
      rcases List.mem_cons.mp hS with rfl | hS
      · exact h1
      · exact subset_trans h1 (subset_trans (hsub U (by simp))
          (chain_head_closing_sub U r (List.isChain_cons_cons.mp hc).2
            (fun V hV ↦ hsub V (by simp [hV])) S hS))

/-- The opening memory of such a list is contained in its closing memory. -/
theorem listO_sub_listC_of_sub : ∀ (l : List (Transition Loc Val)), l ≠ [] →
    List.IsChain Adj l → (∀ T ∈ l, T.opening ⊆ T.closing) → listO l ⊆ listC l
  | [], h, _, _ => absurd rfl h
  | T :: r, _, hc, hsub => by
      rw [listO_cons]
      exact subset_trans (hsub T (by simp)) (chain_closing_sub_listC _ hc hsub T (by simp))

namespace Chro

/-- Every transition of a chronicle with well-formed transitions closes inside
the chronicle's closing memory. -/
theorem closing_sub_c {ξ : Chro Loc Val} (hwf : ∀ T ∈ ξ.toList, T.WF)
    {T : Transition Loc Val} (hT : T ∈ ξ.toList) : T.closing ⊆ ξ.c :=
  chain_closing_sub_listC ξ.toList ξ.chain_toList (fun S hS ↦ (hwf S hS).sub) T hT

/-- A chronicle's opening memory is contained in its closing memory. -/
theorem o_sub_c {ξ : Chro Loc Val} (hwf : ∀ T ∈ ξ.toList, T.WF) : ξ.o ⊆ ξ.c :=
  listO_sub_listC_of_sub ξ.toList ξ.toList_ne_nil ξ.chain_toList
    (fun S hS ↦ (hwf S hS).sub)

end Chro

/-- A trace's opening memory is contained in its closing memory. -/
theorem IsTrace.o_sub_c {A : Type _} {τ : PreTrace Loc Val A} (h : IsTrace τ) :
    τ.ch.o ⊆ τ.ch.c := Chro.o_sub_c h.wf

end Isotope.Elgot.RA
