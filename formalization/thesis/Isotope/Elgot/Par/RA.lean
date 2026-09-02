import Isotope.Elgot.Par.Basic
import Isotope.Elgot.Par.Shuffle
import Isotope.Elgot.RA

/-!
# Release/acquire `∥∥∥` against the uniform interface

The release/acquire parallel composition `Comp.par` of `Isotope/Elgot/RA/Parallel.lean` is
the paper's `|||ᵀ` (Dvir–Kammar–Lahav, TOPLAS 47(2):7, §7.1 p.27, §7.2 p.29).  This module
places it in the classes of `Isotope/Elgot/Par/Basic.lean` and proves the *shuffle half* of
its associativity.

## What is instantiated

`ParOp` and `ParMono` only.  This is deliberate, and the reasons are worth recording:

* **`ParSymm` is not instantiable**, although symmetry *is* proved: `Comp.par_swap` states it
  as an equality of trace sets under `PreTrace.mapRet Prod.swap`, not under the monad's
  `<$>`.  The two agree only where `map = bind ∘ pure` behaves, i.e. where the unit laws
  hold; those are available at `𝔠 ⊆ R ⊆ 𝔤𝔠 ∪ {Ti, Ab}` and fail at `𝔤𝔠𝔞`
  (`Isotope/Elgot/RA/Abstract.lean`).  Restating symmetry through `<$>` would therefore be a
  *weaker* theorem than the one already proved, available at fewer rule sets.
* **`ParAssoc`, `ParUnit`, `ParNat`, `ParExchange`, `ParInline` are not instantiable**:
  associativity of `|||` is open (honest boundary item 8 of `Isotope/Elgot/RA.lean`), and the
  remaining laws are stated in the paper only as the unproved claim of the Fig. 3 caption
  (journal p.12) that `∥` obeys "all symmetric-monoidal laws".

## Why the Brookes route to associativity does not transfer

`Isotope/Elgot/Par/Brookes.lean` gets associativity from `IsPointwise`: every rewrite
replaces a contiguous block by a *single* event, so a rewrite can be pulled back through a
shuffle.  No such decomposition is in reach for `Step R`: `Fw`/`Rw` alter the delimiting
views of the whole pre-trace, and `Ls`, `Ex`, `Cn` alter *every* memory of the chronicle at
once (`Cn` maps them all through a pull).  A pointwise decomposition would have to leave a
prefix and a suffix of the chronicle untouched, which these rules do not.  This is an
observation about the shape of the rules, not a theorem: no `¬ IsPointwise` statement is
proved here.

## What is proved

The shuffle half of associativity, `ChroInterleave.assoc` and `.assoc'`: three chronicles
regroup.  The content beyond `Shuffle.assoc` is that the *middle* chronicle exists at all —
a shuffle of two chronicles need not satisfy the adjacency condition `ρⱼ ⊆ μⱼ₊₁`, but a
shuffle that sits inside a larger chronicle does, because adjacency in the ambient chronicle
composes along `μ ⊆ ρ` (`interleave_isChain`).  This is original: the paper never defines
`ξ₁ ∥ ξ₂` beyond a phrase (see the reconstruction note in `Isotope/Elgot/RA.lean`), let
alone states that it regroups.

What is **not** proved, and what associativity of `Comp.par` still needs on top of this: the
memory half — that the two nestings agree on `inf_{ξ.o}{α₁, α₂}` at the two different
opening memories `(ξ₁ ∥ ξ₂).o` and `(ξ₂ ∥ ξ₃).o`.  Since `inf_μ` is *characterised*
(`IsInfMem`) rather than constructed, this cannot even be stated as an equation.
-/

universe u

namespace Isotope.Elgot.Par

open Isotope.Elgot Isotope.Elgot.RA

variable {Loc Val : Type} {R : RuleSet} {A B : Type u}

/-! ## Shuffles inside a chronicle are chronicles -/

/-- **A shuffle sitting inside a chronicle is itself a chronicle.**  Adjacency `ρⱼ ⊆ μⱼ₊₁` is
not preserved by shuffling in general; it is preserved here because the ambient list is a
chain of well-formed transitions, along which closings compose into every later opening. -/
theorem interleave_isChain {l m w : List (Transition Loc Val)}
    (h : Interleave l m w) (hc : List.IsChain Adj w)
    (hsub : ∀ T ∈ w, T.opening ⊆ T.closing) : List.IsChain Adj m := by
  induction h with
  | nil => exact List.isChain_nil
  | @left e t u w' h' ih =>
      exact ih (List.isChain_cons.mp hc).2 (fun T hT ↦ hsub T (by simp [hT]))
  | @right e t u w' h' ih =>
      have hc' : List.IsChain Adj w' := (List.isChain_cons.mp hc).2
      have hsub' : ∀ T ∈ w', T.opening ⊆ T.closing := fun T hT ↦ hsub T (by simp [hT])
      refine List.isChain_cons.mpr ⟨?_, ih hc' hsub'⟩
      cases u with
      | nil => intro b hb; exact absurd hb (by simp)
      | cons f u' =>
          intro b hb
          have hbf : b = f := by simpa using hb.symm
          subst hbf
          exact chain_head_closing_sub e w' hc hsub' b (h'.mem_of_right (by simp))

/-! ## Regrouping a three-way chronicle shuffle -/

namespace ChroInterleave

/-- **Chronicle shuffling regroups, left to right.**  If `ξ₁₂` shuffles `ξ₁` with `ξ₂` and `ξ`
shuffles `ξ₁₂` with `ξ₃`, then some chronicle `ξ₂₃` shuffles `ξ₂` with `ξ₃` and `ξ` shuffles
`ξ₁` with it.  The hypothesis is that the transitions of the ambient chronicle `ξ` are
well-formed, which every trace supplies. -/
theorem assoc {ξ₁ ξ₂ ξ₁₂ ξ₃ ξ : Chro Loc Val} (h₁ : ChroInterleave ξ₁ ξ₂ ξ₁₂)
    (h₂ : ChroInterleave ξ₁₂ ξ₃ ξ) (hwf : ∀ T ∈ ξ.toList, T.WF) :
    ∃ ξ₂₃ : Chro Loc Val, ChroInterleave ξ₂ ξ₃ ξ₂₃ ∧ ChroInterleave ξ₁ ξ₂₃ ξ := by
  obtain ⟨m, hm, hw⟩ := Shuffle.assoc h₂.toInterleave h₁.toInterleave
  have hne : m ≠ [] := hm.ne_nil_left ξ₂.toList_ne_nil
  have hchain : List.IsChain Adj m :=
    interleave_isChain hw ξ.chain_toList (fun T hT ↦ (hwf T hT).sub)
  refine ⟨Chro.ofList m hne hchain, ?_, ?_⟩
  · change Interleave ξ₂.toList ξ₃.toList (Chro.ofList m hne hchain).toList
    rw [Chro.ofList_toList]
    exact hm
  · change Interleave ξ₁.toList (Chro.ofList m hne hchain).toList ξ.toList
    rw [Chro.ofList_toList]
    exact hw

/-- **Chronicle shuffling regroups, right to left.** -/
theorem assoc' {ξ₁ ξ₂ ξ₂₃ ξ₃ ξ : Chro Loc Val} (h₁ : ChroInterleave ξ₂ ξ₃ ξ₂₃)
    (h₂ : ChroInterleave ξ₁ ξ₂₃ ξ) (hwf : ∀ T ∈ ξ.toList, T.WF) :
    ∃ ξ₁₂ : Chro Loc Val, ChroInterleave ξ₁ ξ₂ ξ₁₂ ∧ ChroInterleave ξ₁₂ ξ₃ ξ := by
  obtain ⟨m, hm, hw⟩ := Shuffle.assoc' h₁.toInterleave h₂.toInterleave
  have hne : m ≠ [] := hm.ne_nil_left ξ₁.toList_ne_nil
  have hchain : List.IsChain Adj m :=
    interleave_isChain hw.swap ξ.chain_toList (fun T hT ↦ (hwf T hT).sub)
  refine ⟨Chro.ofList m hne hchain, ?_, ?_⟩
  · change Interleave ξ₁.toList ξ₂.toList (Chro.ofList m hne hchain).toList
    rw [Chro.ofList_toList]
    exact hm
  · change Interleave (Chro.ofList m hne hchain).toList ξ₃.toList ξ.toList
    rw [Chro.ofList_toList]
    exact hw

end ChroInterleave

/-! ## Instances -/

/-- Release/acquire parallel composition, as a `ParOp`. -/
instance instParOpRA : ParOp (Comp R Loc Val) where
  par := Comp.par

theorem par_eq_RA (P : Comp R Loc Val A) (Q : Comp R Loc Val B) :
    ParOp.par P Q = P.par Q := rfl

/-- **Proposition 7.4** for `∥∥∥`, as an instance of the uniform interface. -/
instance instParMonoRA : ParMono (Comp R Loc Val) where
  par_mono := Comp.par_mono

end Isotope.Elgot.Par
