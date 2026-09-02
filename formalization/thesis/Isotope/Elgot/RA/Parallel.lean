import Isotope.Elgot.Interleave
import Isotope.Elgot.RA.Bounds
import Isotope.Elgot.RA.Monad

/-!
# Parallel composition `∥∥∥`

Transcribed from Dvir, Kammar and Lahav (`release-acquire`), TOPLAS 47(2):7,
§7.2 "Parallel composition", p.29 (ESOP full version §6.3):

> Denote by `ξ₁ ∥ ξ₂` the set of all the interleavings of `ξ₁` and `ξ₂` that
> form chronicles.  We define:
> ```
> P₁ |||ᵀ_{X₁,X₂} P₂ :=
>   { inf_{ξ.o}{α₁,α₂}  ξ  sup_{ξ.c}{ω₁,ω₂} ◁ ⟨r₁,r₂⟩ ∈ Trace (X₁ × X₂)
>   | ξ ∈ (ξ₁ ∥ ξ₂) ∧ ∀ i ∈ {1,2}. αᵢ ξᵢ ωᵢ ◁ rᵢ ∈ Pᵢ }★
> ```

`∥∥∥` is *not* a monad operation.  Journal §7.1, p.27 lists it as extra
algebraic structure on `T`, one component per effect construct in Moggi's style:
`(|||ᵀ_{X,Y}) : T X × T Y → T (X × Y)`, interpreting `⟦M ∥ N⟧ᶜ γ`.  It is a
second, *concurrent* tensor, unrelated to the sequential premonoidal tensor of
`Isotope/CategoryTheory/Premonoidal.lean`, and no `Monad`/`LawfulMonad`/
`Iterate` instance changes because of it.

Everything here is uniform in the rule set `R`, so it applies to the Null,
Generating, `𝔠` and Concrete models at once.

## Reconstruction: `ξ₁ ∥ ξ₂`

⚠ **The paper never defines `ξ₁ ∥ ξ₂` more formally than the sentence quoted
above.**  We read it as: `ξ.toList` is a *shuffle* of `ξ₁.toList` and
`ξ₂.toList` — transitions carried across verbatim, neither merged nor rewritten
— which is again a chronicle, i.e. satisfies the adjacency condition
`ρⱼ ⊆ μⱼ₊₁`.  That is `ChroInterleave`.  The evidence is the paper's own worked
computation of `⟦store ℓ,v⟧_G ||| ⟦rmw ℓ',λ_.⊥⟧_G` (Prop E.5, journal p.59),
which lists the two transitions verbatim in the two possible orders; and the
Deferral of Closure proof (Appendix A, pp.48–49), which decomposes
`ξ = η ⟨μ,μ⟩ η'` with `ξ₂ = η₂η₂'`, `η ∈ η₁ ∥ η₂` and `η' ∈ η₁' ∥ η₂'` — a
position-wise split of a shuffle.  **This is a reading, not a quotation.**

Chronicle adjacency is the *only* compatibility condition between the two
threads: there is no disjointness premise, no footprint, and no frame rule
anywhere in the paper.  Adjacency is exactly what turns one thread's guarantee
into the other's rely.

## What is proved here

* `parGen_isTrace` — the paper's guard `∈ Trace (X₁ × X₂)` is **redundant**, as
  it is for `>>=`.  Every trace condition on the composite follows from the two
  operands and the shuffle.  Original; the paper carries the guard as a side
  condition and never observes that it is automatic.
* `ChroInterleave.own_union` and `ChroInterleave.own_disjoint` — parallel
  composition splits the local messages, *disjointly*.  Original: the paper has
  no separation statement at all, and disjointness is forced by chronicle
  adjacency alone rather than imposed.
* `Comp.par_mono` — the `∥∥∥` half of **Proposition 7.4** (journal p.29), whose
  paper proof is the one line "the `(_)★` operator is monotonic".
* `Comp.par_swap` — **Symmetry** of Table 3 (journal p.44).  The paper claims
  Symmetry and "all symmetric-monoidal laws with the binary operator `∥` and the
  unit `⟨⟩`" (Fig. 3 caption, p.12) with **no proposition, no proof and no proof
  sketch**; this is therefore original work, not a port.

`Isotope/Elgot/RA/Exchange.lean` proves thread inlining and the exchange law.
What is *not* reached is recorded in the honest boundary of
`Isotope/Elgot/RA.lean`.
-/

universe u

namespace Isotope.Elgot.RA

open Isotope.Elgot (Interleave)

variable {Loc Val : Type} {R : RuleSet} {A B C : Type u}

/-! ## `ξ₁ ∥ ξ₂`: shuffling chronicles -/

/-- `ChroInterleave ξ₁ ξ₂ ξ` is the paper's `ξ ∈ ξ₁ ∥ ξ₂`: the transitions of
`ξ` are a shuffle of those of `ξ₁` and `ξ₂`, and `ξ` is again a chronicle —
which, since `Chro` bakes in adjacency, is automatic in the statement. -/
def ChroInterleave (ξ₁ ξ₂ ξ : Chro Loc Val) : Prop :=
  Interleave ξ₁.toList ξ₂.toList ξ.toList

/-- The opening memory of a shuffle is contained in the opening memory of
either operand: the shuffle starts with whichever thread moves first, and every
later transition opens above it. -/
theorem interleave_listO_sub {l₁ l₂ l : List (Transition Loc Val)}
    (h : Interleave l₁ l₂ l) (hc : List.IsChain Adj l)
    (hsub : ∀ T ∈ l, T.opening ⊆ T.closing) (hne : l₁ ≠ []) : listO l ⊆ listO l₁ := by
  cases h with
  | nil => exact absurd rfl hne
  | @left e t u w h' => exact subset_refl _
  | @right e t u w h' =>
      obtain ⟨T, r, rfl⟩ := List.exists_cons_of_ne_nil hne
      have hsub' : ∀ U ∈ w, U.opening ⊆ U.closing := fun U hU ↦ hsub U (by simp [hU])
      have hkey := chain_head_closing_sub e w hc hsub' T (h'.mem_of_left (by simp))
      exact subset_trans (hsub e (by simp)) hkey

namespace ChroInterleave

variable {ξ₁ ξ₂ ξ : Chro Loc Val}

/-- The underlying shuffle of transition lists. -/
theorem toInterleave (h : ChroInterleave ξ₁ ξ₂ ξ) :
    Interleave ξ₁.toList ξ₂.toList ξ.toList := h

/-- Shuffling chronicles is symmetric. -/
theorem symm (h : ChroInterleave ξ₁ ξ₂ ξ) : ChroInterleave ξ₂ ξ₁ ξ := h.toInterleave.swap

/-- Every transition of the shuffle comes from one of the two threads. -/
theorem mem_or (h : ChroInterleave ξ₁ ξ₂ ξ) {T : Transition Loc Val} (hT : T ∈ ξ.toList) :
    T ∈ ξ₁.toList ∨ T ∈ ξ₂.toList := h.toInterleave.mem_or hT

/-- Every transition of the left thread occurs in the shuffle. -/
theorem mem_left (h : ChroInterleave ξ₁ ξ₂ ξ) {T : Transition Loc Val}
    (hT : T ∈ ξ₁.toList) : T ∈ ξ.toList := h.toInterleave.mem_of_left hT

/-- Every transition of the right thread occurs in the shuffle. -/
theorem mem_right (h : ChroInterleave ξ₁ ξ₂ ξ) {T : Transition Loc Val}
    (hT : T ∈ ξ₂.toList) : T ∈ ξ.toList := h.toInterleave.mem_of_right hT

/-- Running the left thread to completion and then the right one is a shuffle:
the concatenation of two chronicles at a compatible seam is one of their
interleavings.  This is the shuffle that thread inlining uses. -/
theorem append (ξ₁ ξ₂ : Chro Loc Val) (h : ξ₁.c ⊆ ξ₂.o) :
    ChroInterleave ξ₁ ξ₂ (ξ₁.append ξ₂ h) := by
  simpa [ChroInterleave] using Interleave.append ξ₁.toList ξ₂.toList

/-- The transitions of a shuffle of two chronicles with well-formed transitions
are well-formed. -/
theorem wf (h : ChroInterleave ξ₁ ξ₂ ξ) (h₁ : ∀ T ∈ ξ₁.toList, T.WF)
    (h₂ : ∀ T ∈ ξ₂.toList, T.WF) : ∀ T ∈ ξ.toList, T.WF := by
  intro T hT
  exact (h.mem_or hT).elim (h₁ T) (h₂ T)

/-- The left thread closes inside the shuffle's closing memory. -/
theorem c_sub_left (h : ChroInterleave ξ₁ ξ₂ ξ) (hwf : ∀ T ∈ ξ.toList, T.WF) :
    ξ₁.c ⊆ ξ.c := by
  obtain ⟨T, hT, hc⟩ := listC_mem ξ₁.toList ξ₁.toList_ne_nil
  change listC ξ₁.toList ⊆ listC ξ.toList
  rw [hc]
  exact chain_closing_sub_listC ξ.toList ξ.chain_toList (fun S hS ↦ (hwf S hS).sub) T
    (h.mem_left hT)

/-- The right thread closes inside the shuffle's closing memory. -/
theorem c_sub_right (h : ChroInterleave ξ₁ ξ₂ ξ) (hwf : ∀ T ∈ ξ.toList, T.WF) :
    ξ₂.c ⊆ ξ.c := h.symm.c_sub_left hwf

/-- The shuffle's opening memory is contained in the left thread's.  This is why
the paper's `inf_{ξ.o}` is applied outside its stated domain `U ⊆ ↠ξ.o`: from
`α₂ ↠ ξ₂.o` one may *not* conclude `α₂ ↠ ξ.o`, since `ξ.o` is the smaller
memory.  See `Isotope/Elgot/RA/Bounds.lean`. -/
theorem o_sub_left (h : ChroInterleave ξ₁ ξ₂ ξ) (hwf : ∀ T ∈ ξ.toList, T.WF) :
    ξ.o ⊆ ξ₁.o :=
  interleave_listO_sub h ξ.chain_toList (fun T hT ↦ (hwf T hT).sub) ξ₁.toList_ne_nil

/-- The shuffle's opening memory is contained in the right thread's. -/
theorem o_sub_right (h : ChroInterleave ξ₁ ξ₂ ξ) (hwf : ∀ T ∈ ξ.toList, T.WF) :
    ξ.o ⊆ ξ₂.o := h.symm.o_sub_left hwf

end ChroInterleave

/-! ## Local messages split, disjointly

**Original work.**  The paper has no separation statement about `∥∥∥`; memories
are global and shared, and there is no frame rule, footprint or ownership
transfer discipline anywhere in it.  Nevertheless the local/environment message
distinction `ξ.own := ⋃ᵢ (ρᵢ \ μᵢ)` (journal p.27) splits across a parallel
composition, and the union is *disjoint* — forced by chronicle adjacency alone,
with no side condition added to the definition. -/

/-- The local messages of a shuffle are those of its two operands. -/
theorem listOwn_union_of_interleave {l₁ l₂ l : List (Transition Loc Val)}
    (h : Interleave l₁ l₂ l) : listOwn l = listOwn l₁ ∪ listOwn l₂ := by
  induction h with
  | nil => simp
  | left _ ih => rw [listOwn_cons, listOwn_cons, ih, Set.union_assoc]
  | right _ ih =>
      rw [listOwn_cons, listOwn_cons, ih, ← Set.union_assoc, ← Set.union_assoc,
        Set.union_comm (listOwn _) _]

/-- **Ownership is separating.**  A message cannot be local to both threads: if
it were, the thread whose transition comes first in the shuffle would have
placed it in the *opening* memory of the other's transition, contradicting
locality there.  Only chronicle adjacency and `μ ⊆ ρ` are used. -/
theorem listOwn_disjoint_of_interleave {l₁ l₂ l : List (Transition Loc Val)}
    (h : Interleave l₁ l₂ l) (hc : List.IsChain Adj l)
    (hsub : ∀ T ∈ l, T.opening ⊆ T.closing) :
    Disjoint (listOwn l₁) (listOwn l₂) := by
  induction h with
  | nil => simp
  | @left e t u w h' ih =>
      have hc' : List.IsChain Adj w := (List.isChain_cons.mp hc).2
      have hsub' : ∀ T ∈ w, T.opening ⊆ T.closing := fun T hT ↦ hsub T (by simp [hT])
      rw [listOwn_cons]
      refine Set.disjoint_union_left.mpr ⟨?_, ih hc' hsub'⟩
      rw [Set.disjoint_left]
      rintro ν ⟨hνc, hνo⟩ ⟨S, hS, hSc, hSo⟩
      exact hSo (chain_head_closing_sub e w hc hsub' S (h'.mem_of_right hS) hνc)
  | @right e t u w h' ih =>
      have hc' : List.IsChain Adj w := (List.isChain_cons.mp hc).2
      have hsub' : ∀ T ∈ w, T.opening ⊆ T.closing := fun T hT ↦ hsub T (by simp [hT])
      rw [listOwn_cons]
      refine Set.disjoint_union_right.mpr ⟨?_, ih hc' hsub'⟩
      rw [Set.disjoint_right]
      rintro ν ⟨hνc, hνo⟩ ⟨S, hS, hSc, hSo⟩
      exact hSo (chain_head_closing_sub e w hc hsub' S (h'.mem_of_left hS) hνc)

namespace ChroInterleave

variable {ξ₁ ξ₂ ξ : Chro Loc Val}

/-- `ξ.own = ξ₁.own ∪ ξ₂.own`. -/
theorem own_union (h : ChroInterleave ξ₁ ξ₂ ξ) : ξ.own = ξ₁.own ∪ ξ₂.own :=
  listOwn_union_of_interleave h.toInterleave

/-- `ξ₁.own` and `ξ₂.own` are disjoint. -/
theorem own_disjoint (h : ChroInterleave ξ₁ ξ₂ ξ) (hwf : ∀ T ∈ ξ.toList, T.WF) :
    Disjoint ξ₁.own ξ₂.own :=
  listOwn_disjoint_of_interleave h.toInterleave ξ.chain_toList
    (fun T hT ↦ (hwf T hT).sub)

end ChroInterleave

/-! ## The generating set of `P₁ ||| P₂` -/

/-- The traces generated by `P₁ ||| P₂`, before closure (journal §7.2, p.29).
`sup_{ξ.c}{ω₁,ω₂}` is literally `ω₁ ⊔ ω₂`; `inf_{ξ.o}{α₁,α₂}` is carried as the
characterisation `IsInfMem` of `Isotope/Elgot/RA/Bounds.lean`.

Following the treatment of `bindGen`, the paper's guard `∈ Trace (X₁ × X₂)` is
*not* a conjunct: `parGen_isTrace` shows it is automatic. -/
def parGen (P : Set (PreTrace Loc Val A)) (Q : Set (PreTrace Loc Val B)) :
    Set (PreTrace Loc Val (A × B)) :=
  {π | ∃ τ ∈ P, ∃ υ ∈ Q, ChroInterleave τ.ch υ.ch π.ch ∧
    IsInfMem π.ch.o {τ.ivw, υ.ivw} π.ivw ∧
    π.fvw = τ.fvw ⊔ υ.fvw ∧ π.ret = (τ.ret, υ.ret)}

/-- **The `∈ Trace` guard in the definition of `∥∥∥` is redundant.**  Every
condition on the composite pre-trace follows from the two operand traces and the
shuffle: transitions are carried over verbatim; `α ⊑ α₁ ⊑ ω₁ ⊑ ω₁ ⊔ ω₂`;
`α ↠ ξ.o` is what `inf_{ξ.o}` delivers; `ω₁ ⊔ ω₂ ↠ ξ.c` because each `ξᵢ.c`
grows into `ξ.c` and `↠ξ.c` is closed under `⊔`; and local messages are bounded
because `α ⊑ αᵢ` and `ωᵢ ⊑ ω₁ ⊔ ω₂`.

Original: the paper carries the guard as a side condition and never observes
that it is automatic, exactly as it does for `>>=`. -/
theorem parGen_isTrace {P : Set (PreTrace Loc Val A)} {Q : Set (PreTrace Loc Val B)}
    (hP : IsTraceSet P) (hQ : IsTraceSet Q) : IsTraceSet (parGen P Q) := by
  rintro π ⟨τ, hτ, υ, hυ, hint, hinf, hfvw, hret⟩
  have hτ' : IsTrace τ := hP _ hτ
  have hυ' : IsTrace υ := hQ _ hυ
  have hwf : ∀ T ∈ π.ch.toList, T.WF := hint.wf hτ'.wf hυ'.wf
  have hα₁ : π.ivw ≤ τ.ivw := hinf.lb _ (by simp)
  have hα₂ : π.ivw ≤ υ.ivw := hinf.lb _ (by simp)
  refine ⟨hwf, hinf.pointsDown, ?_, ?_, ?_⟩
  · rw [hfvw]
    exact le_trans hα₁ (le_trans hτ'.mono le_sup_left)
  · rw [hfvw]
    exact PointsDownInto.sup (hτ'.closePts.mono (hint.c_sub_left hwf))
      (hυ'.closePts.mono (hint.c_sub_right hwf))
  · intro ν hν
    rw [hint.own_union] at hν
    rw [hfvw]
    rcases hν with hν | hν
    · obtain ⟨h1, h2, h3⟩ := hτ'.own ν hν
      exact ⟨le_trans hα₁ h1, le_trans h2 le_sup_left,
        lt_of_le_of_lt (hα₁ ν.lc) h3⟩
    · obtain ⟨h1, h2, h3⟩ := hυ'.own ν hν
      exact ⟨le_trans hα₂ h1, le_trans h2 le_sup_right,
        lt_of_le_of_lt (hα₂ ν.lc) h3⟩

/-- **Proposition 7.4** for `∥∥∥` (journal p.29), before closure. -/
theorem parGen_mono {P P' : Set (PreTrace Loc Val A)} {Q Q' : Set (PreTrace Loc Val B)}
    (hP : P ⊆ P') (hQ : Q ⊆ Q') : parGen P Q ⊆ parGen P' Q' := by
  rintro π ⟨τ, hτ, υ, hυ, hint, hinf, hfvw, hret⟩
  exact ⟨τ, hP hτ, υ, hQ hυ, hint, hinf, hfvw, hret⟩

/-! ## Relabelling the returned value

The rewrite rules never touch the returned value (journal Table 2, p.30: "in
presenting these closure rules we omit the return value, because they all
maintain it"), so relabelling it commutes with the closure.  This is what lets
Symmetry be stated as an equality of trace sets rather than through the monad's
`map`, which is `bind`-and-`pure` and therefore only available where the monad
laws are. -/

/-- Relabel the returned value of a pre-trace. -/
def PreTrace.mapRet (f : A → B) (τ : PreTrace Loc Val A) : PreTrace Loc Val B :=
  ⟨τ.ivw, τ.ch, τ.fvw, f τ.ret⟩

/-- Relabelling leaves the initial view. -/
@[simp] theorem PreTrace.mapRet_ivw (f : A → B) (τ : PreTrace Loc Val A) :
    (τ.mapRet f).ivw = τ.ivw := rfl

/-- Relabelling leaves the chronicle. -/
@[simp] theorem PreTrace.mapRet_ch (f : A → B) (τ : PreTrace Loc Val A) :
    (τ.mapRet f).ch = τ.ch := rfl

/-- Relabelling leaves the final view. -/
@[simp] theorem PreTrace.mapRet_fvw (f : A → B) (τ : PreTrace Loc Val A) :
    (τ.mapRet f).fvw = τ.fvw := rfl

/-- Relabelling acts on the returned value. -/
@[simp] theorem PreTrace.mapRet_ret (f : A → B) (τ : PreTrace Loc Val A) :
    (τ.mapRet f).ret = f τ.ret := rfl

/-- Relabelling is functorial. -/
@[simp] theorem PreTrace.mapRet_mapRet (f : A → B) (g : B → C) (τ : PreTrace Loc Val A) :
    (τ.mapRet f).mapRet g = τ.mapRet (fun a ↦ g (f a)) := rfl

/-- Swapping a paired returned value twice is the identity. -/
@[simp] theorem PreTrace.mapRet_swap_swap (τ : PreTrace Loc Val (A × B)) :
    (τ.mapRet Prod.swap).mapRet Prod.swap = τ := by
  simp only [PreTrace.mapRet_mapRet, Prod.swap_swap]
  rfl

/-- The trace conditions do not mention the returned value. -/
theorem IsTrace.mapRet {f : A → B} {τ : PreTrace Loc Val A} (h : IsTrace τ) :
    IsTrace (τ.mapRet f) :=
  ⟨h.wf, h.openPts, h.mono, h.closePts, h.own⟩

/-- Every rule is a rule on relabelled pre-traces. -/
theorem Step.mapRet (f : A → B) {τ π : PreTrace Loc Val A} (h : Step R τ π) :
    Step R (τ.mapRet f) (π.mapRet f) := by
  cases h with
  | chro hx hc => exact Step.chro hx hc
  | forward hx hκ => exact Step.forward hx hκ
  | rewind hx hα => exact Step.rewind hx hα
  | condense hx l m ν ε hde hfν hfε h₁ h₂ =>
      exact Step.condense hx l m ν ε hde hfν hfε h₁ h₂

/-- Trace-preserving rewrites survive relabelling. -/
theorem TStep.mapRet (f : A → B) {τ π : PreTrace Loc Val A} (h : TStep R τ π) :
    TStep R (τ.mapRet f) (π.mapRet f) := ⟨h.1.mapRet f, h.2.mapRet⟩

/-- Refinement survives relabelling. -/
theorem Refines.mapRet (f : A → B) {τ π : PreTrace Loc Val A} (h : Refines R τ π) :
    Refines R (τ.mapRet f) (π.mapRet f) := by
  induction h with
  | refl => exact Refines.refl _
  | tail _ hstep ih => exact ih.tail (hstep.mapRet f)

/-- Relabelling along a bijection commutes with the closure. -/
theorem closure_image_mapRet (f : A → B) (g : B → A) (hgf : ∀ a, g (f a) = a)
    (hfg : ∀ b, f (g b) = b) (S : Set (PreTrace Loc Val A)) :
    PreTrace.mapRet f '' closure R S = closure R (PreTrace.mapRet f '' S) := by
  have hmap : ∀ (τ : PreTrace Loc Val A), (τ.mapRet f).mapRet g = τ := by
    intro τ; simp only [PreTrace.mapRet_mapRet, hgf]; rfl
  have hmap' : ∀ (τ : PreTrace Loc Val B), (τ.mapRet g).mapRet f = τ := by
    intro τ; simp only [PreTrace.mapRet_mapRet, hfg]; rfl
  apply Set.Subset.antisymm
  · rintro π ⟨τ, ⟨τ₀, hτ₀, hr⟩, rfl⟩
    exact ⟨τ₀.mapRet f, ⟨τ₀, hτ₀, rfl⟩, hr.mapRet f⟩
  · rintro π ⟨σ, ⟨τ₀, hτ₀, rfl⟩, hr⟩
    refine ⟨π.mapRet g, ⟨τ₀, hτ₀, ?_⟩, hmap' π⟩
    have := hr.mapRet g
    rwa [hmap τ₀] at this

/-! ## Symmetry

**Original work.**  Journal Table 3 (p.44) lists `Symmetry: M ∥ N ↠ swap(N ∥ M)`
and the Fig. 3 caption (p.12) claims "all symmetric-monoidal laws with the
binary operator `∥` and the unit `⟨⟩`"; there is no proposition, no proof and no
proof sketch for any of them in either the 85-page journal version or the
80-page ESOP full version.  Symmetry is an *equality*, not merely a refinement:
`⊔` is commutative and `inf_μ` is taken over a *set* of views. -/

/-- Symmetry, before closure, as a membership equivalence. -/
theorem mem_parGen_swap {P : Set (PreTrace Loc Val A)} {Q : Set (PreTrace Loc Val B)}
    {π : PreTrace Loc Val (A × B)} :
    π ∈ parGen P Q ↔ π.mapRet Prod.swap ∈ parGen Q P := by
  constructor
  · rintro ⟨τ, hτ, υ, hυ, hint, hinf, hfvw, hret⟩
    refine ⟨υ, hυ, τ, hτ, hint.symm, hinf.pair_comm, ?_, ?_⟩
    · change π.fvw = υ.fvw ⊔ τ.fvw
      rw [hfvw]; exact sup_comm _ _
    · change Prod.swap π.ret = (υ.ret, τ.ret)
      rw [hret]; rfl
  · rintro ⟨υ, hυ, τ, hτ, hint, hinf, hfvw, hret⟩
    refine ⟨τ, hτ, υ, hυ, hint.symm, hinf.pair_comm, ?_, ?_⟩
    · change π.fvw = τ.fvw ⊔ υ.fvw
      replace hfvw : π.fvw = υ.fvw ⊔ τ.fvw := hfvw
      rw [hfvw]; exact sup_comm _ _
    · have h2 := congrArg Prod.swap hret
      simpa using h2

/-- Symmetry, before closure. -/
theorem parGen_swap (P : Set (PreTrace Loc Val A)) (Q : Set (PreTrace Loc Val B)) :
    parGen P Q = PreTrace.mapRet Prod.swap '' parGen Q P := by
  ext π
  simp only [Set.mem_image]
  constructor
  · intro h
    exact ⟨π.mapRet Prod.swap, mem_parGen_swap.mp h, PreTrace.mapRet_swap_swap π⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact mem_parGen_swap.mpr (by rw [PreTrace.mapRet_swap_swap]; exact hσ)

/-! ## The operation on the monad -/

namespace Comp

/-- `P ||| Q`: parallel composition (journal §7.1, p.27; §7.2, p.29).  Extra
algebraic structure on `T`, of type `T X × T Y → T (X × Y)`; **not** a monad
operation, and not the sequential premonoidal tensor. -/
def par (P : Comp R Loc Val A) (Q : Comp R Loc Val B) : Comp R Loc Val (A × B) :=
  Comp.close R (parGen P.traces Q.traces) (parGen_isTrace P.isTrace Q.isTrace)

/-- The traces of a parallel composition. -/
@[simp] theorem traces_par (P : Comp R Loc Val A) (Q : Comp R Loc Val B) :
    (P.par Q).traces = closure R (parGen P.traces Q.traces) := rfl

/-- **Proposition 7.4** for `∥∥∥` (journal p.29): parallel composition is
monotone in both operands. -/
theorem par_mono {P P' : Comp R Loc Val A} {Q Q' : Comp R Loc Val B}
    (hP : P ≤ P') (hQ : Q ≤ Q') : P.par Q ≤ P'.par Q' :=
  closure_mono (parGen_mono hP hQ)

/-- **Symmetry** (Table 3, journal p.44), for every rule set.  Original work:
the paper claims it without proof. -/
theorem par_swap (P : Comp R Loc Val A) (Q : Comp R Loc Val B) :
    (P.par Q).traces = PreTrace.mapRet Prod.swap '' (Q.par P).traces := by
  rw [traces_par, traces_par, parGen_swap P.traces Q.traces,
    closure_image_mapRet Prod.swap Prod.swap (fun _ ↦ Prod.swap_swap _)
      (fun _ ↦ Prod.swap_swap _)]

/-- `⊥` is an annihilator for `∥∥∥` on the left. -/
@[simp] theorem bot_par (Q : Comp R Loc Val B) :
    (⊥ : Comp R Loc Val A).par Q = ⊥ := by
  apply ext
  rw [traces_par]
  have h : parGen (⊥ : Comp R Loc Val A).traces Q.traces = ∅ := by
    ext π
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨τ, hτ, -⟩
    exact absurd hτ (by simp)
  rw [h, closure_empty, traces_bot]

/-- `⊥` is an annihilator for `∥∥∥` on the right. -/
@[simp] theorem par_bot (P : Comp R Loc Val A) :
    P.par (⊥ : Comp R Loc Val B) = ⊥ := by
  apply ext
  rw [traces_par]
  have h : parGen P.traces (⊥ : Comp R Loc Val B).traces = ∅ := by
    ext π
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨τ, -, υ, hυ, -⟩
    exact absurd hυ (by simp)
  rw [h, closure_empty, traces_bot]

end Comp

end Isotope.Elgot.RA
