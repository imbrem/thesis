import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Order.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Logic.Relation

/-!
# Release/acquire states: views, messages, and memories

This is a transcription of the *state* apparatus of

> Yotam Dvir, Ohad Kammar and Ori Lahav,
> *A Denotational Approach to Release/Acquire Concurrency*, ESOP 2024
> (bib key `release-acquire`; §5.1 of the ESOP full version, §6.1 of the
> TOPLAS journal version *A Brookes-Style Denotational Semantics for
> Release/Acquire Concurrency*),

namely views `View = ℚ^Loc`, messages `ν = ℓ:v@[q, κℓ)⟪κ⟫`, the points-to and
points-downwards-into relations, and well-formed memories.

Deviations from the paper are recorded in `Isotope/Elgot/RA.lean`.  The one that
matters here: the paper says "a memory is a finite non-empty set of messages"
and then reserves `Mem` for the *well-formed* ones.  We take `Memory` to be an
arbitrary set of messages and fold finiteness and non-emptiness into
`WellFormed`, which is where the paper's `Mem` is actually used.
-/

namespace Isotope.Elgot.RA

/-- A view assigns a timestamp to every location: the paper's `View := ℚ^Loc`,
ordered pointwise by the ambient `Pi` order. -/
abbrev View (Loc : Type) : Type := Loc → ℚ

/-- A message `ν = ℓ:v@[q, κ ℓ)⟪κ⟫`, carrying its own view `κ`; the paper's
side condition `q < κ ℓ` is the field `lt`. -/
structure Msg (Loc Val : Type) where
  /-- The location written. -/
  lc : Loc
  /-- The value written. -/
  vl : Val
  /-- The initial timestamp of the message's segment. -/
  i : ℚ
  /-- The view carried by the message. -/
  vw : View Loc
  /-- The paper's side condition: the segment is non-empty. -/
  lt : i < vw lc

namespace Msg

variable {Loc Val : Type}

/-- The final timestamp `ν.t := ν.vw ν.lc`, read out of the carried view. -/
def t (ν : Msg Loc Val) : ℚ := ν.vw ν.lc

/-- The half-open segment `ν.seg := (ν.i, ν.t]`, open below and closed above.
Journal §5.1, p.16: "the message's two timestamps delimit the segment of the
message: the interval `ν.seg ≜ (ν.i, ν.t]`". -/
def seg (ν : Msg Loc Val) : Set ℚ := Set.Ioc ν.i ν.t

theorem i_lt_t (ν : Msg Loc Val) : ν.i < ν.t := ν.lt

theorem t_mem_seg (ν : Msg Loc Val) : ν.t ∈ ν.seg := ⟨ν.lt, le_refl _⟩

/-- A message's segment determines its two timestamps. -/
theorem seg_eq_iff {ν ε : Msg Loc Val} : ν.seg = ε.seg ↔ ν.i = ε.i ∧ ν.t = ε.t := by
  constructor
  · intro h
    have h₁ := (Set.Ioc_subset_Ioc_iff ν.lt).mp h.subset
    have h₂ := (Set.Ioc_subset_Ioc_iff ε.lt).mp h.symm.subset
    exact ⟨le_antisymm h₂.2 h₁.2, le_antisymm h₁.1 h₂.1⟩
  · rintro ⟨h₁, h₂⟩; simp [seg, h₁, h₂]

/-- The *interior* of a segment: the paper's `ε.seg \ {ε.t}`, used in
Lemma 7.6. -/
theorem seg_diff_t (ν : Msg Loc Val) : ν.seg \ {ν.t} = Set.Ioo ν.i ν.t := by
  ext q
  simp only [seg, Set.mem_diff, Set.mem_Ioc, Set.mem_singleton_iff, Set.mem_Ioo]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact ⟨h₁, lt_of_le_of_ne h₂ h₃⟩
  · rintro ⟨h₁, h₂⟩; exact ⟨⟨h₁, le_of_lt h₂⟩, ne_of_lt h₂⟩

end Msg

/-- A memory is a set of messages.  (The paper additionally requires finiteness
and non-emptiness; see `WellFormed`.) -/
abbrev Memory (Loc Val : Type) : Type := Set (Msg Loc Val)

variable {Loc Val : Type}

/-- `κ ↣ ν`: the view `κ` points to the message `ν`. -/
def PointsTo (κ : View Loc) (ν : Msg Loc Val) : Prop := κ ν.lc = ν.t

/-- `κ ↠ ν`: the view `κ` points *downwards* to `ν`, i.e. points to it and
dominates the view it carries. -/
def PointsDownTo (κ : View Loc) (ν : Msg Loc Val) : Prop :=
  PointsTo κ ν ∧ ν.vw ≤ κ

/-- `κ ↣ μ`: `κ` points to some message of `μ` at every location. -/
def PointsInto (κ : View Loc) (μ : Memory Loc Val) : Prop :=
  ∀ ℓ : Loc, ∃ ν ∈ μ, ν.lc = ℓ ∧ PointsTo κ ν

/-- `κ ↠ μ`: `κ` points downwards into `μ`, i.e. points downwards to some
message of `μ` at every location. -/
def PointsDownInto (κ : View Loc) (μ : Memory Loc Val) : Prop :=
  ∀ ℓ : Loc, ∃ ν ∈ μ, ν.lc = ℓ ∧ PointsDownTo κ ν

theorem PointsDownTo.toPointsTo {κ : View Loc} {ν : Msg Loc Val}
    (h : PointsDownTo κ ν) : PointsTo κ ν := h.1

theorem PointsDownInto.toPointsInto {κ : View Loc} {μ : Memory Loc Val}
    (h : PointsDownInto κ μ) : PointsInto κ μ :=
  fun ℓ ↦ let ⟨ν, hν, hl, hp⟩ := h ℓ; ⟨ν, hν, hl, hp.1⟩

/-- Pointing downwards into a memory is monotone in the memory: this is the one
fact about the state layer that the monad laws actually use. -/
theorem PointsDownInto.mono {κ : View Loc} {μ ρ : Memory Loc Val}
    (h : PointsDownInto κ μ) (hsub : μ ⊆ ρ) : PointsDownInto κ ρ :=
  fun ℓ ↦ let ⟨ν, hν, hl, hp⟩ := h ℓ; ⟨ν, hsub hν, hl, hp⟩

theorem PointsInto.mono {κ : View Loc} {μ ρ : Memory Loc Val}
    (h : PointsInto κ μ) (hsub : μ ⊆ ρ) : PointsInto κ ρ :=
  fun ℓ ↦ let ⟨ν, hν, hl, hp⟩ := h ℓ; ⟨ν, hsub hν, hl, hp⟩

/-- `μ` is *scattered*: distinct messages at the same location have disjoint
segments. -/
def Scattered (μ : Memory Loc Val) : Prop :=
  ∀ ν ∈ μ, ∀ ε ∈ μ, ν.lc = ε.lc → (ν.seg ∩ ε.seg).Nonempty → ν = ε

/-- `μ` is *connected*: it is scattered and every message points into it. -/
def Connected (μ : Memory Loc Val) : Prop :=
  Scattered μ ∧ ∀ ν ∈ μ, PointsInto ν.vw μ

/-- `μ` is *causally connected*: it is connected and every message points
downwards into it. -/
def CausallyConnected (μ : Memory Loc Val) : Prop :=
  Connected μ ∧ ∀ ν ∈ μ, PointsDownInto ν.vw μ

/-- The paper's points-to digraph `μ.gph`, with the identity removed. -/
def Gph (μ : Memory Loc Val) (ν ε : Msg Loc Val) : Prop :=
  ν ∈ μ ∧ ε ∈ μ ∧ ν ≠ ε ∧ PointsTo ν.vw ε

/-- `ν` is the timestamp-minimal message of `μ` at its own location: the paper's
`ν = min μ (ν.lc)`. -/
def IsMinAt (μ : Memory Loc Val) (ν : Msg Loc Val) : Prop :=
  ν ∈ μ ∧ ∀ ε ∈ μ, ε.lc = ν.lc → ν.t ≤ ε.t

/-- A well-formed memory: the paper's `Mem`.  Finiteness and non-emptiness are
the paper's conditions on "memory"; the remaining three are its conditions on
well-formedness. -/
structure WellFormed (μ : Memory Loc Val) : Prop where
  /-- The paper's memories are finite. -/
  finite : μ.Finite
  /-- The paper's memories are non-empty. -/
  nonempty : μ.Nonempty
  /-- Well-formed memories are causally connected. -/
  causal : CausallyConnected μ
  /-- Every message on a cycle of the points-to digraph is minimal at its
  location. -/
  cycles : ∀ ν ∈ μ, Relation.TransGen (Gph μ) ν ν → IsMinAt μ ν

theorem WellFormed.scattered {μ : Memory Loc Val} (h : WellFormed μ) : Scattered μ :=
  h.causal.1.1

theorem WellFormed.pointsDownInto {μ : Memory Loc Val} (h : WellFormed μ)
    {ν : Msg Loc Val} (hν : ν ∈ μ) : PointsDownInto ν.vw μ := h.causal.2 ν hν

/-!
## The initial memory

The paper's initial memory: exactly one message per location, all carrying the
same view, which points downwards at all of them.  We need at least one
inhabitant of `WellFormed` for `pure` to be non-empty.
-/

/-- The message of the initial memory at location `ℓ`: value `v`, segment
`[t - 1, t)`, view constantly `t`. -/
def initialMsg (v : Val) (t : ℚ) (ℓ : Loc) : Msg Loc Val where
  lc := ℓ
  vl := v
  i := t - 1
  vw := fun _ ↦ t
  lt := by simp

@[simp] theorem initialMsg_lc (v : Val) (t : ℚ) (ℓ : Loc) :
    (initialMsg (Val := Val) v t ℓ).lc = ℓ := rfl

@[simp] theorem initialMsg_vl (v : Val) (t : ℚ) (ℓ : Loc) :
    (initialMsg (Val := Val) v t ℓ).vl = v := rfl

@[simp] theorem initialMsg_i (v : Val) (t : ℚ) (ℓ : Loc) :
    (initialMsg (Val := Val) v t ℓ).i = t - 1 := rfl

@[simp] theorem initialMsg_vw (v : Val) (t : ℚ) (ℓ : Loc) :
    (initialMsg (Val := Val) v t ℓ).vw = fun _ ↦ t := rfl

@[simp] theorem initialMsg_t (v : Val) (t : ℚ) (ℓ : Loc) :
    (initialMsg (Val := Val) v t ℓ).t = t := rfl

/-- The initial memory: one message per location, at value `v` and timestamp
`t`. -/
def initialMem (v : Val) (t : ℚ) : Memory Loc Val := Set.range (initialMsg v t)

@[simp] theorem mem_initialMem_iff {v : Val} {t : ℚ} {ν : Msg Loc Val} :
    ν ∈ initialMem (Loc := Loc) v t ↔ ν = initialMsg v t ν.lc := by
  constructor
  · rintro ⟨ℓ, rfl⟩; rfl
  · intro h; exact ⟨ν.lc, h.symm⟩

/-- The all-`t` view points downwards into the initial memory. -/
theorem pointsDownInto_initialMem (v : Val) (t : ℚ) :
    PointsDownInto (fun _ ↦ t : View Loc) (initialMem v t) :=
  fun ℓ ↦ ⟨initialMsg v t ℓ, ⟨ℓ, rfl⟩, rfl, rfl, le_refl _⟩

theorem initialMem_wellFormed [Finite Loc] [Nonempty Loc] (v : Val) (t : ℚ) :
    WellFormed (initialMem (Loc := Loc) v t) where
  finite := Set.finite_range _
  nonempty := ⟨initialMsg v t (Classical.arbitrary Loc), ⟨_, rfl⟩⟩
  causal := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro ν hν ε hε hlc -
      rw [mem_initialMem_iff] at hν hε
      rw [hν, hε, hlc]
    · rintro ν hν ℓ
      exact ⟨initialMsg v t ℓ, ⟨ℓ, rfl⟩, rfl, by
        rw [mem_initialMem_iff] at hν; rw [hν]; rfl⟩
    · rintro ν hν ℓ
      refine ⟨initialMsg v t ℓ, ⟨ℓ, rfl⟩, rfl, ?_, ?_⟩
      · rw [mem_initialMem_iff] at hν; rw [hν]; rfl
      · rw [mem_initialMem_iff] at hν
        intro ℓ'
        rw [hν]
        exact le_refl t
  cycles := by
    intro ν hν _
    refine ⟨hν, ?_⟩
    intro ε hε hlc
    rw [mem_initialMem_iff] at hν hε
    rw [hν, hε, hlc]

/-!
## Message orders, initial-timestamp update, and pulling

Transcribed from the journal version §7.3, pp.31–33 (ESOP full version §6.4,
pp.27–28).  The paper gives all four notions in prose rather than in a numbered
display:

```
ν ≤vw ε   ⟺   ν.lc = ε.lc ∧ ν.vl = ε.vl ∧ ν.seg = ε.seg ∧ ν.vw ≤ ε.vw   (p.31)
ν ⤙  ε    ⟺   ν.lc = ε.lc ∧ ν.t  = ε.i  ∧ ν.vw ≤ ε.vw                   (p.32)
ν ⤙= ε    ⟺   ν ⤙ ε ∧ ν.vl = ε.vl                                       (p.33)
κ[↑ε]     ≜   if κ ε.lc = ε.i then κ[ε.lc ↦ ε.t] else κ                  (p.32)
```

`Msg.setI` is the paper's `ε[i ↦ ν.i]`, which Table 2 renders typographically
and the Expel prose (p.32) spells out.  Its well-definedness is never checked in
the paper; it follows from `Dovetail`.

We formalize the *relaxed* dovetailing `ν.vw ≤ ε.vw` of Table 2, not the
equal-view variant drawn in Figs. 13–14.  The paper says twice (pp.32, 33) that
the two give the same semantics but proves neither claim, so we do not either.
-/

namespace Msg

/-- `ν ≤vw ε`: the paper's partial order on messages (journal p.31) — same
location, value and segment, with a smaller carried view.  The paper asserts
without proof that this is a partial order; see `LeVw.refl`, `LeVw.trans` and
`LeVw.antisymm`. -/
def LeVw (ν ε : Msg Loc Val) : Prop :=
  ν.lc = ε.lc ∧ ν.vl = ε.vl ∧ ν.seg = ε.seg ∧ ν.vw ≤ ε.vw

theorem LeVw.refl (ν : Msg Loc Val) : LeVw ν ν := ⟨rfl, rfl, rfl, le_refl _⟩

theorem LeVw.trans {ν ε ϑ : Msg Loc Val} (h₁ : LeVw ν ε) (h₂ : LeVw ε ϑ) : LeVw ν ϑ :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1,
    le_trans h₁.2.2.2 h₂.2.2.2⟩

theorem LeVw.antisymm {ν ε : Msg Loc Val} (h₁ : LeVw ν ε) (h₂ : LeVw ε ν) : ν = ε := by
  obtain ⟨hlc, hvl, hseg, hvw⟩ := h₁
  obtain ⟨-, -, -, hvw'⟩ := h₂
  obtain ⟨hi, -⟩ := seg_eq_iff.mp hseg
  cases ν; cases ε
  simp_all only [Msg.mk.injEq, true_and]
  exact le_antisymm hvw hvw'

/-- `ν ⤙ ε`: *monotone dovetailing* (journal p.32) — `ν`'s segment ends exactly
where `ε`'s begins, at the same location, with a smaller carried view. -/
def Dovetail (ν ε : Msg Loc Val) : Prop :=
  ν.lc = ε.lc ∧ ν.t = ε.i ∧ ν.vw ≤ ε.vw

/-- `ν ⤙= ε`: *monotone repetitive dovetailing* (journal p.33) — dovetailing
with the same value. -/
def DovetailEq (ν ε : Msg Loc Val) : Prop := Dovetail ν ε ∧ ν.vl = ε.vl

theorem Dovetail.i_lt_t {ν ε : Msg Loc Val} (h : Dovetail ν ε) : ν.i < ε.t :=
  lt_trans (lt_of_lt_of_le ν.lt (le_of_eq h.2.1)) ε.lt

/-- `ε[i ↦ q]`: `ε` with its initial timestamp replaced by `q`.  The paper's
`ε[i ↦ ν.i]` of the Expel rule (journal p.32). -/
def setI (ε : Msg Loc Val) (q : ℚ) (h : q < ε.t) : Msg Loc Val where
  lc := ε.lc
  vl := ε.vl
  i := q
  vw := ε.vw
  lt := h

@[simp] theorem setI_lc (ε : Msg Loc Val) (q : ℚ) (h : q < ε.t) : (ε.setI q h).lc = ε.lc := rfl
@[simp] theorem setI_vl (ε : Msg Loc Val) (q : ℚ) (h : q < ε.t) : (ε.setI q h).vl = ε.vl := rfl
@[simp] theorem setI_i (ε : Msg Loc Val) (q : ℚ) (h : q < ε.t) : (ε.setI q h).i = q := rfl
@[simp] theorem setI_vw (ε : Msg Loc Val) (q : ℚ) (h : q < ε.t) : (ε.setI q h).vw = ε.vw := rfl
@[simp] theorem setI_t (ε : Msg Loc Val) (q : ℚ) (h : q < ε.t) : (ε.setI q h).t = ε.t := rfl

end Msg

open Classical in
/-- `κ[↑ε]`: *pulling* the view `κ` along the message `ε` (journal p.32) — `κ`
is unchanged unless it points at `ε`'s initial timestamp, in which case it moves
up to `ε`'s final timestamp. -/
noncomputable def View.pull (ε : Msg Loc Val) (κ : View Loc) : View Loc :=
  fun ℓ ↦ if ℓ = ε.lc ∧ κ ε.lc = ε.i then ε.t else κ ℓ

theorem View.pull_of_ne {ε : Msg Loc Val} {κ : View Loc} {ℓ : Loc} (h : ℓ ≠ ε.lc) :
    View.pull ε κ ℓ = κ ℓ := by simp [View.pull, h]

theorem View.pull_lc_of_eq {ε : Msg Loc Val} {κ : View Loc} (h : κ ε.lc = ε.i) :
    View.pull ε κ ε.lc = ε.t := by simp [View.pull, h]

theorem View.pull_lc_of_ne {ε : Msg Loc Val} {κ : View Loc} (h : κ ε.lc ≠ ε.i) :
    View.pull ε κ ε.lc = κ ε.lc := by simp [View.pull, h]

theorem View.pull_eq_self {ε : Msg Loc Val} {κ : View Loc} (h : κ ε.lc ≠ ε.i) :
    View.pull ε κ = κ := by
  funext ℓ
  by_cases hℓ : ℓ = ε.lc
  · subst hℓ; exact View.pull_lc_of_ne h
  · exact View.pull_of_ne hℓ

/-- **Lemma 7.6** (journal p.33).  Pulling is monotone on views that do not
point into the *interior* of the pulled message's segment.  This is what carries
the seam condition `κ ⊑ σ` of `>>=` through a `Condense` rewrite.

(The hypothesis on `κ` is part of the paper's statement but is not needed for
the proof; we keep it so that the Lean statement is the paper's.) -/
theorem View.pull_le_pull {ε : Msg Loc Val} {κ σ : View Loc}
    (_hκ : κ ε.lc ∉ ε.seg \ {ε.t}) (hσ : σ ε.lc ∉ ε.seg \ {ε.t}) (h : κ ≤ σ) :
    View.pull ε κ ≤ View.pull ε σ := by
  rw [Msg.seg_diff_t, Set.mem_Ioo, not_and_or, not_lt, not_lt] at hσ
  intro ℓ
  by_cases hℓ : ℓ = ε.lc
  · subst hℓ
    by_cases hk : κ ε.lc = ε.i
    · rw [View.pull_lc_of_eq hk]
      by_cases hs : σ ε.lc = ε.i
      · rw [View.pull_lc_of_eq hs]
      · rw [View.pull_lc_of_ne hs]
        rcases hσ with hσ | hσ
        · exact absurd (le_antisymm hσ (hk ▸ h ε.lc)) hs
        · exact hσ
    · rw [View.pull_lc_of_ne hk]
      by_cases hs : σ ε.lc = ε.i
      · rw [View.pull_lc_of_eq hs]
        exact le_trans (hs ▸ h ε.lc) (le_of_lt ε.lt)
      · rw [View.pull_lc_of_ne hs]; exact h ε.lc
  · rw [View.pull_of_ne hℓ, View.pull_of_ne hℓ]; exact h ℓ

/-- `ν[↑ε]`: pulling a message, i.e. pulling the view it carries (journal
p.32).  Its location, value and initial timestamp are unchanged; its final
timestamp moves iff `ν` points at `ε`'s initial timestamp. -/
noncomputable def Msg.pull (ε ν : Msg Loc Val) : Msg Loc Val where
  lc := ν.lc
  vl := ν.vl
  i := ν.i
  vw := View.pull ε ν.vw
  lt := by
    by_cases hℓ : ν.lc = ε.lc
    · rw [hℓ]
      by_cases hk : ν.vw ε.lc = ε.i
      · rw [View.pull_lc_of_eq hk]
        exact lt_trans (lt_of_lt_of_le ν.lt (le_of_eq (hℓ ▸ hk))) ε.lt
      · rw [View.pull_lc_of_ne hk, ← hℓ]; exact ν.lt
    · rw [View.pull_of_ne hℓ]; exact ν.lt

@[simp] theorem Msg.pull_lc (ε ν : Msg Loc Val) : (Msg.pull ε ν).lc = ν.lc := rfl
@[simp] theorem Msg.pull_vl (ε ν : Msg Loc Val) : (Msg.pull ε ν).vl = ν.vl := rfl
@[simp] theorem Msg.pull_i (ε ν : Msg Loc Val) : (Msg.pull ε ν).i = ν.i := rfl
@[simp] theorem Msg.pull_vw (ε ν : Msg Loc Val) : (Msg.pull ε ν).vw = View.pull ε ν.vw := rfl

/-- `μ[↑ε]`: pulling a memory, pointwise (journal p.32). -/
noncomputable def Memory.pull (ε : Msg Loc Val) (μ : Memory Loc Val) : Memory Loc Val :=
  Msg.pull ε '' μ

theorem Memory.pull_mono {ε : Msg Loc Val} {μ ρ : Memory Loc Val} (h : μ ⊆ ρ) :
    Memory.pull ε μ ⊆ Memory.pull ε ρ := Set.image_mono h

@[simp] theorem Memory.pull_insert (ε ν : Msg Loc Val) (μ : Memory Loc Val) :
    Memory.pull ε (insert ν μ) = insert (Msg.pull ε ν) (Memory.pull ε μ) :=
  Set.image_insert_eq


end Isotope.Elgot.RA
