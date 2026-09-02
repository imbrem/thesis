import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Order.Basic
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

/-- The half-open segment `ν.seg := [ν.i, ν.t)`. -/
def seg (ν : Msg Loc Val) : Set ℚ := Set.Ico ν.i ν.t

theorem i_lt_t (ν : Msg Loc Val) : ν.i < ν.t := ν.lt

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

end Isotope.Elgot.RA
