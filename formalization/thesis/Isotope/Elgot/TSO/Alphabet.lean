import Isotope.Pomset

/-!
# The TSO action alphabet and buffers

`𝒜_TSO = 𝒜_PO ∪ 𝒜_b = 𝒜_w ∪ 𝒜_r ∪ {δ} ∪ 𝒜_b`
(`denotational-semantics-of-ssa.tex` L4766-4769, L4818-4821), buffers `Buf = 𝒜_b*` read as
linear pomsets over `𝒜_TSO` ordered by index, and the buffer lookup `[·]_x` of L4827-4838.

The key structural fact is `Buf.toPom_inj`: the reading of a buffer as a linear pomset is
*injective*, so no information is lost in the pomset presentation.

## Honest boundary

Locations and values are arbitrary types; nothing here fixes `Word`.  The alphabet is a plain
inductive type, so `𝒜_PO` is the `tick`/`read`/`write` fragment and `𝒜_b` the `buf` fragment;
they are not carved out as separate types.
-/

universe u

namespace Isotope.Elgot.TSO

open Isotope.Pomset

/-- The TSO action alphabet `𝒜_TSO`: the null action `δ`, reads `x = v`, writes `x := v`, and
buffer writes `b(x) := v`. -/
inductive Act (Loc Val : Type u) : Type u
  /-- The null action `δ`. -/
  | tick
  /-- A read `x = v`. -/
  | read (x : Loc) (v : Val)
  /-- A global write `x := v`. -/
  | write (x : Loc) (v : Val)
  /-- A buffered write `b(x) := v`. -/
  | buf (x : Loc) (v : Val)

instance instTick {Loc Val : Type u} : Tick (Act Loc Val) := ⟨Act.tick⟩

/-- `Buf = 𝒜_b*`, oldest first; new writes are appended at the **end**. -/
abbrev Buf (Loc Val : Type u) : Type u := List (Loc × Val)

variable {Loc Val : Type u}

instance instIsEmptyLiveNil {A : Type u} [Tick A] :
    IsEmpty ((PrePom.ofList ([] : List A)).toLPoset.Live tick) := ⟨fun x => x.1.elim0⟩

/-- A buffer read as a linear pomset over `𝒜_TSO`, with the empty buffer denoting `{δ} = 1`. -/
def Buf.toPom (L : Buf Loc Val) : Pom (Act Loc Val) :=
  Pom.mk (PrePom.ofList (L.map fun p => Act.buf p.1 p.2))

@[simp] theorem Buf.toPom_nil : Buf.toPom ([] : Buf Loc Val) = 1 := by
  simp only [Buf.toPom, List.map_nil]
  exact Quotient.sound ⟨DIso.ofIsEmpty⟩

/-- Concatenating buffers is concatenating their pomsets. -/
theorem Buf.toPom_append (L L' : Buf Loc Val) :
    Buf.toPom (L ++ L') = Buf.toPom L * Buf.toPom L' := by
  simp only [Buf.toPom, List.map_append]
  exact Quotient.sound (PrePom.ofList_append _ _)

theorem Act.buf_injective :
    Function.Injective (fun p : Loc × Val => Act.buf p.1 p.2) := by
  rintro ⟨x, v⟩ ⟨y, w⟩ h
  simp only [Act.buf.injEq] at h
  simp [h.1, h.2]

/-- **Buffers embed faithfully as linear pomsets.**  Distinct buffers denote distinct
pomsets, so nothing is lost by the paper's reading of `Buf = 𝒜_b*` as linear pomsets over
`𝒜_TSO`.  This is the concrete payoff of `PrePom.ofList_deq_iff`. -/
theorem Buf.toPom_inj {L L' : Buf Loc Val} : Buf.toPom L = Buf.toPom L' ↔ L = L' := by
  constructor
  · intro h
    have hfree : ∀ K : Buf Loc Val,
        (tick : Act Loc Val) ∉ K.map fun p => Act.buf p.1 p.2 := by
      intro K hmem
      obtain ⟨p, _, hp⟩ := List.mem_map.mp hmem
      have h2 : Act.buf p.1 p.2 = (Act.tick : Act Loc Val) := hp
      exact absurd h2 (by simp)
    have := (PrePom.ofList_deq_iff (hfree L) (hfree L')).1 (Pom.mk_eq_mk.1 h)
    exact List.map_injective_iff.mpr Act.buf_injective this
  · rintro rfl; rfl

section Peek

variable [DecidableEq Loc]

/-- The buffer lookup `[·]_x` of L4827-4838: the value of the **latest** buffered write to
`x`, if any.  Later writes overwrite earlier ones. -/
def Buf.peek (x : Loc) : Buf Loc Val → Option Val
  | [] => none
  | (y, v) :: L =>
      match Buf.peek x L with
      | some w => some w
      | none => if y = x then some v else none

/-- `[][x] = ⊥` (L4836). -/
@[simp] theorem Buf.peek_nil (x : Loc) : Buf.peek (Val := Val) x [] = none := rfl

/-- `(L;{b(x) := v})[x] = v` (L4830): a write at the end of the buffer wins. -/
@[simp] theorem Buf.peek_append_self (x : Loc) (v : Val) (L : Buf Loc Val) :
    Buf.peek x (L ++ [(x, v)]) = some v := by
  induction L with
  | nil => simp [Buf.peek]
  | cons p L ih => simp [Buf.peek, ih]

/-- `(L;{b(y) := v})[x] = L[x]` for `y ≠ x` (L4833). -/
@[simp] theorem Buf.peek_append_other {x y : Loc} (hxy : y ≠ x) (v : Val) (L : Buf Loc Val) :
    Buf.peek x (L ++ [(y, v)]) = Buf.peek x L := by
  induction L with
  | nil => simp [Buf.peek, hxy]
  | cons p L ih => simp [Buf.peek, ih]

/-- Later writes overwrite earlier ones (L4838). -/
theorem Buf.peek_later_wins (x : Loc) (v w : Val) (L : Buf Loc Val) :
    Buf.peek x (L ++ [(x, v)] ++ [(x, w)]) = some w :=
  Buf.peek_append_self x w (L ++ [(x, v)])

end Peek

end Isotope.Elgot.TSO
