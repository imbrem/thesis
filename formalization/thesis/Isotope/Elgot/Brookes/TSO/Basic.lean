import Isotope.Elgot.Brookes.SeqCst

/-!
# Store-buffer states for a Brookes-style TSO model

The paper's TSO semantics (`\citet{sparky}`, transcribed at
`papers/isotope/denotational-semantics-of-ssa.tex` lines 4740-5008) is built from
*pomsets* over the alphabet `𝒜_TSO = 𝒜_PO ∪ 𝒜_b`, with `TSO = StateT Buf (Traces Σ)`
and a post-filter cutting out the executions that never flush.  **That is not what
this file builds**; see `Isotope/Elgot/Brookes/TSO.lean` for the honest boundary.

Instead we follow the paper's own suggestion at lines 5191-5193 — "more complex
states (e.g. involving per-thread buffers) and closure operators can allow us to
model weak memory models" — and take the *interleaving* reading: a TSO state is
global memory together with one FIFO write buffer per thread, and traces are
Brookes rely-guarantee words over that state.  Nothing here is new closure
machinery: the rules are still stuttering and mumbling, at a richer state.

The buffer API is the paper's, transposed to append-at-the-end orientation:
`Buf.peek` is `[·]_x` of lines 4827-4839 ("writes at the *end* of the buffer are
prioritized, since later writes overwrite earlier ones"), `St.push` is the effect
of `x̄ := v`, and `FlushRel` commits the oldest buffered write, which is the event
the paper writes `x := v`.
-/

namespace Isotope.Elgot.Brookes

universe u

namespace TSO

variable {Tid Loc Val : Type u}

/-- A per-thread FIFO write buffer: the pending writes, oldest first. -/
abbrev Buf (Loc Val : Type u) : Type u := List (Loc × Val)

/-- The paper's buffer lookup `[·]_ℓ : Buf → Val ⊔ {⊥}` (lines 4827-4839): the
value of the *latest* buffered write to `ℓ`, if there is one. -/
def Buf.peek [DecidableEq Loc] (ℓ : Loc) : Buf Loc Val → Option Val
  | [] => none
  | (k, v) :: L =>
    match Buf.peek ℓ L with
    | some w => some w
    | none => if k = ℓ then some v else none

@[simp] theorem Buf.peek_nil [DecidableEq Loc] (ℓ : Loc) :
    Buf.peek (Val := Val) ℓ [] = none := rfl

theorem Buf.peek_cons [DecidableEq Loc] (ℓ k : Loc) (v : Val) (L : Buf Loc Val) :
    Buf.peek ℓ ((k, v) :: L) =
      match Buf.peek ℓ L with
      | some w => some w
      | none => if k = ℓ then some v else none := rfl

/-- The paper's second lookup equation: a trailing write to `ℓ` wins. -/
theorem Buf.peek_append_self [DecidableEq Loc] (ℓ : Loc) (v : Val) (L : Buf Loc Val) :
    Buf.peek ℓ (L ++ [(ℓ, v)]) = some v := by
  induction L with
  | nil => simp [Buf.peek]
  | cons p L ih => obtain ⟨k, w⟩ := p; rw [List.cons_append, Buf.peek_cons, ih]

/-- The paper's third lookup equation: a trailing write elsewhere is ignored. -/
theorem Buf.peek_append_ne [DecidableEq Loc] {ℓ k : Loc} (h : k ≠ ℓ) (v : Val)
    (L : Buf Loc Val) : Buf.peek ℓ (L ++ [(k, v)]) = Buf.peek ℓ L := by
  induction L with
  | nil => simp [Buf.peek, h]
  | cons p L ih => obtain ⟨m, w⟩ := p; rw [List.cons_append, Buf.peek_cons, ih, Buf.peek_cons]

/-- The TSO machine state: global memory, plus one write buffer per thread. -/
structure St (Tid Loc Val : Type u) : Type u where
  /-- The globally visible store. -/
  mem : Loc → Val
  /-- The pending buffered writes of each thread. -/
  buf : Tid → Buf Loc Val

@[ext] theorem St.ext {s t : St Tid Loc Val} (hm : s.mem = t.mem) (hb : s.buf = t.buf) :
    s = t := by cases s; cases t; cases hm; cases hb; rfl

/-- Write `v` to `ℓ` in global memory. -/
def St.setMem [DecidableEq Loc] (s : St Tid Loc Val) (ℓ : Loc) (v : Val) : St Tid Loc Val :=
  { s with mem := Function.update s.mem ℓ v }

/-- Append `ℓ := v` to thread `i`'s write buffer; this is the paper's `ℓ̄ := v`. -/
def St.push [DecidableEq Tid] (s : St Tid Loc Val) (i : Tid) (ℓ : Loc) (v : Val) :
    St Tid Loc Val :=
  { s with buf := Function.update s.buf i (s.buf i ++ [(ℓ, v)]) }

/-- The value thread `i` observes at `ℓ`: its own buffered write if it has one,
otherwise global memory.  This is the paper's read rule (line 4845) with the
buffer-miss case resolved by memory rather than by an arbitrary value, since our
state carries memory and no post-filter is available. -/
def St.observe [DecidableEq Loc] (s : St Tid Loc Val) (i : Tid) (ℓ : Loc) : Val :=
  (Buf.peek ℓ (s.buf i)).getD (s.mem ℓ)

@[simp] theorem St.mem_setMem [DecidableEq Loc] (s : St Tid Loc Val) (ℓ : Loc) (v : Val) :
    (s.setMem ℓ v).mem = Function.update s.mem ℓ v := rfl

@[simp] theorem St.buf_setMem [DecidableEq Loc] (s : St Tid Loc Val) (ℓ : Loc) (v : Val) :
    (s.setMem ℓ v).buf = s.buf := rfl

@[simp] theorem St.mem_push [DecidableEq Tid] (s : St Tid Loc Val) (i : Tid) (ℓ : Loc) (v : Val) :
    (s.push i ℓ v).mem = s.mem := rfl

@[simp] theorem St.buf_push [DecidableEq Tid] (s : St Tid Loc Val) (i : Tid) (ℓ : Loc) (v : Val) :
    (s.push i ℓ v).buf = Function.update s.buf i (s.buf i ++ [(ℓ, v)]) := rfl

/-- One buffer-commit step of thread `i`: the *oldest* pending write is applied to
global memory.  This is where the paper's globally visible `ℓ := v` event happens;
unlike the paper (line 4848) we do not also emit it when the write is issued,
because in an interleaving reading that would place the write in global order
before it is visible. -/
def FlushRel [DecidableEq Tid] [DecidableEq Loc] (i : Tid) (s s' : St Tid Loc Val) : Prop :=
  ∃ (ℓ : Loc) (v : Val) (β : Buf Loc Val),
    s.buf i = (ℓ, v) :: β ∧
      s' = { mem := Function.update s.mem ℓ v, buf := Function.update s.buf i β }

theorem FlushRel.buf_ne_nil [DecidableEq Tid] [DecidableEq Loc] {i : Tid}
    {s s' : St Tid Loc Val} (h : FlushRel i s s') : s.buf i ≠ [] := by
  obtain ⟨ℓ, v, β, hb, -⟩ := h
  rw [hb]; exact List.cons_ne_nil _ _

/-- A flush leaves every other thread's buffer alone. -/
theorem FlushRel.buf_other [DecidableEq Tid] [DecidableEq Loc] {i : Tid}
    {s s' : St Tid Loc Val} (h : FlushRel i s s') {k : Tid} (hk : k ≠ i) :
    s'.buf k = s.buf k := by
  obtain ⟨ℓ, v, β, -, rfl⟩ := h
  exact Function.update_of_ne hk _ _

end TSO

end Isotope.Elgot.Brookes
