import Isotope.Elgot.Brookes.TSO.Basic

/-!
# The store-buffer TSO computations

`TSO.Comp Tid Loc Val` is the Brookes monad of `Isotope/Elgot/Brookes/Monad.lean`
instantiated at the stuttering/mumbling rewriting system over the store-buffer
state `TSO.St`.  **Every monad law, the iteration operator, and all four Elgot
laws are therefore inherited, not reproved**: `Monad`, `LawfulMonad`, `Iterate`
and `LawfulElgotMonad` instances are already available for `Brookes c` at an
arbitrary `c`.  This file only supplies the *operations*.

Following the paper (lines 4841-4850) each memory operation is sandwiched between
partial buffer flushes, `pflush`.  The paper needs the idempotent-envelope
category `Ide(Set_TSO, pflush)` (lines 4908-4939) to make `pflush` the identity;
here the same content is available directly as the equations `pflush_idem`,
`pflush_write`, `write_pflush`, `pflush_read`, `read_pflush`, `pflush_fence` —
so no `Ide` construction is needed.  `pflush_idem` is the lemma the paper uses at
lines 4913-4918 but never proves.

## Deliberate divergences from the paper

* The global write event is emitted when a buffered write *drains* (`FlushRel`),
  not when it is issued as the paper's `W_x^TSO` does (line 4848); under an
  interleaving reading, emitting it at issue time would order it globally before
  it is visible.
* A read that misses in the buffer reads global memory, rather than an arbitrary
  value later cut down by a post-filter (line 4845).
* Rely steps are unconstrained, as in any Brookes monad: nothing in the *monad*
  stops the environment from rewriting this thread's own buffer.  That is
  recovered where it belongs, in parallel composition (`TSO/Litmus.lean`), by
  interleaving traces of threads that only touch their own buffers.
-/

namespace Isotope.Elgot.Brookes

universe u

namespace TSO

variable {Tid Loc Val : Type u}

/-- Traces of the store-buffer TSO model: Brookes rely-guarantee words over `St`. -/
abbrev Tr (Tid Loc Val : Type u) : Type u := Trace (St Tid Loc Val × St Tid Loc Val)

/-- The store-buffer TSO monad: the Brookes monad at the stuttering/mumbling
closure over `St Tid Loc Val`. -/
abbrev Comp (Tid Loc Val A : Type u) : Type u :=
  Brookes (SeqCst.rewriting (St Tid Loc Val)) A

section Ops

variable [DecidableEq Tid] [DecidableEq Loc]

/-- Every step of the trace commits one of thread `i`'s buffered writes.  Gaps
between steps are environment interference, exactly as elsewhere in the model. -/
def FlushTrace (i : Tid) (t : Tr Tid Loc Val) : Prop := ∀ p ∈ t, FlushRel i p.1 p.2

@[simp] theorem flushTrace_nil (i : Tid) : FlushTrace i ([] : Tr Tid Loc Val) := by
  intro p hp; exact absurd hp (List.not_mem_nil)

theorem flushTrace_append {i : Tid} {t u : Tr Tid Loc Val}
    (ht : FlushTrace i t) (hu : FlushTrace i u) : FlushTrace i (t ++ u) := by
  intro p hp
  rcases List.mem_append.1 hp with h | h
  · exact ht p h
  · exact hu p h

/-- The paper's `pflush` (lines 4852-4855): commit some prefix of this thread's
write buffer, emitting the commits.  Doing nothing is allowed. -/
def pflush (i : Tid) : Comp Tid Loc Val PUnit :=
  close _ {p | FlushTrace i p.1}

/-- Issue a write: append `ℓ := v` to thread `i`'s buffer.  This is the paper's
buffer action `ℓ̄ := v`, and it changes no memory. -/
def writeCore (i : Tid) (ℓ : Loc) (v : Val) : Comp Tid Loc Val PUnit :=
  close _ {p | ∃ s : St Tid Loc Val, p.1 = [(s, s.push i ℓ v)]}

/-- Perform a read: rely on some state, guarantee it unchanged, and return the
value thread `i` observes at `ℓ`. -/
def readCore (i : Tid) (ℓ : Loc) : Comp Tid Loc Val Val :=
  close _ {p | ∃ s : St Tid Loc Val, p.1 = [(s, s)] ∧ p.2 = s.observe i ℓ}

/-- The paper's `W_ℓ^TSO = pflush ; (buffer the write) ; pflush` (line 4848). -/
def write (i : Tid) (ℓ : Loc) (v : Val) : Comp Tid Loc Val PUnit :=
  pflush i >>= fun _ ↦ writeCore i ℓ v >>= fun _ ↦ pflush i

/-- The paper's `R_ℓ^TSO = pflush ; (observe ℓ) ; pflush` (line 4845). -/
def read (i : Tid) (ℓ : Loc) : Comp Tid Loc Val Val :=
  pflush i >>= fun _ ↦ readCore i ℓ >>= fun v ↦ pflush i >>= fun _ ↦ pure v

/-- Traces of a fence of thread `i`: commit buffered writes until the buffer is
empty, then a final stutter witnessing that it is.  The closing stutter cannot be
dropped, for the same reason `SeqCst.read` keeps one: the empty trace records no
state, so it could not witness an empty buffer. -/
inductive Fences (i : Tid) : Tr Tid Loc Val → Prop
  | /-- The buffer is empty; record the state and stop. -/
    done {s : St Tid Loc Val} : s.buf i = [] → Fences i [(s, s)]
  | /-- Commit the oldest buffered write and continue. -/
    step {s s' : St Tid Loc Val} {t : Tr Tid Loc Val} :
      FlushRel i s s' → Fences i t → Fences i ((s, s') :: t)

/-- The paper's `⟦fence⟧` (lines 4860-4862): drain thread `i`'s buffer entirely. -/
def fence (i : Tid) : Comp Tid Loc Val PUnit :=
  close _ {p | Fences i p.1}

/-! ## The sequentially consistent fragment

The same state, but writes go straight to memory and reads come straight from it:
no buffer is touched, so these are the sequentially consistent operations, living
in the very same monad.  This is what makes the TSO/SC comparison of
`TSO/Litmus.lean` a statement about one trace order rather than a translation. -/

/-! ## Membership -/

theorem mem_pflush_iff (i : Tid) (t : Tr Tid Loc Val) (x : PUnit) :
    (t, x) ∈ pflush i ↔ ∃ t₀, FlushTrace i t₀ ∧ (SeqCst.rewriting _).Refines t₀ t := Iff.rfl

theorem mem_pflush {i : Tid} {t : Tr Tid Loc Val} (h : FlushTrace i t) (x : PUnit) :
    (t, x) ∈ pflush i := ⟨t, h, .refl⟩

theorem nil_mem_pflush (i : Tid) (x : PUnit) : (([] : Tr Tid Loc Val), x) ∈ pflush i :=
  mem_pflush (flushTrace_nil i) x

omit [DecidableEq Loc] in
theorem mem_writeCore (i : Tid) (ℓ : Loc) (v : Val) (s : St Tid Loc Val) (x : PUnit) :
    ([(s, s.push i ℓ v)], x) ∈ writeCore i ℓ v := ⟨_, ⟨s, rfl⟩, .refl⟩

omit [DecidableEq Tid] in
theorem mem_readCore (i : Tid) (ℓ : Loc) (s : St Tid Loc Val) :
    ([(s, s)], s.observe i ℓ) ∈ readCore i ℓ := ⟨_, ⟨s, rfl, rfl⟩, .refl⟩

theorem mem_fence {i : Tid} {t : Tr Tid Loc Val} (h : Fences i t) (x : PUnit) :
    (t, x) ∈ fence i := ⟨t, h, .refl⟩

/-! ## The `pflush` equations

These are the content the paper needs the idempotent envelope `Ide(Set_TSO, pflush)`
for (lines 4908-4939); as equations between operations they need no new category. -/

/-- The paper's unproved lemma `pflush ; pflush = pflush` (used at lines 4913-4918). -/
@[simp] theorem pflush_idem (i : Tid) :
    (pflush i >>= fun _ ↦ pflush i : Comp Tid Loc Val PUnit) = pflush i := by
  apply Brookes.ext_mem
  intro t x
  rw [Brookes.mem_bind_iff]
  constructor
  · rintro ⟨a, u, v, hu', hv', hr⟩
    obtain ⟨u₀, hu₀, hu⟩ := (mem_pflush_iff i u _).1 hu'
    obtain ⟨v₀, hv₀, hv⟩ := (mem_pflush_iff i v _).1 hv'
    exact ⟨u₀ ++ v₀, flushTrace_append hu₀ hv₀,
      (Rewriting.refines_append hu hv).trans hr⟩
  · intro h
    exact ⟨PUnit.unit, [], t, nil_mem_pflush i PUnit.unit, h, by rw [List.nil_append]⟩

/-- Two consecutive partial flushes are one. -/
@[simp] theorem pflush_pflush_bind {A : Type u} (i : Tid) (f : PUnit → Comp Tid Loc Val A) :
    (pflush i >>= fun _ ↦ pflush i >>= f) = pflush i >>= f := by
  rw [← bind_assoc, pflush_idem]

@[simp] theorem pflush_write (i : Tid) (ℓ : Loc) (v : Val) :
    (pflush i >>= fun _ ↦ write i ℓ v : Comp Tid Loc Val PUnit) = write i ℓ v := by
  rw [write, ← bind_assoc, pflush_idem]

@[simp] theorem write_pflush (i : Tid) (ℓ : Loc) (v : Val) :
    (write i ℓ v >>= fun _ ↦ pflush i : Comp Tid Loc Val PUnit) = write i ℓ v := by
  simp only [write, bind_assoc, pflush_idem]

@[simp] theorem pflush_read (i : Tid) (ℓ : Loc) :
    (pflush i >>= fun _ ↦ read i ℓ : Comp Tid Loc Val Val) = read i ℓ := by
  rw [read, ← bind_assoc, pflush_idem]

@[simp] theorem read_pflush (i : Tid) (ℓ : Loc) :
    (read i ℓ >>= fun v ↦ pflush i >>= fun _ ↦ pure v : Comp Tid Loc Val Val) = read i ℓ := by
  simp only [read, bind_assoc, pure_bind, pflush_pflush_bind]

/-- Flushing before a fence is redundant: the fence drains the buffer anyway. -/
@[simp] theorem pflush_fence (i : Tid) :
    (pflush i >>= fun _ ↦ fence i : Comp Tid Loc Val PUnit) = fence i := by
  have hcat : ∀ {t u : Tr Tid Loc Val}, FlushTrace i t → Fences i u → Fences i (t ++ u) := by
    intro t
    induction t with
    | nil => intro _ _ hu; exact hu
    | cons p t ih =>
      intro u ht hu
      obtain ⟨s, s'⟩ := p
      exact Fences.step (ht (s, s') (by simp)) (ih (fun q hq ↦ ht q (by simp [hq])) hu)
  apply Brookes.ext_mem
  intro t x
  rw [Brookes.mem_bind_iff]
  constructor
  · rintro ⟨a, u, v, hu', hv', hr⟩
    obtain ⟨u₀, hu₀, hu⟩ := (mem_pflush_iff i u _).1 hu'
    obtain ⟨v₀, hv₀, hv⟩ := hv'
    exact ⟨u₀ ++ v₀, hcat hu₀ hv₀, (Rewriting.refines_append hu hv).trans hr⟩
  · intro h
    exact ⟨PUnit.unit, [], t, nil_mem_pflush i PUnit.unit, h, by rw [List.nil_append]⟩

/-! ## Fences really drain -/

/-- A fence trace is never empty: it always records the drained state. -/
theorem Fences.ne_nil {i : Tid} {t : Tr Tid Loc Val} (h : Fences i t) : t ≠ [] := by
  cases h <;> exact List.cons_ne_nil _ _

/-- A fence trace ends with a stutter at a state in which thread `i`'s buffer is
empty: after a fence, nothing of thread `i`'s is left pending. -/
theorem Fences.getLast_drained {i : Tid} {t : Tr Tid Loc Val} (h : Fences i t) :
    ∃ s : St Tid Loc Val, t.getLast? = some (s, s) ∧ s.buf i = [] := by
  induction h with
  | done hs => exact ⟨_, rfl, hs⟩
  | step _ ht ih =>
    obtain ⟨s, hlast, hbuf⟩ := ih
    obtain ⟨q, t', rfl⟩ := List.exists_cons_of_ne_nil (Fences.ne_nil ht)
    rw [List.getLast?_cons_cons]
    exact ⟨s, hlast, hbuf⟩

/-- A fence is not the trivial computation: it always contributes a step. -/
theorem fence_ne_pure (i : Tid) :
    (fence i : Comp Tid Loc Val PUnit) ≠ pure PUnit.unit := by
  intro h
  have hmem : (([] : Tr Tid Loc Val), PUnit.unit) ∈ fence i :=
    h ▸ Brookes.mem_pure (c := SeqCst.rewriting (St Tid Loc Val)) PUnit.unit
  obtain ⟨t₀, ht₀, hr⟩ := hmem
  exact Fences.ne_nil ht₀ (SeqCst.refines_nil hr)

end Ops

/-! ## The sequentially consistent fragment

The same state and the same monad, but writes go straight to memory and reads
come straight from it: no buffer is touched, so these are the sequentially
consistent operations.  Having both fragments in *one* monad is what makes the
TSO/SC comparison of `TSO/Litmus.lean` a statement about one set of traces rather
than a translation between two models. -/

/-- A sequentially consistent write: memory is updated in a single step. -/
def writeSC [DecidableEq Loc] (ℓ : Loc) (v : Val) : Comp Tid Loc Val PUnit :=
  close _ {p | ∃ s : St Tid Loc Val, p.1 = [(s, s.setMem ℓ v)]}

/-- A sequentially consistent read: global memory is observed in one stutter step. -/
def readSC (ℓ : Loc) : Comp Tid Loc Val Val :=
  close _ {p | ∃ s : St Tid Loc Val, p.1 = [(s, s)] ∧ p.2 = s.mem ℓ}

theorem mem_writeSC [DecidableEq Loc] (ℓ : Loc) (v : Val) (s : St Tid Loc Val) (x : PUnit) :
    ([(s, s.setMem ℓ v)], x) ∈ (writeSC ℓ v : Comp Tid Loc Val PUnit) := ⟨_, ⟨s, rfl⟩, .refl⟩

theorem mem_readSC (ℓ : Loc) (s : St Tid Loc Val) :
    ([(s, s)], s.mem ℓ) ∈ (readSC ℓ : Comp Tid Loc Val Val) := ⟨_, ⟨s, rfl, rfl⟩, .refl⟩

end TSO

end Isotope.Elgot.Brookes
