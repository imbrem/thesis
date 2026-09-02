import Isotope.Elgot.TSO.Basic

/-!
# The TSO operations

`pflush`, `read_x`, `write_x` and `fence`
(`denotational-semantics-of-ssa.tex` L4841-4862), together with the idempotence of `pflush`
that the paper's `PTSO` construction silently relies on (L4913-4918), and the `pflush`
sandwich equations that make `pflush` behave as an identity on the sandwiched operations.

## Honest boundary

* **Reads emit an arbitrary value on a buffer miss**, faithful to L4845.  No global memory is
  threaded, so nothing here proves TSO-correctness of an execution; the post-filter of
  L4781-4788 is not formalised.
* **Paper erratum (E2)**: L4848 gives `W_x^TSO` the return value `v`, while
  `write_x : ℐ₀^∅(Word, 𝟏)` at L4773 demands `()`.  We return `()`.
* **Paper erratum (E3)**: L4848 emits the global write `x := v` at write time while
  *simultaneously* buffering it.  This is coherent only under the post-filter reading; we
  transcribe it as written rather than silently switching to flush-time emission.
* `fence` is transcribed as the paper's `λ () L. {((), [], L;{δ})}`; since `{δ}` is the unit
  of the concatenation monoid, `L;{δ} = L`.
* The paper's healthiness condition `pflush ; f ; pflush = f` genuinely fails for `f = id`
  (L4893-4906); `pflush_ne_pure` proves it.
-/

universe u

namespace Isotope.Elgot.TSO

open Isotope.Pomset Isotope.Elgot

variable {Loc Val : Type u} {A B : Type u}

/-- The paper's `pflush_A = λ a L. {(a, R, α) | L = α;R}` (L4852-4855): nondeterministically
flush a prefix of the buffer into the emitted pomset. -/
def pflush (a : A) : TSO Loc Val A :=
  ⟨fun L => {e | ∃ α R, L = α ++ R ∧ e = ⟨a, R, Buf.toPom α⟩}⟩

theorem mem_pflush_iff (a : A) (L : Buf Loc Val) (e : Exec (Buf Loc Val) (Pom (Act Loc Val)) A) :
    e ∈ (pflush a).runs L ↔ ∃ α R, L = α ++ R ∧ e = ⟨a, R, Buf.toPom α⟩ := Iff.rfl

/-- **`pflush` is idempotent.**  The paper states this only implicitly, in the calculation of
L4913-4918 that makes `pflush_A` the identity of `PTSO`. -/
theorem pflush_kcomp_pflush :
    kcomp (pflush : A → TSO Loc Val A) pflush = pflush := by
  funext a
  ext L e
  rw [WS.mem_kcomp_iff]
  constructor
  · rintro ⟨r₁, ⟨α, R, rfl, rfl⟩, r₂, ⟨α', R', hR, rfl⟩, rfl⟩
    have hR' : R = α' ++ R' := hR
    subst hR'
    exact ⟨α ++ α', R', (List.append_assoc _ _ _).symm, by simp [Buf.toPom_append]⟩
  · rintro ⟨β, R, rfl, rfl⟩
    exact ⟨⟨a, R, Buf.toPom β⟩, ⟨β, R, rfl, rfl⟩, ⟨a, R, Buf.toPom []⟩,
      ⟨[], R, rfl, rfl⟩, by simp⟩

/-- **The paper's healthiness condition fails for the identity** (L4893-4906):
`pflush ; id ; pflush = pflush ; pflush = pflush ≠ id`.  Here `id` is `pure`. -/
theorem pflush_ne_pure (a : A) (x : Loc) (v : Val) :
    (pflush : A → TSO Loc Val A) ≠ pure := by
  intro h
  have hx := congrFun h a
  have hmem : (⟨a, [], Buf.toPom [(x, v)]⟩ : Exec (Buf Loc Val) (Pom (Act Loc Val)) A) ∈
      (pflush a).runs [(x, v)] := ⟨[(x, v)], [], by simp, rfl⟩
  rw [hx] at hmem
  have : ([] : Buf Loc Val) = [(x, v)] := congrArg Exec.state hmem
  exact absurd this (by simp)

/-- `pflush ; f ; pflush`, the shape of every TSO instruction denotation at L4845-4850. -/
def sandwich (f : A → TSO Loc Val B) : A → TSO Loc Val B :=
  kcomp pflush (kcomp f pflush)

/-- A flush before a sandwiched operation is absorbed. -/
theorem pflush_kcomp_sandwich (f : A → TSO Loc Val B) :
    kcomp pflush (sandwich f) = sandwich f := by
  rw [sandwich, ← kcomp_assoc, pflush_kcomp_pflush]

/-- A flush after a sandwiched operation is absorbed. -/
theorem sandwich_kcomp_pflush (f : A → TSO Loc Val B) :
    kcomp (sandwich f) pflush = sandwich f := by
  rw [sandwich, kcomp_assoc, kcomp_assoc, pflush_kcomp_pflush]

/-- The core of a write (L4848): append `b(x) := v` to the buffer and emit `x := v`. -/
def writeCore (x : Loc) (v : Val) : TSO Loc Val PUnit :=
  ⟨fun L => {⟨⟨⟩, L ++ [(x, v)], Pom.mk (PrePom.single (Act.write x v))⟩}⟩

/-- `⟦write_x⟧ = W_x^TSO = pflush ; writeCore ; pflush` (L4848). -/
def write (x : Loc) : Val → TSO Loc Val PUnit := sandwich (writeCore x)

@[simp] theorem pflush_kcomp_write (x : Loc) :
    kcomp pflush (write (Loc := Loc) (Val := Val) x) = write x := pflush_kcomp_sandwich _

@[simp] theorem write_kcomp_pflush (x : Loc) :
    kcomp (write (Loc := Loc) (Val := Val) x) pflush = write x := sandwich_kcomp_pflush _

section Ops

variable [DecidableEq Loc]

/-- The core of a read (L4845): read the latest buffered write to `x` if there is one, and
otherwise an *arbitrary* value; emit the read event `x = v`. -/
def readCore (x : Loc) (_ : PUnit) : TSO Loc Val Val :=
  ⟨fun L => {e | ∃ v, (Buf.peek x L = some v ∨ Buf.peek x L = none) ∧
    e = ⟨v, L, Pom.mk (PrePom.single (Act.read x v))⟩}⟩

/-- `⟦read_x⟧ = R_x^TSO = pflush ; readCore ; pflush` (L4845). -/
def read (x : Loc) : PUnit → TSO Loc Val Val := sandwich (readCore x)

@[simp] theorem pflush_kcomp_read (x : Loc) :
    kcomp pflush (read (Val := Val) x) = read x := pflush_kcomp_sandwich _

@[simp] theorem read_kcomp_pflush (x : Loc) :
    kcomp (read (Val := Val) x) pflush = read x := sandwich_kcomp_pflush _

end Ops

/-- `⟦fence⟧ = λ () L. {((), [], L;{δ})}` (L4860-4862): flush the whole buffer.  Since `{δ}`
is the unit of the concatenation monoid, the emitted pomset is exactly `L`. -/
def fence (_ : PUnit) : TSO Loc Val PUnit :=
  ⟨fun L => {⟨⟨⟩, [], Buf.toPom L⟩}⟩

theorem mem_fence_iff (L : Buf Loc Val)
    (e : Exec (Buf Loc Val) (Pom (Act Loc Val)) PUnit) :
    e ∈ (fence ⟨⟩ : TSO Loc Val PUnit).runs L ↔ e = ⟨⟨⟩, [], Buf.toPom L⟩ := Iff.rfl

/-- A fence already absorbs a preceding flush: unlike `read` and `write`, `fence` needs no
`pflush` sandwich. -/
theorem pflush_kcomp_fence :
    kcomp pflush (fence : PUnit → TSO Loc Val PUnit) = fence := by
  funext u
  ext L e
  rw [WS.mem_kcomp_iff]
  constructor
  · rintro ⟨r₁, ⟨α, R, rfl, rfl⟩, r₂, h₂, rfl⟩
    have h₂' : r₂ = ⟨⟨⟩, [], Buf.toPom R⟩ := h₂
    subst h₂'
    change (⟨⟨⟩, [], Buf.toPom α * Buf.toPom R⟩ :
      Exec (Buf Loc Val) (Pom (Act Loc Val)) PUnit) = ⟨⟨⟩, [], Buf.toPom (α ++ R)⟩
    rw [Buf.toPom_append]
  · intro h
    have h' : e = ⟨⟨⟩, [], Buf.toPom L⟩ := h
    subst h'
    exact ⟨⟨⟨⟩, L, Buf.toPom []⟩, ⟨[], L, rfl, rfl⟩, ⟨⟨⟩, [], Buf.toPom L⟩, rfl, by simp⟩

/-- A fence already absorbs a following flush. -/
theorem fence_kcomp_pflush :
    kcomp (fence : PUnit → TSO Loc Val PUnit) pflush = fence := by
  funext u
  ext L e
  rw [WS.mem_kcomp_iff]
  constructor
  · rintro ⟨r₁, h₁, r₂, ⟨α, R, hsplit, rfl⟩, rfl⟩
    have h₁' : r₁ = ⟨⟨⟩, [], Buf.toPom L⟩ := h₁
    subst h₁'
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hsplit.symm
    change (⟨⟨⟩, [], Buf.toPom L * Buf.toPom []⟩ :
      Exec (Buf Loc Val) (Pom (Act Loc Val)) PUnit) = ⟨⟨⟩, [], Buf.toPom L⟩
    rw [Buf.toPom_nil, mul_one]
  · intro h
    have h' : e = ⟨⟨⟩, [], Buf.toPom L⟩ := h
    subst h'
    exact ⟨⟨⟨⟩, [], Buf.toPom L⟩, rfl, ⟨⟨⟩, [], Buf.toPom []⟩, ⟨[], [], rfl, rfl⟩, by simp⟩

/-- **After a fence the buffer is always empty.** -/
theorem fence_state (L : Buf Loc Val) (e : Exec (Buf Loc Val) (Pom (Act Loc Val)) PUnit)
    (h : e ∈ (fence ⟨⟩ : TSO Loc Val PUnit).runs L) : e.state = [] := by
  have h' : e = ⟨⟨⟩, [], Buf.toPom L⟩ := h
  subst h'
  rfl

end Isotope.Elgot.TSO
