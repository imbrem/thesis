import Isotope.Elgot.TSO.Ops

/-!
# Drainable computations

The paper's first candidate validity condition (`denotational-semantics-of-ssa.tex`
L4891-4897): a "valid" morphism must have, from every initial buffer, at least one execution
that completely flushes the buffer.  `Drainable` is that predicate.

Two negative facts are stated up front rather than discovered later, because they are what
forces `Drainable` to stay *outside* the carrier of the monad:

* `not_drainable_pure` — `pure` is not drainable at a nonempty buffer.  This is precisely the
  paper's `pflush ; id ; pflush = pflush ≠ id` at L4898-4906.
* `not_drainable_iter` — `Drainable` is not preserved by `iter`.  A body that always
  recurses is drainable while the loop it generates has no finite run at all.

Making `Drainable` a carrier field would therefore make `Iterate` unfillable.

## Honest boundary

`Drainable` is only the *first* of the paper's candidate validity conditions.  The stronger
`pflush ; f ; pflush = f` is not imposed (it fails for `pure`), and the TSO post-filter of
L4781-4788 — which is what would make an execution genuinely TSO-correct — is not formalised
anywhere in this development.
-/

universe u

namespace Isotope.Elgot.TSO

open Isotope.Pomset Isotope.Elgot

variable {Loc Val : Type u} {A B : Type u}

/-- A computation has at least one execution from every initial buffer. -/
def Total (x : TSO Loc Val A) : Prop := ∀ L, (x.runs L).Nonempty

/-- A computation has, from every initial buffer, at least one execution that completely
flushes the buffer (L4893-4897). -/
def Drainable (x : TSO Loc Val A) : Prop := ∀ L, ∃ r ∈ x.runs L, r.state = []

theorem Drainable.total {x : TSO Loc Val A} (h : Drainable x) : Total x :=
  fun L => let ⟨r, hr, _⟩ := h L; ⟨r, hr⟩

/-- Draining is closed under sequencing, provided the first computation has *some* execution
and the continuation drains. -/
theorem Total.bind_drainable {x : TSO Loc Val A} {f : A → TSO Loc Val B}
    (hx : Total x) (hf : ∀ a, Drainable (f a)) : Drainable (x >>= f) := by
  intro L
  obtain ⟨r₁, h₁⟩ := hx L
  obtain ⟨r₂, h₂, h₂'⟩ := hf r₁.value r₁.state
  exact ⟨⟨r₂.value, r₂.state, r₁.effect * r₂.effect⟩, ⟨r₁, h₁, r₂, h₂, rfl⟩, h₂'⟩

/-- Draining is closed under sequencing. -/
theorem Drainable.bind {x : TSO Loc Val A} {f : A → TSO Loc Val B}
    (hx : Drainable x) (hf : ∀ a, Drainable (f a)) : Drainable (x >>= f) :=
  hx.total.bind_drainable hf

theorem total_pflush (a : A) : Total (pflush (Loc := Loc) (Val := Val) a) :=
  fun L => ⟨⟨a, L, Buf.toPom []⟩, [], L, rfl, rfl⟩

/-- `pflush` drains: flushing the whole buffer is always one of its executions. -/
theorem drainable_pflush (a : A) : Drainable (pflush (Loc := Loc) (Val := Val) a) :=
  fun L => ⟨⟨a, [], Buf.toPom L⟩, ⟨L, [], by simp, rfl⟩, rfl⟩

/-- `fence` drains: it flushes the whole buffer in its only execution. -/
theorem drainable_fence : Drainable (fence (Loc := Loc) (Val := Val) ⟨⟩) :=
  fun L => ⟨⟨⟨⟩, [], Buf.toPom L⟩, rfl, rfl⟩

/-- Any `pflush`-sandwiched operation drains, as long as its core has some execution. -/
theorem drainable_sandwich {f : A → TSO Loc Val B} (hf : ∀ a, Total (f a)) (a : A) :
    Drainable (sandwich f a) :=
  (total_pflush a).bind_drainable
    (fun a' => (hf a').bind_drainable (fun b => drainable_pflush b))

theorem total_writeCore (x : Loc) (v : Val) : Total (writeCore x v) :=
  fun _ => ⟨_, rfl⟩

/-- Writes drain. -/
theorem drainable_write (x : Loc) (v : Val) :
    Drainable (write (Loc := Loc) (Val := Val) x v) :=
  drainable_sandwich (total_writeCore x) v

section Read

variable [DecidableEq Loc] [Nonempty Val]

theorem total_readCore (x : Loc) (u : PUnit) : Total (readCore (Val := Val) x u) := by
  intro L
  cases h : Buf.peek (Val := Val) x L with
  | none => exact ⟨_, Classical.arbitrary Val, Or.inr h, rfl⟩
  | some v => exact ⟨_, v, Or.inl h, rfl⟩

/-- Reads drain. -/
theorem drainable_read (x : Loc) :
    Drainable (read (Loc := Loc) (Val := Val) x ⟨⟩) :=
  drainable_sandwich (total_readCore x) ⟨⟩

end Read

/-- **`pure` does not drain.**  This is the paper's observation at L4898-4906 that
`pflush ; id ; pflush = pflush ≠ id`, stated as a property of `id = pure` itself. -/
theorem not_drainable_pure (a : A) (x : Loc) (v : Val) :
    ¬ Drainable (pure a : TSO Loc Val A) := by
  intro h
  obtain ⟨r, hr, hr'⟩ := h [(x, v)]
  have hr'' : r = ⟨a, [(x, v)], 1⟩ := hr
  rw [hr''] at hr'
  exact absurd hr' (by simp)

section Iter

/-- A loop body that flushes and then always recurses. -/
def loopBody (a : A) : TSO Loc Val (B ⊕ A) :=
  pflush a >>= fun a' => pure (Sum.inr a')

theorem loopBody_value {a : A} {L : Buf Loc Val}
    {e : Exec (Buf Loc Val) (Pom (Act Loc Val)) (B ⊕ A)}
    (h : e ∈ (loopBody (B := B) a).runs L) : ∃ a', e.value = Sum.inr a' := by
  obtain ⟨r₁, _, r₂, h₂, rfl⟩ := h
  have h₂' : r₂ = ⟨Sum.inr r₁.value, r₁.state, 1⟩ := h₂
  subst h₂'
  exact ⟨r₁.value, rfl⟩

/-- The always-recursing body drains: flush everything, then recurse. -/
theorem drainable_loopBody (a : A) :
    Drainable (loopBody (Loc := Loc) (Val := Val) (B := B) a) := fun L =>
  ⟨⟨Sum.inr a, [], Buf.toPom L * 1⟩,
    ⟨⟨a, [], Buf.toPom L⟩, ⟨L, [], by simp, rfl⟩, ⟨Sum.inr a, [], 1⟩, rfl, rfl⟩, rfl⟩

theorem not_runs_loopBody {a : A} {L : Buf Loc Val} {b : B} {s' : Buf Loc Val}
    {w : Pom (Act Loc Val)} :
    ¬ WS.Runs (loopBody (Loc := Loc) (Val := Val) (B := B)) L a b s' w := by
  intro h
  induction h with
  | done hs =>
      obtain ⟨a', ha⟩ := loopBody_value hs
      exact absurd ha (by simp)
  | more _ _ ih => exact ih

/-- **`Drainable` is not preserved by iteration.**  Every unfolding of `loopBody` drains, but
the loop itself has no finite run at all, so it drains from no buffer.  Together with
`not_drainable_pure` this is why `Drainable` must not be built into the monad's carrier. -/
theorem not_drainable_iter (a : A) :
    (∀ a' : A, Drainable (loopBody (Loc := Loc) (Val := Val) (B := B) a')) ∧
      ¬ Drainable (iter (loopBody (Loc := Loc) (Val := Val) (B := B)) a) := by
  refine ⟨drainable_loopBody, ?_⟩
  intro h
  obtain ⟨r, hr, _⟩ := h []
  exact not_runs_loopBody ((WS.mem_iter_iff _ _ _ _).1 hr)

end Iter

end Isotope.Elgot.TSO
