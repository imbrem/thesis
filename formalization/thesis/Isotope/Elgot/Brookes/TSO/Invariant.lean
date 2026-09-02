import Isotope.Elgot.Brookes.TSO.Interleaving

/-!
# The write-then-read invariant

The store-buffering litmus test separates two memory models by an *ordering*
fact: under sequential consistency a thread's write to `ℓ` has reached global
memory before its subsequent read of `k` observes anything, whereas under TSO the
write may still be sitting in the thread's buffer.

This file isolates that fact as a predicate on traces:

* `OkStep ℓ v p` — the step `p` changes global memory only by writing `v` to `ℓ`.
  Note that it says **nothing** about write buffers: buffering a write and
  committing `ℓ := v` from the buffer are both `OkStep ℓ v`, which is exactly why
  the same invariant serves for both models.
* `Reads ℓ v k r t` — every step of `t` is `OkStep ℓ v`, and one of them observes
  `k = r`.
* `Wrote ℓ v k r t` — some step of `t` sets memory at `ℓ` to `v`, and the
  observation of `k = r` happens at or after it.

`Wrote` is closed under stuttering and mumbling (`Wrote.refines`), so it is a
property of the *closed* trace set of a computation, not merely of its
generators.  The litmus argument in `TSO/Litmus.lean` needs nothing else about
the two programs.
-/

namespace Isotope.Elgot.Brookes

universe u

namespace TSO

variable {Tid Loc Val : Type u} [DecidableEq Loc]

/-- A step whose only effect on global memory is, possibly, to write `v` at `ℓ`.
Write buffers are unconstrained: buffering a write and committing it are both
`OkStep`, and so is a plain stutter. -/
def OkStep (ℓ : Loc) (v : Val) (p : St Tid Loc Val × St Tid Loc Val) : Prop :=
  p.2.mem = p.1.mem ∨ p.2.mem = Function.update p.1.mem ℓ v

/-- A stutter is harmless. -/
theorem okStep_stutter (ℓ : Loc) (v : Val) (s : St Tid Loc Val) : OkStep ℓ v (s, s) :=
  Or.inl rfl

/-- An `OkStep` leaves every other location alone. -/
theorem OkStep.mem_ne {ℓ k : Loc} {v : Val} {p : St Tid Loc Val × St Tid Loc Val}
    (h : OkStep ℓ v p) (hk : k ≠ ℓ) : p.2.mem k = p.1.mem k := by
  rcases h with h | h <;> rw [h]
  exact Function.update_of_ne hk _ _

/-- Once memory holds `v` at `ℓ`, an `OkStep` keeps it there. -/
theorem OkStep.keeps {ℓ : Loc} {v : Val} {p : St Tid Loc Val × St Tid Loc Val}
    (h : OkStep ℓ v p) (h1 : p.1.mem ℓ = v) : p.2.mem ℓ = v := by
  rcases h with h | h <;> rw [h]
  · exact h1
  · exact Function.update_self _ _ _

/-- An `OkStep` that actually writes leaves `v` at `ℓ`. -/
theorem okStep_update_mem {ℓ : Loc} {v : Val} {s : St Tid Loc Val} {f : Loc → Val}
    (h : f = Function.update s.mem ℓ v) : f ℓ = v := by
  rw [h]; exact Function.update_self _ _ _

/-- Two composable `OkStep`s compose: this is what makes the invariant survive
mumbling. -/
theorem OkStep.trans {ℓ : Loc} {v : Val} {μ ρ θ : St Tid Loc Val}
    (h₁ : OkStep ℓ v (μ, ρ)) (h₂ : OkStep ℓ v (ρ, θ)) : OkStep ℓ v (μ, θ) := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;>
    simp only [] at h₁ h₂ ⊢
  · exact Or.inl (h₂.trans h₁)
  · exact Or.inr (by rw [h₂, h₁])
  · exact Or.inr (by rw [h₂, h₁])
  · exact Or.inr (by rw [h₂, h₁, Function.update_idem])

/-- Every step of the trace is an `OkStep`. -/
def OkAll (ℓ : Loc) (v : Val) (t : Tr Tid Loc Val) : Prop := ∀ p ∈ t, OkStep ℓ v p

@[simp] theorem okAll_nil (ℓ : Loc) (v : Val) : OkAll ℓ v ([] : Tr Tid Loc Val) := by
  intro p hp; exact absurd hp List.not_mem_nil

theorem OkAll.head {ℓ : Loc} {v : Val} {p : St Tid Loc Val × St Tid Loc Val}
    {t : Tr Tid Loc Val} (h : OkAll ℓ v (p :: t)) : OkStep ℓ v p := h p (by simp)

theorem OkAll.tail {ℓ : Loc} {v : Val} {p : St Tid Loc Val × St Tid Loc Val}
    {t : Tr Tid Loc Val} (h : OkAll ℓ v (p :: t)) : OkAll ℓ v t :=
  fun q hq ↦ h q (by simp [hq])

theorem OkAll.cons {ℓ : Loc} {v : Val} {p : St Tid Loc Val × St Tid Loc Val}
    {t : Tr Tid Loc Val} (hp : OkStep ℓ v p) (ht : OkAll ℓ v t) : OkAll ℓ v (p :: t) := by
  intro q hq
  rcases List.mem_cons.1 hq with rfl | hq
  · exact hp
  · exact ht q hq

/-- `OkAll` survives one stuttering or mumbling rewrite. -/
theorem okAll_step {ℓ : Loc} {v : Val} {t t' : Tr Tid Loc Val}
    (h : SeqCst.Step (St Tid Loc Val) t t') : OkAll ℓ v t → OkAll ℓ v t' := by
  induction h with
  | stutter μ t => exact fun ht ↦ OkAll.cons (okStep_stutter ℓ v μ) ht
  | mumble μ ρ θ t =>
    exact fun ht ↦ OkAll.cons (OkStep.trans ht.head ht.tail.head) ht.tail.tail
  | cons q _ ih => exact fun ht ↦ OkAll.cons ht.head (ih ht.tail)

/-- `OkAll` survives refinement. -/
theorem OkAll.refines {ℓ : Loc} {v : Val} {t t' : Tr Tid Loc Val}
    (h : (SeqCst.rewriting (St Tid Loc Val)).Refines t t') (ht : OkAll ℓ v t) :
    OkAll ℓ v t' := by
  induction h with
  | refl => exact ht
  | tail _ hstep ih => exact okAll_step hstep ih

/-- `Reads ℓ v k r t`: every step of `t` writes at most `ℓ := v`, and some step
observes the value `r` at `k`. -/
inductive Reads (ℓ : Loc) (v : Val) (k : Loc) (r : Val) : Tr Tid Loc Val → Prop
  | /-- The observation happens now. -/
    here {p : St Tid Loc Val × St Tid Loc Val} {t : Tr Tid Loc Val} :
      OkStep ℓ v p → p.2.mem k = r → OkAll ℓ v t → Reads ℓ v k r (p :: t)
  | /-- The observation happens later. -/
    there {p : St Tid Loc Val × St Tid Loc Val} {t : Tr Tid Loc Val} :
      OkStep ℓ v p → Reads ℓ v k r t → Reads ℓ v k r (p :: t)

theorem Reads.okAll {ℓ : Loc} {v : Val} {k : Loc} {r : Val} {t : Tr Tid Loc Val}
    (h : Reads ℓ v k r t) : OkAll ℓ v t := by
  induction h with
  | here hp _ ht => exact OkAll.cons hp ht
  | there hp _ ih => exact OkAll.cons hp ih

/-- `Reads` survives one stuttering or mumbling rewrite, provided the location
being read is not the location being written. -/
theorem reads_step {ℓ : Loc} {v : Val} {k : Loc} {r : Val} (hk : k ≠ ℓ)
    {t t' : Tr Tid Loc Val} (h : SeqCst.Step (St Tid Loc Val) t t') :
    Reads ℓ v k r t → Reads ℓ v k r t' := by
  induction h with
  | stutter μ t => exact fun ht ↦ .there (okStep_stutter ℓ v μ) ht
  | mumble μ ρ θ t =>
    intro ht
    cases ht with
    | here hp hr hall =>
      exact .here (hp.trans hall.head) ((hall.head.mem_ne hk).trans hr) hall.tail
    | there hp ht' =>
      cases ht' with
      | here hq hr hall => exact .here (hp.trans hq) hr hall
      | there hq ht'' => exact .there (hp.trans hq) ht''
  | cons q hstep ih =>
    intro ht
    cases ht with
    | here hp hr hall => exact .here hp hr (okAll_step hstep hall)
    | there hp ht' => exact .there hp (ih ht')

/-- `Reads` survives refinement. -/
theorem Reads.refines {ℓ : Loc} {v : Val} {k : Loc} {r : Val} (hk : k ≠ ℓ)
    {t t' : Tr Tid Loc Val} (h : (SeqCst.rewriting (St Tid Loc Val)).Refines t t')
    (ht : Reads ℓ v k r t) : Reads ℓ v k r t' := by
  induction h with
  | refl => exact ht
  | tail _ hstep ih => exact reads_step hk hstep ih

/-- `Wrote ℓ v k r t`: some step of `t` leaves `v` in memory at `ℓ`, and the
observation of `r` at `k` happens at or after that step. -/
inductive Wrote (ℓ : Loc) (v : Val) (k : Loc) (r : Val) : Tr Tid Loc Val → Prop
  | /-- The write lands now, and the read follows. -/
    write {p : St Tid Loc Val × St Tid Loc Val} {t : Tr Tid Loc Val} :
      OkStep ℓ v p → p.2.mem ℓ = v → Reads ℓ v k r (p :: t) → Wrote ℓ v k r (p :: t)
  | /-- The write has not landed yet. -/
    skip {p : St Tid Loc Val × St Tid Loc Val} {t : Tr Tid Loc Val} :
      OkStep ℓ v p → Wrote ℓ v k r t → Wrote ℓ v k r (p :: t)

theorem Wrote.okAll {ℓ : Loc} {v : Val} {k : Loc} {r : Val} {t : Tr Tid Loc Val}
    (h : Wrote ℓ v k r t) : OkAll ℓ v t := by
  induction h with
  | write _ _ hr => exact hr.okAll
  | skip hp _ ih => exact OkAll.cons hp ih

/-- `Wrote` survives one stuttering or mumbling rewrite. -/
theorem wrote_step {ℓ : Loc} {v : Val} {k : Loc} {r : Val} (hk : k ≠ ℓ)
    {t t' : Tr Tid Loc Val} (h : SeqCst.Step (St Tid Loc Val) t t') :
    Wrote ℓ v k r t → Wrote ℓ v k r t' := by
  induction h with
  | stutter μ t => exact fun ht ↦ .skip (okStep_stutter ℓ v μ) ht
  | mumble μ ρ θ t =>
    intro ht
    cases ht with
    | write hp hset hreads =>
      have hq : OkStep ℓ v ((ρ, θ) : St Tid Loc Val × St Tid Loc Val) :=
        hreads.okAll.tail.head
      exact .write (hp.trans hq) (hq.keeps hset)
        (reads_step hk (SeqCst.Step.mumble μ ρ θ t) hreads)
    | skip hp ht' =>
      cases ht' with
      | write hq hset hreads =>
        refine .write (hp.trans hq) hset ?_
        cases hreads with
        | here _ hr hall => exact .here (hp.trans hq) hr hall
        | there _ hrest => exact .there (hp.trans hq) hrest
      | skip hq ht'' => exact .skip (hp.trans hq) ht''
  | cons q hstep ih =>
    intro ht
    cases ht with
    | write hp hset hreads =>
      exact .write hp hset (reads_step hk (SeqCst.Step.cons q hstep) hreads)
    | skip hp ht' => exact .skip hp (ih ht')

/-- `Wrote` survives refinement, so it is a property of the closed trace set of a
computation and not merely of its generators. -/
theorem Wrote.refines {ℓ : Loc} {v : Val} {k : Loc} {r : Val} (hk : k ≠ ℓ)
    {t t' : Tr Tid Loc Val} (h : (SeqCst.rewriting (St Tid Loc Val)).Refines t t')
    (ht : Wrote ℓ v k r t) : Wrote ℓ v k r t' := by
  induction h with
  | refl => exact ht
  | tail _ hstep ih => exact wrote_step hk hstep ih

end TSO

end Isotope.Elgot.Brookes
