import Isotope.Elgot.Brookes.TSO.Monad

/-!
# Interleaving, parallel composition, and interference-free executions

Brookes traces are designed so that parallel composition is *trace interleaving*:
a step of the other thread appearing between two of my steps is exactly the
environment interference my rely-guarantee pairs already allow for.  This file
defines that interleaving and the parallel composition it induces, and the
predicate `Seq` picking out the complete, interference-free executions — the
runs in which every gap between successive steps is closed, i.e. the runs of a
closed system.

Parallel composition is *not* part of the monad, and no `λ_iter` model obligation
mentions it; it is here only because the store-buffering litmus test needs two
threads to be observable at all.

`Seq.of_refines` is the fact that makes reasoning about `par` possible in spite
of its closure operator: stuttering and mumbling can only ever *undo* into an
interference-free execution, never create one out of nothing.
-/

namespace Isotope.Elgot.Brookes

universe u v

variable {E : Type u} {c : Rewriting E} {A B : Type u}

/-- `Interleave t u w`: the trace `w` is a merge of `t` and `u` that preserves the
order of each.  Steps of `u` sit in the gaps of `t`, where a Brookes trace already
allows for environment interference, and vice versa. -/
inductive Interleave : Trace E → Trace E → Trace E → Prop
  | /-- Two finished threads interleave to nothing. -/
    nil : Interleave [] [] []
  | /-- The next global step is the left thread's. -/
    left {e : E} {t u w : Trace E} : Interleave t u w → Interleave (e :: t) u (e :: w)
  | /-- The next global step is the right thread's. -/
    right {e : E} {t u w : Trace E} : Interleave t u w → Interleave t (e :: u) (e :: w)

/-- Interleaving is symmetric. -/
theorem Interleave.swap {t u w : Trace E} (h : Interleave t u w) : Interleave u t w := by
  induction h with
  | nil => exact .nil
  | left _ ih => exact .right ih
  | right _ ih => exact .left ih

/-- A thread interleaved with an idle thread runs on its own. -/
theorem Interleave.nil_right (t : Trace E) : Interleave t [] t := by
  induction t with
  | nil => exact .nil
  | cons e t ih => exact .left ih

/-- A thread interleaved with an idle thread runs on its own. -/
theorem Interleave.nil_left (t : Trace E) : Interleave [] t t :=
  (Interleave.nil_right t).swap

/-- Parallel composition: run both computations, interleaving their traces, and
return both results.  The closure is genuine: mumbling can merge a step of one
thread with a step of the other, and the result is no longer an interleaving. -/
def par (x : Brookes c A) (y : Brookes c B) : Brookes c (A × B) :=
  close c {p | ∃ t u, (t, p.2.1) ∈ x ∧ (u, p.2.2) ∈ y ∧ Interleave t u p.1}

theorem mem_par {x : Brookes c A} {y : Brookes c B} {t u w : Trace E} {a : A} {b : B}
    (ha : (t, a) ∈ x) (hb : (u, b) ∈ y) (h : Interleave t u w) : (w, (a, b)) ∈ par x y :=
  ⟨w, ⟨t, u, ha, hb, h⟩, .refl⟩

theorem mem_par_iff {x : Brookes c A} {y : Brookes c B} {w : Trace E} {a : A} {b : B} :
    (w, (a, b)) ∈ par x y ↔
      ∃ w₀ t u, (t, a) ∈ x ∧ (u, b) ∈ y ∧ Interleave t u w₀ ∧ c.Refines w₀ w := by
  constructor
  · rintro ⟨w₀, ⟨t, u, ha, hb, hi⟩, hr⟩
    exact ⟨w₀, t, u, ha, hb, hi, hr⟩
  · rintro ⟨w₀, t, u, ha, hb, hi, hr⟩
    exact ⟨w₀, ⟨t, u, ha, hb, hi⟩, hr⟩

namespace TSO

variable {Tid Loc Val : Type u}

/-- `Seq s t s'`: the trace `t` is a complete execution from `s` to `s'` with no
environment interference — every gap between successive rely-guarantee pairs is
closed.  These are the runs of the closed system. -/
inductive Seq : St Tid Loc Val → Tr Tid Loc Val → St Tid Loc Val → Prop
  | /-- The empty execution. -/
    nil {s : St Tid Loc Val} : Seq s [] s
  | /-- One step, taken from the current state. -/
    cons {s s' : St Tid Loc Val} {t : Tr Tid Loc Val} {s'' : St Tid Loc Val} :
      Seq s' t s'' → Seq s ((s, s') :: t) s''

/-- Stuttering and mumbling reflect interference-free executions: if a rewrite of
`t` is interference-free, so was `t`, with the same endpoints. -/
theorem Seq.of_step {t t' : Tr Tid Loc Val} (h : SeqCst.Step (St Tid Loc Val) t t')
    {s s' : St Tid Loc Val} (hs : Seq s t' s') : Seq s t s' := by
  induction h generalizing s with
  | stutter μ t => cases hs with | cons h => exact h
  | mumble μ ρ θ t => cases hs with | cons h => exact .cons (.cons h)
  | cons p _ ih =>
    obtain ⟨q, q'⟩ := p
    cases hs with | cons h => exact .cons (ih h)

/-- Refinement reflects interference-free executions. -/
theorem Seq.of_refines {t t' : Tr Tid Loc Val}
    (h : (SeqCst.rewriting (St Tid Loc Val)).Refines t t')
    {s s' : St Tid Loc Val} (hs : Seq s t' s') : Seq s t s' := by
  induction h with
  | refl => exact hs
  | tail _ hstep ih => exact ih (Seq.of_step hstep hs)

/-- The final state of an interference-free execution is reached from the initial
one; in particular an empty execution changes nothing. -/
theorem Seq.nil_eq {s s' : St Tid Loc Val} (h : Seq s [] s') : s = s' := by
  cases h; rfl

end TSO

end Isotope.Elgot.Brookes
