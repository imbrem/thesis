import Isotope.Elgot.Brookes.SeqCst.Op.Traces
import Isotope.Elgot.Brookes.SeqCst.Laws

/-!
# Proposition 6.2: the parallel composition clause

This file proves

```
T[C₁ ∥ C₂] = T[C₁] ∥ T[C₂]
```

i.e. `opDen (Com.par C₁ C₂) = parU (opDen C₁) (opDen C₂)`, where `parU` is
Brookes's shuffle-then-close parallel composition on trace sets.

Everything turns on `joinCfg`, which describes the configurations reachable from
`C₁ ∥ C₂`: they are `D₁ ∥ D₂` while both threads run, `D₂` once the left thread
has finished, `D₁` once the right one has, and `none` once both have.  Reading
`joinCfg` as a map on *pairs of residuals* folds the four congruence rules
`Red.parL`, `Red.parL'`, `Red.parR`, `Red.parR'` into the two statements
`cstep_join_left` / `cstep_join_right`, and folds the four cases of the
decomposition into the single `step_join_inv`.

## Thread projection

The `⊆` direction is the only place in `Op/` where two inductions meet the
shuffle relation `Interleave`, and it is done in two stages.

* `steps_join_inv` projects **one segment**.  It is a tail induction on
  `Relation.ReflTransGen CStep`, whose source configuration stays `joinCfg oD₁
  oD₂` throughout; the invariant maintained is that the segment so far has been
  split into a run `r₁` of the left thread, a run `r₂` of the right one, and a
  shuffle `w` of the two which is an interference-free `Chain` from the
  segment's rely to the current store.  Each small step is attributed to one
  thread by `step_join_inv` and appended to that thread's run, to the shuffle,
  and to the chain.

  Note that **every small step contributes its own pair** to its own thread's
  trace.  Building maximal uninterrupted stretches per thread instead does not
  work: extending a thread's trace would have to *modify its last pair* whenever
  the previous step was that same thread's.

* `run_join_inv` projects **across segments**, by induction on the run.  Per
  segment, `steps_join_inv` returns a shuffle `w₀` which is a chain from the
  segment's rely `μ` to its guarantee `ν`, and `Chain.refines_single` mumbles
  that whole shuffle back down to the single pair `⟨μ, ν⟩`.  The per-segment
  refinements are then glued by `Rewriting.refines_append`.

This is where the closure earns its keep for `∥`: within one segment both
threads may have stepped, so the two threads' pairs must be mumbled back
together, and the clause is therefore an identity of *closed* trace sets.

## The other direction

`⊇` is `run_of_interleave` — every shuffle of a transition trace of `C₁` with
one of `C₂` is a transition trace of `C₁ ∥ C₂`, with no closure step needed —
composed with `SeqCst.defersPar`, which is what lets the *closed* members
supplied by `mem_parU_iff` be replaced by the raw transition traces
`run_of_interleave` consumes.
-/

universe u

namespace Isotope.Elgot.Brookes.SeqCst.Op

open Isotope.Elgot Isotope.Elgot.Brookes

variable {Loc Val : Type u}

/-! ## Parallel residuals -/

/-- The residual of `C₁ ∥ C₂` determined by residuals of the two threads: both
running gives `D₁ ∥ D₂`, a terminated thread disappears, and two terminated
threads give a terminated command.  Every configuration reachable from `C₁ ∥ C₂`
has this form. -/
def joinCfg : Option (Com Loc Val) → Option (Com Loc Val) → Option (Com Loc Val)
  | none, oD₂ => oD₂
  | some D₁, none => some D₁
  | some D₁, some D₂ => some (Com.par D₁ D₂)

/-- A terminated left thread leaves the right thread's residual. -/
@[simp] theorem joinCfg_none_left (oD₂ : Option (Com Loc Val)) :
    joinCfg none oD₂ = oD₂ := rfl

/-- A terminated right thread leaves the left thread's residual. -/
@[simp] theorem joinCfg_none_right (oD₁ : Option (Com Loc Val)) :
    joinCfg oD₁ none = oD₁ := by cases oD₁ <;> rfl

/-- A parallel composition has terminated exactly when both its threads have. -/
@[simp] theorem joinCfg_eq_none {oD₁ oD₂ : Option (Com Loc Val)} :
    joinCfg oD₁ oD₂ = none ↔ oD₁ = none ∧ oD₂ = none := by
  cases oD₁ <;> cases oD₂ <;> simp [joinCfg]

section

variable [DecidableEq Loc] [DecidableEq Val]

/-! ## Congruence -/

/-- **Left congruence, one step.**  A step of the left thread is a step of the
parallel composition, whichever of `Red.parL` / `Red.parL'` applies and whether
or not the right thread is still running. -/
theorem cstep_join_left {D : Com Loc Val} {μ : Store Loc Val}
    {oE : Option (Com Loc Val)} {ν : Store Loc Val} (h : Red D μ oE ν)
    (oD₂ : Option (Com Loc Val)) :
    CStep (joinCfg (some D) oD₂, μ) (joinCfg oE oD₂, ν) := by
  cases oD₂ with
  | none => cases oE <;> exact h
  | some D₂ =>
      cases oE with
      | none => exact Red.parL' h
      | some D' => exact Red.parL h

/-- **Right congruence, one step.** -/
theorem cstep_join_right {D : Com Loc Val} {μ : Store Loc Val}
    {oE : Option (Com Loc Val)} {ν : Store Loc Val} (h : Red D μ oE ν)
    (oD₁ : Option (Com Loc Val)) :
    CStep (joinCfg oD₁ (some D), μ) (joinCfg oD₁ oE, ν) := by
  cases oD₁ with
  | none => cases oE <;> exact h
  | some D₁ =>
      cases oE with
      | none => exact Red.parR' h
      | some D' => exact Red.parR h

/-- **Left congruence.**  An execution of the left thread lifts to one of the
parallel composition, the right thread standing still.  Stated over a variable
target `y` with `y.1`/`y.2` projections, as a `Relation.ReflTransGen` induction
demands. -/
theorem steps_join_congL {C₁ : Com Loc Val} {μ : Store Loc Val} {y : Config Loc Val}
    (h : Relation.ReflTransGen CStep (some C₁, μ) y) (oD₂ : Option (Com Loc Val)) :
    Relation.ReflTransGen CStep (joinCfg (some C₁) oD₂, μ) (joinCfg y.1 oD₂, y.2) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hxy hyz ih =>
      obtain ⟨b₁, b₂⟩ := b
      obtain ⟨c₁, c₂⟩ := c
      cases b₁ with
      | none => exact absurd hyz id
      | some D =>
          have hred : Red D b₂ c₁ c₂ := hyz
          exact ih.tail (cstep_join_left hred oD₂)

/-- **Right congruence.** -/
theorem steps_join_congR {C₂ : Com Loc Val} {μ : Store Loc Val} {y : Config Loc Val}
    (h : Relation.ReflTransGen CStep (some C₂, μ) y) (oD₁ : Option (Com Loc Val)) :
    Relation.ReflTransGen CStep (joinCfg oD₁ (some C₂), μ) (joinCfg oD₁ y.1, y.2) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hxy hyz ih =>
      obtain ⟨b₁, b₂⟩ := b
      obtain ⟨c₁, c₂⟩ := c
      cases b₁ with
      | none => exact absurd hyz id
      | some D =>
          have hred : Red D b₂ c₁ c₂ := hyz
          exact ih.tail (cstep_join_right hred oD₁)

/-! ## Decomposition of executions -/

/-- **Attribution of a single step.**  A step of a parallel residual is a step
of exactly one of its two threads, the other thread's residual being unchanged. -/
theorem step_join_inv {oD₁ oD₂ : Option (Com Loc Val)} {C : Com Loc Val}
    {μ : Store Loc Val} {oE : Option (Com Loc Val)} {ν : Store Loc Val}
    (hj : joinCfg oD₁ oD₂ = some C) (hs : Red C μ oE ν) :
      (∃ D₁ oF₁, oD₁ = some D₁ ∧ Red D₁ μ oF₁ ν ∧ oE = joinCfg oF₁ oD₂)
    ∨ (∃ D₂ oF₂, oD₂ = some D₂ ∧ Red D₂ μ oF₂ ν ∧ oE = joinCfg oD₁ oF₂) := by
  cases oD₁ with
  | none =>
      cases oD₂ with
      | none => exact absurd hj (by simp)
      | some D₂ =>
          simp only [joinCfg_none_left, Option.some.injEq] at hj
          subst hj
          exact Or.inr ⟨D₂, oE, rfl, hs, rfl⟩
  | some D₁ =>
      cases oD₂ with
      | none =>
          simp only [joinCfg_none_right, Option.some.injEq] at hj
          subst hj
          exact Or.inl ⟨D₁, oE, rfl, hs, (joinCfg_none_right oE).symm⟩
      | some D₂ =>
          simp only [joinCfg, Option.some.injEq] at hj
          subst hj
          cases hs with
          | @parL _ _ D₁' _ _ h => exact Or.inl ⟨D₁, some D₁', rfl, h, rfl⟩
          | @parL' _ _ _ _ h => exact Or.inl ⟨D₁, none, rfl, h, rfl⟩
          | @parR _ _ D₂' _ _ h => exact Or.inr ⟨D₂, some D₂', rfl, h, rfl⟩
          | @parR' _ _ _ _ h => exact Or.inr ⟨D₂, none, rfl, h, rfl⟩

/-- **Thread projection, one segment.**  An uninterrupted execution of a
parallel residual splits into a run of each thread, whose shuffle is an
interference-free execution from the initial store to the final one.

Every small step contributes its own pair to its own thread's run; the shuffle
`w` is all those pairs in execution order.  The lemma is a tail induction on the
execution, which is what keeps the *source* configuration fixed at
`joinCfg oD₁ oD₂` — the shape the invariant needs. -/
theorem steps_join_inv {oD₁ oD₂ : Option (Com Loc Val)} {μ : Store Loc Val}
    {z : Config Loc Val} (h : Relation.ReflTransGen CStep (joinCfg oD₁ oD₂, μ) z) :
    ∃ r₁ r₂ w oF₁ oF₂, Run oD₁ r₁ oF₁ ∧ Run oD₂ r₂ oF₂ ∧
      Interleave r₁ r₂ w ∧ Chain μ w z.2 ∧ z.1 = joinCfg oF₁ oF₂ := by
  induction h with
  | refl =>
      exact ⟨[], [], [], oD₁, oD₂, Run.refl _, Run.refl _, Interleave.nil, Chain.nil μ, rfl⟩
  | @tail b c hxy hyz ih =>
      obtain ⟨b₁, b₂⟩ := b
      obtain ⟨c₁, c₂⟩ := c
      obtain ⟨r₁, r₂, w, oF₁, oF₂, h₁, h₂, hi, hc, hb⟩ := ih
      have hc' : Chain μ w b₂ := hc
      cases b₁ with
      | none => exact absurd hyz id
      | some C =>
          have hred : Red C b₂ c₁ c₂ := hyz
          have hb' : joinCfg oF₁ oF₂ = some C := hb.symm
          rcases step_join_inv hb' hred with ⟨D₁, oG₁, hF₁, hstep, hce⟩ |
            ⟨D₂, oG₂, hF₂, hstep, hce⟩
          · subst hF₁
            refine ⟨r₁ ++ [(b₂, c₂)], r₂, w ++ [(b₂, c₂)], oG₁, oF₂,
              h₁.append (Run.single (steps_single hstep)), h₂, ?_,
              hc'.append (Chain.cons b₂ c₂ (Chain.nil c₂)), hce⟩
            simpa using hi.appendCompat (Interleave.nil_right [(b₂, c₂)])
          · subst hF₂
            refine ⟨r₁, r₂ ++ [(b₂, c₂)], w ++ [(b₂, c₂)], oF₁, oG₂, h₁,
              h₂.append (Run.single (steps_single hstep)), ?_,
              hc'.append (Chain.cons b₂ c₂ (Chain.nil c₂)), hce⟩
            simpa using hi.appendCompat (Interleave.nil_left [(b₂, c₂)])

/-! ## Decomposition of transition traces -/

/-- **Thread projection, across segments.**  Every run of a parallel residual
projects to a run of each thread, whose shuffle refines the original trace.

The refinement is genuinely needed: within one segment `⟨μ, ν⟩` both threads may
have stepped, so many pairs of the shuffle correspond to that one pair, and are
recovered from it by mumbling — `Chain.refines_single` performs exactly that
collapse, one segment at a time. -/
theorem run_join_inv : ∀ {oC : Option (Com Loc Val)}
    {t : Trace (Store Loc Val × Store Loc Val)} {oE}, Run oC t oE →
    ∀ {oD₁ oD₂ : Option (Com Loc Val)}, oC = joinCfg oD₁ oD₂ →
      ∃ t₁ t₂ w oE₁ oE₂, Run oD₁ t₁ oE₁ ∧ Run oD₂ t₂ oE₂ ∧ Interleave t₁ t₂ w ∧
        (rewriting (Store Loc Val)).Refines w t ∧ oE = joinCfg oE₁ oE₂ := by
  intro oC t oE h
  induction h with
  | refl oC =>
      intro oD₁ oD₂ hj
      exact ⟨[], [], [], oD₁, oD₂, Run.refl _, Run.refl _, Interleave.nil,
        Relation.ReflTransGen.refl, hj⟩
  | @cons C a oD b t' oF hs hr ih =>
      intro oD₁ oD₂ hj
      rw [hj] at hs
      obtain ⟨r₁, r₂, w₀, oF₁, oF₂, k₁, k₂, hi, hch, hz⟩ := steps_join_inv hs
      obtain ⟨t₁, t₂, w', oE₁, oE₂, m₁, m₂, hi', href, hend⟩ :=
        ih (oD₁ := oF₁) (oD₂ := oF₂) hz
      exact ⟨r₁ ++ t₁, r₂ ++ t₂, w₀ ++ w', oE₁, oE₂, k₁.append m₁, k₂.append m₂,
        hi.appendCompat hi', Rewriting.refines_append hch.refines_single href, hend⟩

/-! ## Composition of transition traces -/

/-- **Interleaving.**  Every shuffle of a run of `oD₁` to termination with a run
of `oD₂` to termination is a run of the parallel residual `joinCfg oD₁ oD₂` to
termination — no closure step is needed in this direction. -/
theorem run_of_interleave : ∀ {t₁ t₂ w : Trace (Store Loc Val × Store Loc Val)},
    Interleave t₁ t₂ w → ∀ {oD₁ oD₂ : Option (Com Loc Val)}, Run oD₁ t₁ none →
      Run oD₂ t₂ none → Run (joinCfg oD₁ oD₂) w none := by
  intro t₁ t₂ w hi
  induction hi with
  | nil =>
      intro oD₁ oD₂ h₁ h₂
      obtain rfl := (Run.nil_inv h₁).symm
      obtain rfl := (Run.nil_inv h₂).symm
      exact Run.refl none
  | @left e t₁ t₂ w _ ih =>
      intro oD₁ oD₂ h₁ h₂
      obtain ⟨μ, ν⟩ := e
      obtain ⟨C, oD, rfl, hs, hr⟩ := h₁.cons_inv
      cases oD₂ with
      | none => exact Run.cons (steps_join_congL hs none) (ih hr h₂)
      | some D₂ => exact Run.cons (steps_join_congL hs (some D₂)) (ih hr h₂)
  | @right e t₁ t₂ w _ ih =>
      intro oD₁ oD₂ h₁ h₂
      obtain ⟨μ, ν⟩ := e
      obtain ⟨C, oD, rfl, hs, hr⟩ := h₂.cons_inv
      cases oD₁ with
      | none => exact Run.cons (steps_join_congR hs none) (ih h₁ hr)
      | some D₁ => exact Run.cons (steps_join_congR hs (some D₁)) (ih h₁ hr)

/-- **Composition of transition traces.**  Every shuffle of a transition trace
of `C₁` with one of `C₂` is a transition trace of `C₁ ∥ C₂`. -/
theorem ttrace_par {C₁ C₂ : Com Loc Val} {t₁ t₂ w : Trace (Store Loc Val × Store Loc Val)}
    (h₁ : TTrace C₁ t₁) (h₂ : TTrace C₂ t₂) (hi : Interleave t₁ t₂ w) :
    TTrace (Com.par C₁ C₂) w :=
  run_of_interleave hi h₁ h₂

/-- **Decomposition of transition traces.**  Every transition trace of `C₁ ∥ C₂`
is refined from a shuffle of a transition trace of `C₁` with one of `C₂`. -/
theorem ttrace_par_inv {C₁ C₂ : Com Loc Val} {t : Trace (Store Loc Val × Store Loc Val)}
    (h : TTrace (Com.par C₁ C₂) t) :
    ∃ t₁ t₂ w, TTrace C₁ t₁ ∧ TTrace C₂ t₂ ∧ Interleave t₁ t₂ w ∧
      (rewriting (Store Loc Val)).Refines w t := by
  obtain ⟨t₁, t₂, w, oE₁, oE₂, h₁, h₂, hi, href, hend⟩ :=
    run_join_inv h (oD₁ := some C₁) (oD₂ := some C₂) rfl
  obtain ⟨rfl, rfl⟩ := joinCfg_eq_none.1 hend.symm
  exact ⟨t₁, t₂, w, h₁, h₂, hi, href⟩

/-! ## The clause -/

/-- **Brookes, Proposition 6.2, parallel composition:** `T[C₁ ∥ C₂] = T[C₁] ∥ T[C₂]`.

`⊇` is `run_of_interleave`, which needs no closure but does need
`SeqCst.defersPar` to strip the closure off the two operands' members; `⊆` is
`ttrace_par_inv`, whose per-segment mumbling is absorbed by the closure in the
codomain. -/
theorem opDen_par (C₁ C₂ : Com Loc Val) :
    opDen (Com.par C₁ C₂) = SeqCst.parU (opDen C₁) (opDen C₂) := by
  apply le_antisymm
  · refine opDen_le_iff.2 fun t ht ↦ ?_
    obtain ⟨t₁, t₂, w, h₁, h₂, hi, href⟩ := ttrace_par_inv ht
    exact Brookes.mem_of_refines
      (SeqCst.mem_parU (mem_opDen h₁ PUnit.unit) (mem_opDen h₂ PUnit.unit) hi) href
  · refine Brookes.le_of_mem fun t x hmem ↦ ?_
    obtain ⟨w₀, u, v, hu, hv, hi, hr⟩ := SeqCst.mem_parU_iff.1 hmem
    obtain ⟨u₀, hu₀, hru⟩ := hu
    obtain ⟨v₀, hv₀, hrv⟩ := hv
    obtain ⟨w₁, hi₁, hr₁⟩ := SeqCst.defersPar.refines hru hi
    obtain ⟨w₂, hi₂, hr₂⟩ := SeqCst.defersPar.refines_right hrv hi₁
    exact Brookes.mem_of_refines (mem_opDen (ttrace_par hu₀ hv₀ hi₂) x)
      (hr₂.trans (hr₁.trans hr))

end

end Isotope.Elgot.Brookes.SeqCst.Op
