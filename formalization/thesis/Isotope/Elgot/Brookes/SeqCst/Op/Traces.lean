import Isotope.Elgot.Brookes.SeqCst.Op.Basic

/-!
# Transition traces of the small-step machine

Brookes's `T[C]` is defined operationally (journal §5): a *transition trace* of
`C` is a finite sequence of rely-guarantee pairs `⟨μ₁, ν₁⟩⋯⟨μₙ, νₙ⟩` obtained by
running `C` to completion in an environment that is allowed to change the store
arbitrarily between the machine's own steps, and `T[C]` is the closure of that
set under stuttering and mumbling.

`Run oC t oE` transcribes the "running with interference" relation, but at an
arbitrary residual `oC` and an arbitrary final residual `oE`, which is what the
`seq`, `while` and `par` clauses need — the segments of a transition trace of
`C₁ ; C₂` are read partly at a residual of `C₁` and partly at one of `C₂`.  A
transition trace of `C` proper is a `Run` from `some C` to `none`, and `opDen C`
is its closure.

Two features of the definition deserve comment.

* **Empty segments are allowed.**  `Relation.ReflTransGen.refl` is a legitimate
  segment, contributing a stutter pair `⟨μ, μ⟩`.  This is Brookes's definition;
  the closure absorbs such pairs anyway.
* **The empty trace is not a transition trace of anything.**  There is
  deliberately no rule making `[]` a transition trace of a terminated
  configuration: `Run oC [] oE` forces `oC = oE`, so `TTrace C []` is
  impossible.  Together with `SeqCst.refines_nil` this gives
  `nil_not_mem_opDen`, and hence — for instance — `opDen skip = test (fun _ ↦
  true)` rather than `pure ()`.  That is exactly the ε-freeness `den` was
  arranged to have, and it is what keeps full abstraction true.

The two lemmas the rest of `Op/` turns on are proved here.  `opObs_iff` is the
one-pair fragment: it identifies the observation `SeqCst.obs (opDen C)` extracted
denotationally from the trace set with operational termination `opObs C`.  This
is Brookes's `M[C] = {(s,s') | (s,s') ∈ T[C]}`, and its proof is `Run.stitch`,
which glues the segments of a run whose pairs form an interference-free `Chain`
into a single uninterrupted execution.  `run_peel` exposes the first *real*
small step of a transition trace, after a prefix of stutter-only segments; every
clause of Proposition 6.2 whose command starts by reducing (`ite`, `wh`, and via
`Atomic` also `skip`, `assign`, `await`) is proved by peeling.

Note that peeling is by "the segment took no step", never by "the segment's
endpoints agree": `while tt do skip` returns to its own configuration in an
unchanged store after doing real work.
-/

universe u

namespace Isotope.Elgot.Brookes.SeqCst.Op

open Isotope.Elgot Isotope.Elgot.Brookes

variable {Loc Val : Type u}

section

variable [DecidableEq Loc] [DecidableEq Val]

/-! ## Runs -/

/-- `Run oC t oE`: running the residual `oC` with interference produces the
sequence `t` of rely-guarantee pairs and leaves the residual `oE`.  Each pair
`⟨μ, ν⟩` of `t` records one *segment* of uninterrupted machine steps from `μ` to
`ν`; between segments the environment may change the store arbitrarily, which is
why nothing relates the guarantee `ν` of one pair to the rely of the next.

A segment may be empty, contributing a stutter pair.  A terminated residual
`none` admits only the empty run, so `[]` is never a transition trace. -/
inductive Run : Option (Com Loc Val) → Trace (Store Loc Val × Store Loc Val) →
    Option (Com Loc Val) → Prop
  | /-- Stop, contributing no pairs. -/ refl (oC) : Run oC [] oC
  | /-- One more segment of uninterrupted steps, at the front. -/
    cons {C μ oD ν t oE} : Relation.ReflTransGen CStep (some C, μ) (oD, ν) → Run oD t oE →
      Run (some C) ((μ, ν) :: t) oE

/-- **Brookes's transition traces** (journal §5): `t` is a transition trace of
`C` when running `C` with interference produces `t` and terminates. -/
def TTrace (C : Com Loc Val) (t : Trace (Store Loc Val × Store Loc Val)) : Prop :=
  Run (some C) t none

/-- **Brookes's `T[C]`, defined operationally**: the stutter/mumble closure of
the set of transition traces of `C`.  Proposition 6.2 — proved downstream as
`opDen_eq_den` — says this agrees with the transcribed denotational `den`. -/
def opDen (C : Com Loc Val) : Comp Loc Val PUnit := Brookes.close _ {p | TTrace C p.1}

/-- **Operational termination**: `C` run from `μ` without interference can
terminate in `ν`.  This is Brookes's `M[C]`, read off the machine. -/
def opObs (C : Com Loc Val) (μ ν : Store Loc Val) : Prop :=
  Relation.ReflTransGen CStep (some C, μ) ((none : Option (Com Loc Val)), ν)

/-! ## Basic properties of runs -/

/-- A run contributing no pairs does not change the residual. -/
theorem Run.nil_inv {oC oE : Option (Com Loc Val)} (h : Run oC [] oE) : oC = oE := by
  cases h; rfl

/-- A terminated residual admits only the empty run. -/
theorem Run.none_inv {t : Trace (Store Loc Val × Store Loc Val)} {oE}
    (h : Run (none : Option (Com Loc Val)) t oE) : t = [] ∧ oE = none := by
  cases h; exact ⟨rfl, rfl⟩

/-- Inversion for a run with at least one segment. -/
theorem Run.cons_inv {oC : Option (Com Loc Val)} {μ ν : Store Loc Val}
    {t : Trace (Store Loc Val × Store Loc Val)} {oE} (h : Run oC ((μ, ν) :: t) oE) :
    ∃ C oD, oC = some C ∧ Relation.ReflTransGen CStep (some C, μ) (oD, ν) ∧ Run oD t oE := by
  cases h with
  | cons hs hr => exact ⟨_, _, rfl, hs, hr⟩

/-- A single segment is a run. -/
theorem Run.single {C : Com Loc Val} {μ oD ν}
    (h : Relation.ReflTransGen CStep (some C, μ) (oD, ν)) : Run (some C) [(μ, ν)] oD :=
  Run.cons h (Run.refl oD)

/-- Runs compose, concatenating their traces. -/
theorem Run.append : ∀ {oC : Option (Com Loc Val)} {t oD}, Run oC t oD →
    ∀ {u oE}, Run oD u oE → Run oC (t ++ u) oE := by
  intro oC t oD h
  induction h with
  | refl oC => intro u oE h₂; exact h₂
  | cons hs _ ih => intro u oE h₂; exact Run.cons hs (ih h₂)

/-- A run splits wherever its trace splits. -/
theorem Run.split : ∀ {oC : Option (Com Loc Val)} {t u oE}, Run oC (t ++ u) oE →
    ∃ oD, Run oC t oD ∧ Run oD u oE := by
  intro oC t
  induction t generalizing oC with
  | nil => intro u oE h; exact ⟨oC, Run.refl oC, h⟩
  | cons p t ih =>
      intro u oE h
      obtain ⟨p₁, p₂⟩ := p
      simp only [List.cons_append] at h
      obtain ⟨C, oD, hC, hs, hr⟩ := h.cons_inv
      obtain ⟨oF, h₁, h₂⟩ := ih hr
      exact ⟨oF, hC ▸ Run.cons hs h₁, h₂⟩

/-- A run may be prefixed by an empty segment, contributing a stutter pair. -/
theorem Run.stutter {C : Com Loc Val} {μ : Store Loc Val} {t oE} (h : Run (some C) t oE) :
    Run (some C) ((μ, μ) :: t) oE :=
  Run.cons Relation.ReflTransGen.refl h

/-! ## Membership in `opDen` -/

/-- Membership in `opDen C` unfolds to a transition trace refining to the given
trace. -/
theorem mem_opDen_iff {C : Com Loc Val} {t : Trace (Store Loc Val × Store Loc Val)}
    {x : PUnit} : (t, x) ∈ opDen C ↔ ∃ t₀, TTrace C t₀ ∧ (rewriting (Store Loc Val)).Refines t₀ t :=
  Iff.rfl

/-- Every transition trace of `C` is a trace of `opDen C`. -/
theorem mem_opDen {C : Com Loc Val} {t : Trace (Store Loc Val × Store Loc Val)}
    (h : TTrace C t) (x : PUnit) : (t, x) ∈ opDen C :=
  ⟨t, h, Relation.ReflTransGen.refl⟩

/-- `opDen C` is the least computation containing every transition trace of `C`,
so an inequation out of it need only be checked on transition traces. -/
theorem opDen_le_iff {C : Com Loc Val} {y : Comp Loc Val PUnit} :
    opDen C ≤ y ↔ ∀ t, TTrace C t → (t, PUnit.unit) ∈ y := by
  constructor
  · intro h t ht; exact h (mem_opDen ht PUnit.unit)
  · intro h
    apply Brookes.le_of_mem
    rintro t ⟨⟩ ⟨t₀, ht₀, hr⟩
    exact Brookes.mem_of_refines (h t₀ ht₀) hr

/-! ## ε-freeness -/

/-- A transition trace is never empty: reaching a terminated residual from a
running one takes at least one segment. -/
theorem TTrace.ne_nil {C : Com Loc Val} {t : Trace (Store Loc Val × Store Loc Val)}
    (h : TTrace C t) : t ≠ [] := by
  intro ht; subst ht; cases h

/-- **`opDen` is ε-free.**  No rewrite produces the empty trace, and no
transition trace is empty, so the empty trace is in no command's denotation —
matching the ε-freeness of the transcribed `den`. -/
theorem nil_not_mem_opDen (C : Com Loc Val) (x : PUnit) :
    (([] : Trace (Store Loc Val × Store Loc Val)), x) ∉ opDen C := by
  rintro ⟨t₀, ht₀, hr⟩
  exact ht₀.ne_nil (SeqCst.refines_nil hr)

/-! ## Refinement plumbing -/

omit [DecidableEq Loc] [DecidableEq Val] in
/-- A prefix of stutter pairs may be added to any trace. -/
theorem refines_stutter_prefix {s : Trace (Store Loc Val × Store Loc Val)}
    (hs : ∀ p ∈ s, p.1 = p.2) (t : Trace (Store Loc Val × Store Loc Val)) :
    (rewriting (Store Loc Val)).Refines t (s ++ t) := by
  simpa using Rewriting.refines_appendRight (SeqCst.refines_nil_of_stutters hs) t

omit [DecidableEq Loc] [DecidableEq Val] in
/-- A stutter in front of a pair it relies on may be mumbled away. -/
theorem refines_mumble_head (μ ν : Store Loc Val) (t : Trace (Store Loc Val × Store Loc Val)) :
    (rewriting (Store Loc Val)).Refines ((μ, μ) :: (μ, ν) :: t) ((μ, ν) :: t) :=
  Relation.ReflTransGen.single (SeqCst.Step.mumble μ μ ν t)

/-! ## The one-pair fragment -/

/-- **Stitching.**  If the pairs of a run form an interference-free `Chain` from
`μ` to `ν` — each segment's guarantee being the next segment's rely, so the
environment in fact did nothing — then the whole run is one uninterrupted
execution from `μ` to `ν`.

The statement must be at arbitrary residuals `oC`, `oE`: at `some C` and `none`
the `Run` induction is blocked by non-variable indices. -/
theorem Run.stitch : ∀ {oC : Option (Com Loc Val)} {t oE}, Run oC t oE →
    ∀ {μ ν : Store Loc Val}, Chain μ t ν → Relation.ReflTransGen CStep (oC, μ) (oE, ν) := by
  intro oC t oE h
  induction h with
  | refl oC => intro μ ν hc; cases hc.nil_inv; exact Relation.ReflTransGen.refl
  | @cons C a oD b t oE hs _ ih =>
      intro μ ν hc
      obtain ⟨h₁, h₂⟩ := hc.cons_inv rfl
      cases h₁
      exact hs.trans (ih h₂)

/-- **Brookes's `M[C] = {(s,s') ∈ T[C]}`.**  The observation extracted from the
operational trace set is exactly operational termination.  This is the one-pair
fragment of Proposition 6.2, and the lemma the whole bridge turns on. -/
theorem opObs_iff {C : Com Loc Val} {μ ν : Store Loc Val} :
    SeqCst.obs (opDen C) μ ν ↔ opObs C μ ν := by
  constructor
  · rintro ⟨t₀, ht₀, hr⟩
    exact ht₀.stitch (chain_iff_refines_single.2 hr)
  · intro h
    exact ⟨[(μ, ν)], Run.cons h (Run.refl none), Relation.ReflTransGen.refl⟩

/-! ## Peeling -/

/-- Peeling, in the generalized form the `Run` induction demands: both `some C`
and `none` are non-variable indices, so they enter as equational premises. -/
theorem run_peel_gen : ∀ {oC : Option (Com Loc Val)} {t oF}, Run oC t oF →
    ∀ {C : Com Loc Val}, oC = some C → oF = none →
      ∃ (s : Trace (Store Loc Val × Store Loc Val)) (μ ν : Store Loc Val)
        (oD : Option (Com Loc Val)) (ρ : Store Loc Val) (oE : Option (Com Loc Val))
        (t' : Trace (Store Loc Val × Store Loc Val)),
        (∀ p ∈ s, p.1 = p.2) ∧ t = s ++ (μ, ν) :: t' ∧
        Red C μ oD ρ ∧ Relation.ReflTransGen CStep (oD, ρ) (oE, ν) ∧ Run oE t' none := by
  intro oC t oF h
  induction h with
  | refl oC => intro C h₁ h₂; cases h₁; exact absurd h₂ (by simp)
  | @cons D a oD b t oF hs hr ih =>
      intro C h₁ h₂
      cases h₁
      rcases Relation.ReflTransGen.cases_head hs with h₃ | ⟨z, hz₁, hz₂⟩
      · cases h₃
        obtain ⟨s, μ, ν, oD', ρ, oE, t', hst, ht, hred, hsteps, hrun⟩ := ih rfl h₂
        refine ⟨(a, a) :: s, μ, ν, oD', ρ, oE, t', ?_, ?_, hred, hsteps, hrun⟩
        · intro p hp
          rcases List.mem_cons.1 hp with rfl | hp
          · rfl
          · exact hst p hp
        · rw [ht]; rfl
      · obtain ⟨z₁, z₂⟩ := z
        exact ⟨[], a, b, z₁, z₂, oD, t, by simp, rfl, hz₁, hz₂, h₂ ▸ hr⟩

/-- **The peeling lemma.**  A transition trace of `C` begins with a run of
stutter-only segments, followed by a segment in which `C` takes its first real
small step `Red C μ oD ρ`; the rest of that segment runs `oD` on to `oE` at the
segment's guarantee `ν`, and the remaining pairs are a run of `oE` to
termination.

Peeling is by "the segment took no step", not by "the segment's endpoints
agree": `while tt do skip` returns to its own configuration in an unchanged
store after real work. -/
theorem run_peel {C : Com Loc Val} {t : Trace (Store Loc Val × Store Loc Val)}
    (h : TTrace C t) :
    ∃ (s : Trace (Store Loc Val × Store Loc Val)) (μ ν : Store Loc Val)
      (oD : Option (Com Loc Val)) (ρ : Store Loc Val) (oE : Option (Com Loc Val))
      (t' : Trace (Store Loc Val × Store Loc Val)),
      (∀ p ∈ s, p.1 = p.2) ∧ t = s ++ (μ, ν) :: t' ∧
      Red C μ oD ρ ∧ Relation.ReflTransGen CStep (oD, ρ) (oE, ν) ∧ Run oE t' none :=
  run_peel_gen h rfl rfl

end

end Isotope.Elgot.Brookes.SeqCst.Op
