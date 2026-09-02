import Isotope.Elgot.Brookes.SeqCst.Op.Traces

/-!
# Proposition 6.2: the atomic clauses and the conditional

This file proves the clauses of Brookes's Proposition 6.2 (journal p. 150) whose
commands take exactly one small step of their own before handing control on:

```
T[skip]                 = {(s,s) | s ∈ S}†
T[I:=E]                 = {(s,[s | I = n]) | (s,n) ∈ E[E]}†
T[await B then C]       = {(s,s') ∈ T[C] | (s,tt) ∈ B[B]}†
T[if B then C₁ else C₂] = T[B];T[C₁] ∪ T[¬B];T[C₂]
```

The first three share a single argument, packaged as `Atomic`: a command all of
whose reductions terminate immediately.  For such a command a run with
interference degenerates — every segment before the last takes no step at all,
so it contributes a stutter pair, and the last segment is one whole terminating
execution.  `Atomic.run_inv` extracts that normal form and `opDen_of_atomic`
turns it into `opDen C = atom (opObs C)`, after which each clause is a one-line
computation of `opObs`.  The conditional is the same argument with the peeling
lemma `run_peel` in place of `Atomic.run_inv`, the residual after the first step
being `C₁` or `C₂` rather than `none`.

## `await` widens the language

Brookes restricts `await` bodies syntactically to finite sequences of
assignments, precisely so that his transition system can justify executing one
atomically.  Our `Red.await` rule instead *stipulates* atomicity for an
arbitrary body — including bodies containing `par` and nested `await`, which his
machine cannot run atomically at all.  So `opDen_await` is **not** an
independent vindication of the transcribed clause: on this one constructor we
widen the language relative to Brookes, and the operational and denotational
readings agree **by construction**.  The honest claim is that our operational
semantics agrees with `den` on the wider language.

The consistency checks do pass — an `await` whose body diverges or deadlocks has
no terminating execution, hence no step, hence denotes `⊥` — but that is a
sanity check, not a proof that the widened rule is Brookes's.
-/

universe u

namespace Isotope.Elgot.Brookes.SeqCst.Op

open Isotope.Elgot Isotope.Elgot.Brookes

variable {Loc Val : Type u}

section

variable [DecidableEq Loc] [DecidableEq Val]

/-! ## Atomic commands -/

/-- A command is *atomic* when every small step it takes terminates it: there
are no proper residuals, so the machine cannot be interrupted part-way through.
`skip`, assignment and `await` are atomic; `seq`, `par`, `ite` and `wh` are
not. -/
def Atomic (C : Com Loc Val) : Prop := ∀ μ oD ν, Red C μ oD ν → oD = none

/-- **Executions of an atomic command are trivial or complete.**  Any run of
steps from `some C` either takes no step at all or terminates, since the first
step already terminates.

The statement is over a variable target `y` with `y.1`/`y.2` projections: a
`Relation.ReflTransGen` induction requires the target index to be a variable,
so a conclusion pinning it to `(some C, μ)` or `(none, ν)` cannot be proved this
way. -/
theorem Atomic.steps_inv {C : Com Loc Val} (hA : Atomic C) {μ : Store Loc Val} :
    ∀ {y : Config Loc Val}, Relation.ReflTransGen CStep (some C, μ) y →
      y = (some C, μ) ∨ (y.1 = none ∧ opObs C μ y.2) := by
  intro y h
  induction h with
  | refl => exact Or.inl rfl
  | @tail b c hxy hyz ih =>
      rcases ih with h₁ | ⟨h₁, h₂⟩
      · cases h₁
        obtain ⟨c₁, c₂⟩ := c
        cases hA _ _ _ hyz
        exact Or.inr ⟨rfl, Relation.ReflTransGen.single hyz⟩
      · obtain ⟨b₁, b₂⟩ := b
        cases h₁
        exact absurd hyz id

/-- **Normal form for transition traces of an atomic command.**  All but the
last segment take no step, so they contribute stutter pairs; the last is a
single complete execution.

Stated in the generalized `Run` form the induction demands, with `some C` and
`none` entering as equational premises. -/
theorem Atomic.run_inv {C : Com Loc Val} (hA : Atomic C) :
    ∀ {t : Trace (Store Loc Val × Store Loc Val)}, TTrace C t →
      ∃ s μ ν, (∀ p ∈ s, p.1 = p.2) ∧ t = s ++ [(μ, ν)] ∧ opObs C μ ν := by
  suffices h : ∀ {oC : Option (Com Loc Val)} {t oE}, Run oC t oE →
      ∀ {C : Com Loc Val}, Atomic C → oC = some C → oE = none →
      ∃ s μ ν, (∀ p ∈ s, p.1 = p.2) ∧ t = s ++ [(μ, ν)] ∧ opObs C μ ν by
    intro t ht; exact h ht hA rfl rfl
  intro oC t oE hr
  induction hr with
  | refl oC => intro C hA h₁ h₂; cases h₁; exact absurd h₂ (by simp)
  | @cons D a oD b t oE hs hr ih =>
      intro C hA h₁ h₂
      cases h₁
      rcases hA.steps_inv hs with h₃ | ⟨h₃, h₄⟩
      · cases h₃
        obtain ⟨s, μ, ν, hst, ht, ho⟩ := ih hA rfl h₂
        refine ⟨(a, a) :: s, μ, ν, ?_, by rw [ht]; rfl, ho⟩
        intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · rfl
        · exact hst p hp
      · simp only at h₃ h₄
        cases h₃
        cases hr
        exact ⟨[], a, b, by simp, rfl, h₄⟩

/-- For an atomic command, termination is a single step. -/
theorem Atomic.opObs_iff {C : Com Loc Val} (hA : Atomic C) {μ ν : Store Loc Val} :
    opObs C μ ν ↔ Red C μ none ν := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with h₁ | ⟨b, hb, hbc⟩
    · exact absurd h₁ (by simp)
    · rcases hA.steps_inv hb with h₂ | ⟨h₂, h₃⟩
      · cases h₂; exact hbc
      · obtain ⟨b₁, b₂⟩ := b
        simp only at h₂
        cases h₂
        exact absurd hbc id
  · intro h; exact Relation.ReflTransGen.single h

/-- **An atomic command denotes an atomic computation**, namely the one whose
relation is its operational termination relation.  This is the shape of the
first three clauses of Proposition 6.2. -/
theorem opDen_of_atomic {C : Com Loc Val} (hA : Atomic C) :
    opDen C = SeqCst.atom (fun μ ν ↦ opObs C μ ν) := by
  apply Brookes.ext_mem
  intro t x
  constructor
  · rintro ⟨t₀, ht₀, hr⟩
    obtain ⟨s, μ, ν, hst, ht, ho⟩ := hA.run_inv ht₀
    refine SeqCst.mem_atom_iff.2 ⟨μ, ν, ho, Relation.ReflTransGen.trans ?_ hr⟩
    simp only at ht
    rw [ht]
    exact refines_stutter_prefix hst [(μ, ν)]
  · intro h
    obtain ⟨μ, ν, ho, hr⟩ := SeqCst.mem_atom_iff.1 h
    exact ⟨[(μ, ν)], Run.cons ho (Run.refl none), hr⟩

/-! ## `skip`, assignment and `await` are atomic -/

/-- `skip` terminates in one step. -/
theorem atomic_skip : Atomic (Com.skip : Com Loc Val) := by
  intro μ oD ν h; cases h; rfl

/-- An assignment terminates in one step. -/
theorem atomic_assign (ℓ : Loc) (e : Exp Loc Val) : Atomic (Com.assign ℓ e : Com Loc Val) := by
  intro μ oD ν h; cases h; rfl

/-- A conditional critical region terminates in one step: that is what makes it
critical. -/
theorem atomic_await (b : BExp Loc Val) (C : Com Loc Val) : Atomic (Com.await b C) := by
  intro μ oD ν h; cases h; rfl

/-! ## The atomic clauses of Proposition 6.2 -/

/-- `skip` terminates exactly in the state it started in. -/
theorem opObs_skip {μ ν : Store Loc Val} : opObs (Com.skip : Com Loc Val) μ ν ↔ ν = μ := by
  rw [atomic_skip.opObs_iff]
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact Red.skip _

/-- An assignment terminates exactly in the updated state. -/
theorem opObs_assign {ℓ : Loc} {e : Exp Loc Val} {μ ν : Store Loc Val} :
    opObs (Com.assign ℓ e : Com Loc Val) μ ν ↔ ν = Function.update μ ℓ (e.eval μ) := by
  rw [(atomic_assign ℓ e).opObs_iff]
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact Red.assign _ _ _

/-- `await B then C` terminates exactly when its test holds and its body
terminates — atomically, in one step of the outer machine. -/
theorem opObs_await {b : BExp Loc Val} {C : Com Loc Val} {μ ν : Store Loc Val} :
    opObs (Com.await b C) μ ν ↔ b.eval μ = true ∧ opObs C μ ν := by
  rw [(atomic_await b C).opObs_iff]
  constructor
  · intro h; cases h with | await hb hs => exact ⟨hb, steps_iff.1 hs⟩
  · rintro ⟨hb, hs⟩; exact Red.await hb (steps_iff.2 hs)

/-- **Proposition 6.2, `skip`.**  `T[skip] = {(s,s) | s ∈ S}†`.

The denotation is `test (fun _ ↦ true)`, not `pure ⋆`: the empty trace is not a
transition trace of anything, so `opDen` is ε-free just as `den` is. -/
theorem opDen_skip : opDen (Com.skip : Com Loc Val) = SeqCst.test (fun _ ↦ true) := by
  rw [opDen_of_atomic atomic_skip]
  congr 1
  funext μ ν
  simp [opObs_skip, eq_comm]

/-- **Proposition 6.2, assignment.**
`T[I:=E] = {(s,[s | I = n]) | (s,n) ∈ E[E]}†`. -/
theorem opDen_assign (ℓ : Loc) (e : Exp Loc Val) :
    opDen (Com.assign ℓ e) = SeqCst.atom fun μ ν ↦ ν = Function.update μ ℓ (e.eval μ) := by
  rw [opDen_of_atomic (atomic_assign ℓ e)]
  congr 1
  funext μ ν
  simp [opObs_assign]

/-- **Proposition 6.2, `await`.**
`T[await B then C] = {(s,s') ∈ T[C] | (s,tt) ∈ B[B]}†`.

As explained in the module docstring, this clause holds **by construction**: our
`Red.await` rule stipulates atomicity for an arbitrary body, widening the
language relative to Brookes, who restricts `await` bodies syntactically so that
his machine can justify atomicity.  Agreement here is therefore not an
independent check of the transcription. -/
theorem opDen_await (b : BExp Loc Val) (C : Com Loc Val) :
    opDen (Com.await b C) = SeqCst.atom fun μ ν ↦ b.eval μ = true ∧ SeqCst.obs (opDen C) μ ν := by
  rw [opDen_of_atomic (atomic_await b C)]
  congr 1
  funext μ ν
  exact propext (opObs_await.trans (and_congr_right fun _ ↦ opObs_iff.symm))

/-! ## The conditional -/

omit [DecidableEq Loc] in
/-- Negation of a boolean expression tests for falsity. -/
theorem neg_eval (b : BExp Loc Val) (μ : Store Loc Val) :
    (BExp.neg b).eval μ = true ↔ b.eval μ = false := by
  simp [BExp.eval]

attribute [local simp] neg_eval

/-- Taking the true branch: the conditional's own step contributes a stutter
pair, after which the machine is running `C₁`. -/
theorem ttrace_ite_left {b : BExp Loc Val} {C₁ C₂ : Com Loc Val} {μ : Store Loc Val}
    {w : Trace (Store Loc Val × Store Loc Val)} (hb : b.eval μ = true) (h : TTrace C₁ w) :
    TTrace (Com.ite b C₁ C₂) ((μ, μ) :: w) :=
  Run.cons (steps_single (Red.iteT hb)) h

/-- Taking the false branch. -/
theorem ttrace_ite_right {b : BExp Loc Val} {C₁ C₂ : Com Loc Val} {μ : Store Loc Val}
    {w : Trace (Store Loc Val × Store Loc Val)} (hb : b.eval μ = false) (h : TTrace C₂ w) :
    TTrace (Com.ite b C₁ C₂) ((μ, μ) :: w) :=
  Run.cons (steps_single (Red.iteF hb)) h

/-- **Proposition 6.2, the conditional.**
`T[if B then C₁ else C₂] = T[B];T[C₁] ∪ T[¬B];T[C₂]`.

The `⊆` half peels the first small step off a transition trace, which must be
`iteT` or `iteF`; the stutter pair that step contributes is exactly the one-pair
trace of the test, and the closure absorbs the seam by one mumble
(`refines_mumble_head`) and the peeled stutter prefix by
`refines_stutter_prefix`.  The `⊇` half is `ttrace_ite_left`/`ttrace_ite_right`. -/
theorem opDen_ite (b : BExp Loc Val) (C₁ C₂ : Com Loc Val) :
    opDen (Com.ite b C₁ C₂)
      = SeqCst.union2 (SeqCst.test b.eval >>= fun _ ↦ opDen C₁)
          (SeqCst.test (BExp.neg b).eval >>= fun _ ↦ opDen C₂) := by
  apply Brookes.ext_mem
  intro t x
  constructor
  · rintro ⟨t₀, ht₀, hr⟩
    obtain ⟨s, μ, ν, oD, ρ, oE, t', hst, ht, hred, hsteps, hrun⟩ := run_peel ht₀
    simp only at ht hr
    subst ht
    have hfin : (rewriting (Store Loc Val)).Refines ((μ, μ) :: (μ, ν) :: t') t :=
      ((refines_mumble_head μ ν t').trans
        (refines_stutter_prefix hst ((μ, ν) :: t'))).trans hr
    cases hred with
    | iteT hb =>
        refine SeqCst.mem_union2_iff.2 (Or.inl (Brookes.mem_of_refines ?_ hfin))
        refine (Brookes.mem_bind_iff _ _ _ x).2
          ⟨PUnit.unit, [(μ, μ)], (μ, ν) :: t',
            SeqCst.mem_atom_iff.2 ⟨μ, μ, ⟨hb, rfl⟩, Relation.ReflTransGen.refl⟩,
            mem_opDen (Run.cons hsteps hrun) x, Relation.ReflTransGen.refl⟩
    | iteF hb =>
        refine SeqCst.mem_union2_iff.2 (Or.inr (Brookes.mem_of_refines ?_ hfin))
        refine (Brookes.mem_bind_iff _ _ _ x).2
          ⟨PUnit.unit, [(μ, μ)], (μ, ν) :: t',
            SeqCst.mem_atom_iff.2 ⟨μ, μ, ⟨(neg_eval b μ).2 hb, rfl⟩,
              Relation.ReflTransGen.refl⟩,
            mem_opDen (Run.cons hsteps hrun) x, Relation.ReflTransGen.refl⟩
  · intro h
    rcases SeqCst.mem_union2_iff.1 h with h | h
    · obtain ⟨a, u, v, hu, hv, hruv⟩ := (Brookes.mem_bind_iff _ _ t x).1 h
      obtain ⟨μ, ν, ⟨hb, rfl⟩, hu'⟩ := SeqCst.mem_atom_iff.1 hu
      obtain ⟨v₀, hv₀, hv'⟩ := hv
      exact Brookes.mem_of_refines (mem_opDen (ttrace_ite_left hb hv₀) x)
        ((Rewriting.refines_append hu' hv').trans hruv)
    · obtain ⟨a, u, v, hu, hv, hruv⟩ := (Brookes.mem_bind_iff _ _ t x).1 h
      obtain ⟨μ, ν, ⟨hb, rfl⟩, hu'⟩ := SeqCst.mem_atom_iff.1 hu
      obtain ⟨v₀, hv₀, hv'⟩ := hv
      exact Brookes.mem_of_refines
        (mem_opDen (ttrace_ite_right ((neg_eval b ν).1 hb) hv₀) x)
        ((Rewriting.refines_append hu' hv').trans hruv)

end

end Isotope.Elgot.Brookes.SeqCst.Op
