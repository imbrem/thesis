import Isotope.Elgot.Brookes.SeqCst.Syntax

/-!
# A small-step machine for the shared-variable parallel language

`Isotope/Elgot/Brookes/SeqCst/Syntax.lean` *transcribes* Brookes's Proposition
6.2 and takes its clauses as the definition of the trace semantics `den`.  This
file begins closing that gap by giving the language an operational semantics,
against which Proposition 6.2 becomes a theorem (`Op.opDen_eq_den`, downstream).

A *configuration* is a residual command together with a store; the residual is
`none` once the command has terminated, so that termination is a property of the
configuration rather than a distinguished `skip`.  `Red C μ oD ν` is one small
step from the (running) configuration `(some C, μ)` to `(oD, ν)`, and
`Reds` is its reflexive-transitive closure.

The two relations must be defined **mutually**: the `await` rule fires only when
its body can run to completion, so it takes a `Reds` premise.  That occurrence
is strictly positive — it is a premise of a constructor of a relation in the
same mutual family — so Lean accepts the block as an ordinary inductive
definition: no fuel parameter, no stratification by `await`-depth, and no
well-founded recursion.  (`Relation.ReflTransGen CStep` in the premise, by
contrast, is *not* strictly positive, because `CStep` mentions `Red`.)

Reasoning about `Reds` directly is unpleasant — its own recursor is the
recursor of the mutual family, with a minor premise for each of the fourteen
`Red` constructors.  `steps_iff` therefore transports it once and for all to
`Relation.ReflTransGen CStep`, where `trans`, `head`, `tail`, `single`,
`cases_head`, `cases_tail` and `head_induction_on` are available from Mathlib.
**`Reds` is used only in the `await` constructor and in `steps_iff`; every
subsequent definition and proof in `Op/` uses `Relation.ReflTransGen CStep`.**

## Deviations from the paper

Brookes's §3 transition system is over finite partial states with a
`free[C] ⊆ dom(s)` discipline, and restricts `await` bodies syntactically to
finite sequences of assignments.  `Red`/`Reds` is the natural total-state
reading of it on the unrestricted syntax of `SeqCst.Com`; in particular the
`await` rule *stipulates* atomicity for an arbitrary body, including bodies
containing `par` and nested `await`, which is precisely what Brookes's syntactic
restriction rules out.
-/

universe u

namespace Isotope.Elgot.Brookes.SeqCst.Op

open Isotope.Elgot Isotope.Elgot.Brookes

variable {Loc Val : Type u}

/-- A machine configuration: a residual command, `none` if the command has
terminated, together with the current store. -/
abbrev Config (Loc Val : Type u) : Type u := Option (Com Loc Val) × Store Loc Val

section

variable [DecidableEq Loc] [DecidableEq Val]

mutual

/-- One small step of the machine: `Red C μ oD ν` says the running configuration
`(some C, μ)` steps to `(oD, ν)`, where `oD = none` means the command has just
terminated.  Both threads of a `par` may step, and `await` steps only when its
guard holds and its body runs to completion — atomically, in a single step. -/
inductive Red : Com Loc Val → Store Loc Val → Option (Com Loc Val) → Store Loc Val → Prop
  | /-- `skip` terminates, leaving the store alone. -/
    skip (μ) : Red Com.skip μ none μ
  | /-- An assignment terminates, updating the store atomically. -/
    assign (ℓ : Loc) (e : Exp Loc Val) (μ) :
      Red (Com.assign ℓ e) μ none (Function.update μ ℓ (e.eval μ))
  | /-- The first component of a sequence steps, and has not yet terminated. -/
    seqL {C₁ μ C₁' ν C₂} : Red C₁ μ (some C₁') ν → Red (Com.seq C₁ C₂) μ (some (Com.seq C₁' C₂)) ν
  | /-- The first component of a sequence terminates, exposing the second. -/
    seqR {C₁ μ ν C₂} : Red C₁ μ none ν → Red (Com.seq C₁ C₂) μ (some C₂) ν
  | /-- The left thread steps, and has not yet terminated. -/
    parL {C₁ μ C₁' ν C₂} : Red C₁ μ (some C₁') ν → Red (Com.par C₁ C₂) μ (some (Com.par C₁' C₂)) ν
  | /-- The left thread terminates, leaving the right one running. -/
    parL' {C₁ μ ν C₂} : Red C₁ μ none ν → Red (Com.par C₁ C₂) μ (some C₂) ν
  | /-- The right thread steps, and has not yet terminated. -/
    parR {C₂ μ C₂' ν C₁} : Red C₂ μ (some C₂') ν → Red (Com.par C₁ C₂) μ (some (Com.par C₁ C₂')) ν
  | /-- The right thread terminates, leaving the left one running. -/
    parR' {C₂ μ ν C₁} : Red C₂ μ none ν → Red (Com.par C₁ C₂) μ (some C₁) ν
  | /-- A conditional whose guard holds selects its first branch. -/
    iteT {b C₁ C₂ μ} : b.eval μ = true → Red (Com.ite b C₁ C₂) μ (some C₁) μ
  | /-- A conditional whose guard fails selects its second branch. -/
    iteF {b C₁ C₂ μ} : b.eval μ = false → Red (Com.ite b C₁ C₂) μ (some C₂) μ
  | /-- A loop whose guard holds unfolds. -/
    whT {b C μ} : b.eval μ = true → Red (Com.wh b C) μ (some (Com.seq C (Com.wh b C))) μ
  | /-- A loop whose guard fails terminates. -/
    whF {b C μ} : b.eval μ = false → Red (Com.wh b C) μ none μ
  | /-- A conditional critical region whose guard holds runs its body to
    completion in one indivisible step. -/
    await {b C μ ν} : b.eval μ = true → Reds (some C, μ) ((none : Option (Com Loc Val)), ν) →
      Red (Com.await b C) μ none ν

/-- The reflexive-transitive closure of `Red` on configurations, defined
mutually with it because the `await` rule needs it as a premise.  Use
`steps_iff` to work with `Relation.ReflTransGen CStep` instead. -/
inductive Reds : Config Loc Val → Config Loc Val → Prop
  | /-- No steps. -/ refl (x) : Reds x x
  | /-- One more step at the end. -/
    tail {x C μ oD ν} : Reds x (some C, μ) → Red C μ oD ν → Reds x (oD, ν)

end

/-- The induction principle for `Reds` alone, obtained from the mutual recursor
by taking `True` as the motive for `Red`.

Lean's `induction ... using` tactic rejects this eliminator ("too many targets"),
so apply it directly instead:
`refine Reds.rec' (motive := fun a b ↦ _) (fun _ ↦ _) (fun _ hstep ih ↦ _) h`. -/
theorem Reds.rec' {motive : Config Loc Val → Config Loc Val → Prop}
    (refl : ∀ x, motive x x)
    (tail : ∀ {x : Config Loc Val} {C μ oD ν}, Reds x (some C, μ) → Red C μ oD ν →
      motive x (some C, μ) → motive x (oD, ν))
    {x y : Config Loc Val} (h : Reds x y) : motive x y :=
  Reds.rec (motive_1 := fun _ _ _ _ _ ↦ True) (motive_2 := fun a b _ ↦ motive a b)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial)
    refl (fun hs hstep ih _ ↦ tail hs hstep ih) h

/-- One small step, as a relation on configurations: a terminated configuration
has no successor. -/
def CStep : Config Loc Val → Config Loc Val → Prop
  | (some C, μ), (oD, ν) => Red C μ oD ν
  | (none, _), _ => False

/-- A step out of a running configuration is a reduction of its command. -/
@[simp] theorem cstep_some {C : Com Loc Val} {μ oD ν} :
    CStep (some C, μ) (oD, ν) ↔ Red C μ oD ν := Iff.rfl

/-- A terminated configuration takes no step. -/
@[simp] theorem cstep_none {μ : Store Loc Val} {y : Config Loc Val} :
    ¬ CStep ((none : Option (Com Loc Val)), μ) y := id

/-- **The escape hatch.**  The mutually-defined `Reds` is the reflexive-
transitive closure of `CStep`, so all of Mathlib's `Relation.ReflTransGen` API
applies to it.  Every later definition in `Op/` is phrased with
`Relation.ReflTransGen CStep`. -/
theorem steps_iff {x y : Config Loc Val} : Reds x y ↔ Relation.ReflTransGen CStep x y := by
  constructor
  · intro h
    refine Reds.rec' (motive := fun a b ↦ Relation.ReflTransGen CStep a b)
      (fun _ ↦ Relation.ReflTransGen.refl) (fun _ hstep ih ↦ ih.tail hstep) h
  · intro h
    induction h with
    | refl => exact Reds.refl _
    | @tail b c hxy hyz ih =>
        obtain ⟨b1, b2⟩ := b
        obtain ⟨c1, c2⟩ := c
        cases b1 with
        | none => exact absurd hyz id
        | some C => exact Reds.tail ih hyz

/-- A terminated configuration is stuck: it can only reach itself.

Note the shape of the statement: `Relation.ReflTransGen` induction demands that
the *target* be a variable, so the conclusion is an equation rather than a
pattern in the index position.  Every inversion lemma in `Op/` is stated this
way. -/
theorem steps_none_inv {μ : Store Loc Val} {y : Config Loc Val}
    (h : Relation.ReflTransGen CStep ((none : Option (Com Loc Val)), μ) y) : y = (none, μ) := by
  induction h with
  | refl => rfl
  | @tail b c hxy hyz ih => subst ih; exact absurd hyz id

/-- A single `Red` step is a `CStep` sequence. -/
theorem steps_single {C : Com Loc Val} {μ oD ν} (h : Red C μ oD ν) :
    Relation.ReflTransGen CStep (some C, μ) (oD, ν) :=
  Relation.ReflTransGen.single h

end

end Isotope.Elgot.Brookes.SeqCst.Op
