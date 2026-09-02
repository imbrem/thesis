import Mathlib.Logic.Relation
import Mathlib.Data.Set.Lattice

/-!
# Brookes traces and trace-rewriting systems

A *trace* is a finite word over an alphabet of events.  For the standard Brookes
model the alphabet is `S × S`, the *rely-guarantee pairs* over a state type `S`:
`⟨μ, ρ⟩` records one step in which the program relied on the state `μ` handed to
it by the environment and guaranteed the state `ρ` back.

A Brookes model is determined by a *closure operator* on sets of traces.  Rather
than axiomatise closure operators abstractly, we present one by its generating
one-step rewriting system, packaged as a `Rewriting`.  The two congruence fields
say that rewriting may be performed inside any context; they are exactly what
makes the induced closure compatible with concatenation, which is what the
Brookes monad laws need (the paper's axioms — extensive, idempotent, distributing
over unions — are *not* by themselves enough for `B_c` to be a monad).

`Rewriting` is a *parameter*, not a class, so that several closure operators over
the same alphabet (sequential consistency, TSO, release/acquire, …) can coexist
without instance ambiguity.
-/

namespace Isotope.Elgot.Brookes

universe u

variable {E : Type u}

/-- A finite trace: a word of events. -/
abbrev Trace (E : Type u) : Type u := List E

/-- A one-step trace-rewriting system on `Trace E`, generating a Brookes closure
operator.  Rewriting must be a congruence for consing an event on the front and
for appending a suffix; together these make it a congruence for concatenation. -/
structure Rewriting (E : Type u) : Type u where
  /-- One rewriting step, read as "the left trace may be replaced by the right". -/
  Step : Trace E → Trace E → Prop
  /-- Rewriting may be performed under a prefix event. -/
  step_cons : ∀ (e : E) {t t' : Trace E}, Step t t' → Step (e :: t) (e :: t')
  /-- Rewriting may be performed with a suffix appended. -/
  step_appendRight : ∀ {t t' : Trace E}, Step t t' → ∀ u : Trace E, Step (t ++ u) (t' ++ u)

namespace Rewriting

variable (c : Rewriting E)

/-- Rewriting may be performed under any prefix. -/
theorem step_appendLeft (u : Trace E) {t t' : Trace E} (h : c.Step t t') :
    c.Step (u ++ t) (u ++ t') := by
  induction u with
  | nil => exact h
  | cons e _ ih => exact c.step_cons e ih

/-- `c.Refines t t'` holds when `t'` is reachable from `t` by finitely many
rewriting steps.  This is the reachability order underlying `c`-closure. -/
abbrev Refines : Trace E → Trace E → Prop := Relation.ReflTransGen c.Step

variable {c}

/-- Refinement is a congruence for appending a fixed suffix. -/
theorem refines_appendRight {t t' : Trace E} (h : c.Refines t t') (u : Trace E) :
    c.Refines (t ++ u) (t' ++ u) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (c.step_appendRight hstep u)

/-- Refinement is a congruence for prepending a fixed prefix. -/
theorem refines_appendLeft (u : Trace E) {t t' : Trace E} (h : c.Refines t t') :
    c.Refines (u ++ t) (u ++ t') := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (c.step_appendLeft u hstep)

/-- The key congruence: refinement is compatible with trace concatenation.
This is the extra axiom a closure operator needs for `B_c` to be a monad. -/
theorem refines_append {t u t' u' : Trace E} (h : c.Refines t t') (h' : c.Refines u u') :
    c.Refines (t ++ u) (t' ++ u') :=
  (refines_appendRight h u).trans (refines_appendLeft t' h')

end Rewriting

end Isotope.Elgot.Brookes
