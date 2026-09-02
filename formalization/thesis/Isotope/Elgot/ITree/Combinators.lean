import Isotope.Elgot.ITree.Relation
import Isotope.Elgot.ITree.Events

/-!
# Combinators and worked examples over the final-coalgebra API

Examples that the `destruct` layer makes newly expressible, kept separate from
`ITree/Examples.lean` because they depend on finality.

`forever` repeats a computation indefinitely.  Its three computation lemmas
exhibit the productivity distinction the weak model turns on: repeating a pure
computation is silent divergence (`forever_ret`), while repeating one that emits
an event is a genuinely infinite tree (`forever_vis_ne_diverge`).
-/

namespace Isotope.Elgot.ITree

open Isotope.Elgot

universe u

variable {E F : Type u → Type u} {A B : Type (u + 1)}


/-- The loop body of `forever`: run the computation, then loop. -/
def foreverBody (t : Tree E A) : PUnit.{u + 2} → Tree E (B ⊕ PUnit.{u + 2}) :=
  fun _ => t >>= fun _ => ret (Sum.inr PUnit.unit)

/-- Repeat a computation forever, discarding its results. -/
noncomputable def forever (t : Tree E A) : Tree E B :=
  Isotope.Elgot.iter (foreverBody t) PUnit.unit

/-- `forever` unfolds to one run of its body followed by itself. -/
theorem forever_unfold (t : Tree E A) : (forever t : Tree E B) = t >>= fun _ => forever t := by
  conv_lhs => rw [forever, iterate_apply]
  rw [foreverBody, bind_assoc]
  refine congrArg (t >>= ·) (funext fun _ => ?_)
  change (pure (Sum.inr PUnit.unit) : Tree E (B ⊕ PUnit.{u + 2})) >>= _ = _
  rw [pure_bind]
  rfl

/-- Repeating a diverging computation diverges. -/
@[simp] theorem forever_diverge : forever (E := E) (A := A) diverge = (diverge : Tree E B) := by
  rw [forever_unfold, diverge_bind]

/-- Repeating a pure computation diverges: the loop is unproductive. -/
@[simp] theorem forever_ret (a : A) : forever (ret a) = (diverge : Tree E B) := by
  rw [forever]
  refine Eq.trans (congrArg (fun f => Isotope.Elgot.iter f PUnit.unit) (funext fun _ => ?_))
    (iterate_ret_inr (E := E) (B := B) PUnit.unit)
  exact pure_bind a _

/-- Repeating a visible event emits it, then repeats. -/
theorem forever_vis {R : Type u} (e : E R) (k : R → Tree E A) :
    forever (vis e k) = (vis e (fun r => k r >>= fun _ => forever (vis e k)) : Tree E B) := by
  conv_lhs => rw [forever_unfold]
  exact vis_bind e k _

/-- A productive repetition is not divergence. -/
theorem forever_vis_ne_diverge {R : Type u} (e : E R) (k : R → Tree E A) :
    forever (vis e k) ≠ (diverge : Tree E B) := by
  rw [forever_vis]; exact vis_ne_diverge e _

/-! ## Worked refinement examples -/

/-- Divergence strictly refines a return. -/
theorem diverge_refines_ret (a : A) : Refines (diverge : Tree E A) (ret a) :=
  diverge_refines _

/-- A return does not refine divergence. -/
theorem not_ret_refines_diverge (a : A) : ¬ Refines (ret a) (diverge : Tree E A) := by
  intro h; exact ret_ne_diverge a (refines_diverge_iff.mp h)

/-! ## Relabelling and triggering -/

/-- The head of a triggered event. -/
@[simp] theorem Tree.destruct_trigger {R : Type u} (e : E R) :
    (trigger e).destruct = Part.some (.vis e (fun r => ret (ULift.up r))) :=
  Tree.destruct_vis e _

/-- Relabelling a triggered event triggers the relabelled event. -/
@[simp] theorem translate_trigger (φ : ∀ R : Type u, E R → F R) {R : Type u} (e : E R) :
    translate φ (trigger e) = trigger (φ R e) := by
  rw [trigger, translate_vis, trigger]
  exact congrArg (vis (φ R e)) (funext fun r => translate_ret φ _)

/-- Raising a triggered event is triggering it at the subevent. -/
@[simp] theorem send_trigger [Subevent E F] {R : Type u} (e : E R) :
    send (F := F) (trigger e) = Subevent.trigger e :=
  translate_trigger _ e

end Isotope.Elgot.ITree
