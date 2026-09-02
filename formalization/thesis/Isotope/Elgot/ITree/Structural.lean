import Isotope.Elgot.ITree.Finality
import Isotope.Elgot.ITree.Examples

/-!
# Structural laws in `destruct` form

The monad and iteration structure of `Tree E`, restated at the level of the
final-coalgebra structure map.  `Tree.destruct_bind` is the head-exposing form
of `bind`: the head of `t >>= k` is the head of `t`, with a return head handing
control to `k` and a visible head keeping its event and pushing the continuation
under it.  `Tree.destruct_map` and `Tree.destruct_iterate` are the analogous
forms for `Functor.map` and for the Elgot iteration operator, the latter being
the fixpoint law in head form.
-/

namespace Isotope.Elgot.ITree

open Isotope.Elgot

universe u

variable {E : Type u → Type u} {A B : Type (u + 1)}

/-- Destructing a sequential composition. -/
theorem Tree.destruct_bind (t : Tree E A) (k : A → Tree E B) :
    (t >>= k).destruct = t.destruct >>= fun v => match v with
      | .ret a => (k a).destruct
      | .vis e j => Part.some (.vis e (fun r => j r >>= k)) := by
  rcases Tree.cases_three t with rfl | ⟨a, rfl⟩ | ⟨R, e, j, rfl⟩
  · rw [diverge_bind, Tree.destruct_diverge, Tree.destruct_diverge]
    simp
  · rw [Tree.destruct_ret]
    rw [show ((ret a : Tree E A) >>= k) = k a from pure_bind a k]
    simp
  · rw [vis_bind, Tree.destruct_vis, Tree.destruct_vis]
    simp

/-- The head of a pure computation. -/
@[simp] theorem Tree.destruct_pure (a : A) :
    (pure a : Tree E A).destruct = Part.some (.ret a) := Tree.destruct_ret a

/-- Destructing a mapped tree: the head keeps its shape, with `f` applied to a
returned value and pushed under a visible event. -/
theorem Tree.destruct_map (f : A → B) (t : Tree E A) :
    (f <$> t).destruct = (fun v => match v with
      | .ret a => Visible.ret (f a)
      | .vis e j => Visible.vis e (fun r => f <$> j r)) <$> t.destruct := by
  rw [show (f <$> t) = t >>= (fun a => pure (f a)) from
    (bind_pure_comp f t).symm, Tree.destruct_bind]
  rw [Part.map_eq_map, ← Part.bind_some_eq_map]
  refine congrArg (Part.bind t.destruct) (funext fun v => ?_)
  cases v with
  | ret a => exact Tree.destruct_ret _
  | vis e j =>
      refine congrArg Part.some (congrArg (Visible.vis e) (funext fun r => ?_))
      exact (bind_pure_comp f (j r)).symm

/-- Destructing an iteration: the fixpoint law in head form.  A recursive
return re-enters the loop, a final return leaves it, and a visible event is
emitted with the loop pushed under its continuation. -/
theorem Tree.destruct_iterate (f : A → Tree E (B ⊕ A)) (a : A) :
    (Isotope.Elgot.iter f a).destruct = (f a).destruct >>= fun v => match v with
      | .ret (.inl b) => Part.some (.ret b)
      | .ret (.inr a') => (Isotope.Elgot.iter f a').destruct
      | .vis e j => Part.some (.vis e (fun r =>
          j r >>= Sum.elim pure (Isotope.Elgot.iter f))) := by
  rw [iterate_apply f a, Tree.destruct_bind]
  refine congrArg (Part.bind (f a).destruct) (funext fun v => ?_)
  cases v with
  | ret s => cases s <;> rfl
  | vis e j => rfl

end Isotope.Elgot.ITree
