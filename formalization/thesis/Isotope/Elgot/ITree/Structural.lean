import Isotope.Elgot.ITree.Finality
import Isotope.Elgot.ITree.Examples

/-!
# Structural laws in `destruct` form

The monad structure of `Tree E`, restated at the level of the final-coalgebra
structure map.  `Tree.destruct_bind` is the head-exposing form of `bind`: the
head of `t >>= k` is the head of `t`, with a return head handing control to `k`
and a visible head keeping its event and pushing the continuation under it.
-/

namespace Isotope.Elgot.ITree

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

end Isotope.Elgot.ITree
