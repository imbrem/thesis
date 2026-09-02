import Isotope.Elgot.ITree.Laws
import Mathlib.Logic.Equiv.Defs

/-!
# Weak bisimulation, its setoid, and the quotient carrier

This module keeps the three layers of the construction explicitly apart.

* The **raw guarded layer** is `Tree.corec` (`ITree/Basic.lean`): an arbitrary
  `Part ∘ Visible E A`-coalgebra unfolds to a tree, and `corec_unique` says the
  unfolding is unique.  This is the guarded-corecursion interface; it never
  mentions any equivalence relation.
* The **relation layer** is `Bisim` below: two trees are related when every
  finite observation agrees.  Since observation charges depth only at visible
  events and reports `Part.none` for "no visible head ever", this is exactly
  weak (tau-insensitive) bisimulation, `eutt`, and *not* strong bisimulation:
  finite silent delays are not representable at all (`tau = id`).
* The **quotient layer** is `Tree E A` itself.  `bisim_iff_eq` shows `Bisim` is
  literally propositional equality on the extensional carrier, and
  `quotientEquiv` exhibits `Quotient (setoid E A) ≃ Tree E A`.  So the Elgot
  equations proved in `ITree/Laws.lean` hold as *equalities on the quotient*,
  with no further quotienting step required.

## Honest boundary

We do not construct a separate tau-sensitive type of raw interaction trees, and
therefore do not prove "`Tree E A` is the quotient of Xia-style ITrees by
`eutt`" as an internal theorem: `tau` is definitionally the identity here, so
the tau-sensitive object simply does not exist in this development.  What is
proved is the intrinsic characterisation above.
-/

namespace Isotope.Elgot.ITree

open Isotope.Elgot

universe u

/-- Weak bisimulation: agreement of every finite observation. -/
def Bisim {E : Type u → Type u} {A : Type (u + 1)} (x y : Tree E A) : Prop :=
  ∀ n, x.observe n = y.observe n

namespace Bisim

theorem refl {E : Type u → Type u} {A : Type (u + 1)} (x : Tree E A) : Bisim x x :=
  fun _ => rfl

theorem symm {E : Type u → Type u} {A : Type (u + 1)} {x y : Tree E A}
    (h : Bisim x y) : Bisim y x := fun n => (h n).symm

theorem trans {E : Type u → Type u} {A : Type (u + 1)} {x y z : Tree E A}
    (h₁ : Bisim x y) (h₂ : Bisim y z) : Bisim x z := fun n => (h₁ n).trans (h₂ n)

end Bisim

/-- Weak bisimulation is exactly equality on the extensional carrier. -/
theorem bisim_iff_eq {E : Type u → Type u} {A : Type (u + 1)} {x y : Tree E A} :
    Bisim x y ↔ x = y := Tree.eq_iff_observe.symm

/-- The weak-bisimulation setoid. -/
def setoid (E : Type u → Type u) (A : Type (u + 1)) : Setoid (Tree E A) where
  r := Bisim
  iseqv := ⟨Bisim.refl, Bisim.symm, Bisim.trans⟩

/-- The extensional carrier *is* the weak-bisimulation quotient. -/
def quotientEquiv (E : Type u → Type u) (A : Type (u + 1)) :
    Quotient (setoid E A) ≃ Tree E A where
  toFun := Quotient.lift id (fun _ _ h => bisim_iff_eq.mp h)
  invFun := Quotient.mk (setoid E A)
  left_inv := by rintro ⟨t⟩; rfl
  right_inv := fun _ => rfl

section Congruence

variable {E : Type u → Type u} {A B C : Type (u + 1)}

/-- Sequencing respects weak bisimulation in both arguments. -/
theorem Bisim.bind {x y : Tree E A} (h : Bisim x y) {k l : A → Tree E B}
    (hk : ∀ a, Bisim (k a) (l a)) : Bisim (x >>= k) (y >>= l) := by
  rw [bisim_iff_eq] at h ⊢
  subst h
  exact congrArg _ (funext fun a => bisim_iff_eq.mp (hk a))

/-- A visible event respects weak bisimulation of its continuations. -/
theorem Bisim.vis {R : Type u} (e : E R) {k l : R → Tree E A}
    (h : ∀ r, Bisim (k r) (l r)) : Bisim (ITree.vis e k) (ITree.vis e l) := by
  rw [bisim_iff_eq]
  exact congrArg _ (funext fun r => bisim_iff_eq.mp (h r))

/-- Iteration respects weak bisimulation of its body. -/
theorem Bisim.iterate {f g : A → Tree E (B ⊕ A)} (h : ∀ a, Bisim (f a) (g a)) (a : A) :
    Bisim (Isotope.Elgot.iter f a) (Isotope.Elgot.iter g a) := by
  rw [bisim_iff_eq]
  exact congrFun (congrArg _ (funext fun a => bisim_iff_eq.mp (h a))) a

/-- Guarded corecursion respects pointwise equality of coalgebras. -/
theorem Bisim.corec {X : Type (u + 1)} (h₁ h₂ : X → Part (Visible E A X))
    (h : ∀ x, h₁ x = h₂ x) (x : X) : Bisim (ITree.corec h₁ x) (ITree.corec h₂ x) := by
  rw [bisim_iff_eq, funext h]

end Congruence

end Isotope.Elgot.ITree
