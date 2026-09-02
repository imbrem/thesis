import Isotope.Elgot.Basic

/-!
# Generic Kleisli lemmas

The category laws for `kcomp` on an arbitrary lawful monad, used to reason about the
`pflush`-sandwiched TSO operations without unfolding them.

## Honest boundary

Nothing but the monad laws; no iteration, no effects.
-/

universe u

namespace Isotope.Elgot

variable {m : Type u → Type u} [Monad m] [LawfulMonad m] {A B C D : Type u}

/-- Kleisli composition is associative. -/
theorem kcomp_assoc (f : A → m B) (g : B → m C) (h : C → m D) :
    kcomp (kcomp f g) h = kcomp f (kcomp g h) := by
  funext a; simp only [kcomp, bind_assoc]; rfl

/-- `pure` is a left unit for Kleisli composition. -/
@[simp] theorem pure_kcomp (f : A → m B) : kcomp (pure : A → m A) f = f := by
  funext a; simp [kcomp]

/-- `pure` is a right unit for Kleisli composition. -/
@[simp] theorem kcomp_pure (f : A → m B) : kcomp f (pure : B → m B) = f := by
  funext a; simp [kcomp]

end Isotope.Elgot
