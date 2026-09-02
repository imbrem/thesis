import Isotope.Elgot.TraceSet.Laws
import Isotope.CategoryTheory.Monad.Elgot

/-!
# Kleisli/Freyd structure of the trace-set model

`Isotope.CategoryTheory.Kleisli.Type` derives the categorical Elgot structure of `Kleisli (TM m)`
generically from `Iterate m` and `LawfulElgotMonad m`.  The theorems here record that the
nondeterministic trace-set model really does discharge those hypotheses, so its Kleisli category
is a (strong) Elgot Freyd category.

They are stated with `Nonempty` because the underlying instances are already global; the point is
that instance synthesis succeeds at this carrier, not that a new instance is introduced.
-/

namespace Isotope.Elgot.TraceSet

open CategoryTheory CategoryTheory.Kleisli.Type

universe u

variable (E T : Type u) [Monoid E] [MulAction E T]

/-- The Kleisli category of the trace-set monad is an Elgot category. -/
theorem elgotCategory :
    Nonempty (ElgotCategory (Kleisli (TM (TraceSet E T)))) := ⟨inferInstance⟩

/-- Pure functions and trace-set computations form an Elgot Freyd category. -/
theorem elgotFreydCategory :
    Nonempty (ElgotFreydCategory (Kleisli.Adjunction.toKleisli (TM (TraceSet E T)))) :=
  ⟨inferInstance⟩

/-- The trace-set model is a strong Elgot Freyd category, so it interprets the full
premonoidal iteration structure. -/
theorem strongElgotFreydCategory :
    Nonempty (StrongElgotFreydCategory (Kleisli.Adjunction.toKleisli (TM (TraceSet E T)))) :=
  ⟨inferInstance⟩

end Isotope.Elgot.TraceSet
