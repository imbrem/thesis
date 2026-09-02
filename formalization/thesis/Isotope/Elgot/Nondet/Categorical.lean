import Isotope.Elgot.Nondet.Powerset
import Isotope.Elgot.Nondet.Countable
import Isotope.CategoryTheory.Monad.Elgot

/-!
# Kleisli/Freyd structure of the nondeterministic models

`Isotope.CategoryTheory.Kleisli.Type` derives the categorical Elgot structure of `Kleisli (TM m)`
generically from `Iterate m` and `LawfulElgotMonad m`.  The theorems here record that the
powerset and countable-powerset models really do discharge those hypotheses, so their Kleisli
categories are (strong, distributive) Elgot Freyd categories.

They are stated with `Nonempty` because the underlying instances are already global; the point is
that instance synthesis succeeds at these carriers, not that a new instance is introduced.
-/

namespace Isotope.Elgot.Nondet

open CategoryTheory CategoryTheory.Kleisli.Type

universe u

/-- The Kleisli category of the powerset monad is an Elgot category. -/
theorem elgotCategory_setM :
    Nonempty (ElgotCategory (Kleisli (TM SetM.{u}))) := ⟨inferInstance⟩

/-- Pure functions and nondeterministic computations form an Elgot Freyd category. -/
theorem elgotFreydCategory_setM :
    Nonempty (ElgotFreydCategory (Kleisli.Adjunction.toKleisli (TM SetM.{u}))) := ⟨inferInstance⟩

/-- The powerset model is a strong Elgot Freyd category, so it interprets the full
premonoidal iteration structure. -/
theorem strongElgotFreydCategory_setM :
    Nonempty (StrongElgotFreydCategory (Kleisli.Adjunction.toKleisli (TM SetM.{u}))) :=
  ⟨inferInstance⟩

/-- The Kleisli category of countable nondeterminism is an Elgot category. -/
theorem elgotCategory_cset :
    Nonempty (ElgotCategory (Kleisli (TM CSet.{u}))) := ⟨inferInstance⟩

/-- Countable nondeterminism is a strong Elgot Freyd category. -/
theorem strongElgotFreydCategory_cset :
    Nonempty (StrongElgotFreydCategory (Kleisli.Adjunction.toKleisli (TM CSet.{u}))) :=
  ⟨inferInstance⟩

end Isotope.Elgot.Nondet
