import Isotope.Elgot.RA.Iteration
import Isotope.CategoryTheory.Monad.Elgot

/-!
# Categorical structure of the release/acquire Kleisli category

Nothing here is proved by hand: `Isotope/CategoryTheory/Monad/Elgot.lean`
derives the Elgot and Elgot-Freyd structure of the Kleisli category from
`LawfulMonad` and `LawfulElgotMonad` alone.  This file only records that the
release/acquire monad supplies them.
-/

universe u

namespace Isotope.Elgot.RA

open CategoryTheory

variable (Loc Val : Type)

/-- The Kleisli category of the release/acquire monad is an Elgot category. -/
theorem nonempty_elgotCategory :
    Nonempty (ElgotCategory (Kleisli (Kleisli.Type.TM (Comp Loc Val : Type u → Type u)))) :=
  ⟨inferInstance⟩

/-- It is an Elgot Freyd category over the pure-map inclusion. -/
theorem nonempty_elgotFreydCategory :
    Nonempty (ElgotFreydCategory
      (Kleisli.Adjunction.toKleisli (Kleisli.Type.TM (Comp Loc Val : Type u → Type u)))) :=
  ⟨inferInstance⟩

end Isotope.Elgot.RA
