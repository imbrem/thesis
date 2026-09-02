import Isotope.Elgot.Transformer.Reader
import Isotope.Elgot.Transformer.State
import Isotope.Elgot.Transformer.Writer
import Isotope.Elgot.Nondet
import Isotope.CategoryTheory.Monad.Elgot
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Kleisli/Freyd structure of the transformed monads

`Isotope.CategoryTheory.Kleisli.Type` derives the categorical Elgot structure of `Kleisli (TM m)`
generically from `Iterate m` and `LawfulElgotMonad m`.  The theorems here record that the reader,
state and writer transformers really do discharge those hypotheses over the concrete base monads
available on this branch, so their Kleisli categories are (strong) Elgot Freyd categories.

They are stated with `Nonempty` because the underlying instances are already global; the point is
that instance synthesis succeeds at these carriers, not that a new instance is introduced.

`Set` is not a global `Monad` in Mathlib, so the nondeterministic examples use the `SetM` wrapper
of `Isotope.Elgot.Nondet.Powerset`.
-/

namespace Isotope.Elgot.Transformer

open CategoryTheory CategoryTheory.Kleisli.Type

universe u

/-- Reader over partiality is an Elgot category. -/
theorem elgotCategory_readerT_part (R : Type u) :
    Nonempty (ElgotCategory (Kleisli (TM (ReaderT R _root_.Part.{u})))) := ⟨inferInstance⟩

/-- State over partiality is a strong Elgot Freyd category, so it interprets the full premonoidal
iteration structure. -/
theorem strongElgotFreydCategory_stateT_part (S : Type u) :
    Nonempty (StrongElgotFreydCategory
      (Kleisli.Adjunction.toKleisli (TM (StateT S _root_.Part.{u})))) := ⟨inferInstance⟩

/-- Writer over partiality is a strong Elgot Freyd category. -/
theorem strongElgotFreydCategory_writerT_part (E : Type u) :
    Nonempty (StrongElgotFreydCategory
      (Kleisli.Adjunction.toKleisli (TM (WriterT (FreeMonoid E) _root_.Part.{u})))) :=
  ⟨inferInstance⟩

/-- State over unbounded nondeterminism is a strong Elgot Freyd category. -/
theorem strongElgotFreydCategory_stateT_setM (S : Type u) :
    Nonempty (StrongElgotFreydCategory
      (Kleisli.Adjunction.toKleisli (TM (StateT S SetM.{u})))) := ⟨inferInstance⟩

/-- Reader over unbounded nondeterminism is an Elgot category. -/
theorem elgotCategory_readerT_setM (R : Type u) :
    Nonempty (ElgotCategory (Kleisli (TM (ReaderT R SetM.{u})))) := ⟨inferInstance⟩

end Isotope.Elgot.Transformer
