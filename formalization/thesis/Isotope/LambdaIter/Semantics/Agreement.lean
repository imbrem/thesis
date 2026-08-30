import Isotope.CategoryTheory.Monad.Types
import Isotope.LambdaIter.Semantics.Categorical
import Isotope.LambdaIter.Semantics.Denotation

/-!
# Agreement of categorical and monadic lambda-iter semantics

This file specializes the categorical interfaces to the set-valued model and its Kleisli
category.  The final agreement theorem is intentionally stated pointwise on the underlying
Kleisli arrow.
-/

universe u v w q r

namespace Isotope.LambdaIter.Semantics

open CategoryTheory CategoryTheory.Limits
open Isotope.Elgot
open Isotope.LambdaIter.LocallyNameless

namespace Categorical

variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable [Semantics.TypeModel.{u, v} τ]

/-- A set-valued type model is a categorical type model in `Type`. -/
@[reducible] noncomputable def ofTypeModel : Categorical.TypeModel τ (Type v) where
  obj := Semantics.TypeModel.interp
  tensorIso A B := Equiv.toIso (Semantics.TypeModel.tensorEquiv A B)
  unitIso :=
    { hom := fun _ => PUnit.unit
      inv := fun _ => Semantics.TypeModel.unitEquiv.symm ()
      hom_inv_id := by
        funext x
        exact Semantics.TypeModel.unitEquiv.injective
          (Semantics.TypeModel.unitEquiv.apply_symm_apply ())
      inv_hom_id := by funext x; cases x; rfl }
  coprodIso A B := (Equiv.toIso (Semantics.TypeModel.coprodEquiv A B)).trans
    (Types.binaryCoproductIso _ _).symm
  emptyIsInitial := IsInitial.ofUniqueHom
    (fun X z => Empty.elim (Semantics.TypeModel.emptyEquiv z))
    (fun X f => by funext z; exact Empty.elim (Semantics.TypeModel.emptyEquiv z))
  subty d := Semantics.TypeModel.coe d

variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Semantics.InstructionModel Φ τ ε m]

/-- A monadic instruction interpretation is precisely a Kleisli instruction interpretation. -/
@[reducible] def ofInstructionModel : Categorical.InstructionModel
    (CategoryTheory.Kleisli.Adjunction.toKleisli (CategoryTheory.ofTypeMonad m))
    (ofTypeModel (τ := τ)) Φ where
  denote f := CategoryTheory.Kleisli.Hom.mk
    (by
      simpa [ofTypeModel, CategoryTheory.Kleisli.Adjunction.toKleisli] using
        (Semantics.InstructionModel.denote
          (Φ := Φ) (τ := τ) (ε := ε) (m := m) f))

end Categorical

end Isotope.LambdaIter.Semantics
