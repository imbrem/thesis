import Isotope.LambdaIter.Signature.Category
import Isotope.LambdaIter.Subtyping.Semantics.Models

/-!
# Concrete signatures, and signature morphisms that are not identities

`Sig` is not an empty category: the three concrete models already in the
repository are built over signatures, and this file bundles two of them as
objects.  It then exhibits two non-identity endomorphisms, one acting on
effects and one acting on instructions, to show that `Sig.Hom` has content
beyond the identity.

## Honest boundary

Both examples fix the type component to the identity.  A signature morphism
with a non-trivial *type* component — for instance out of a signature with no
base types — needs the canonical extension of a map of base types to `Ty`,
which is deliberately not duplicated here (it belongs with the empty-signature
work).  So nothing in this file relates two *distinct* signatures.
-/

namespace Isotope.LambdaIter

open Subtyping.Semantics CategoryTheory

/-- The signature underlying the null model: no base types, no instructions,
and the two-element effect lattice. -/
def Sig.ofNull : Sig.{0} where
  Ty := Null.NullTy
  formers := inferInstance
  Instr := Null.NullInstr
  Eff := Subtyping.Semantics.Eff
  pureEff := Subtyping.Semantics.Eff.pure
  hasTy := inferInstance
  hasEff := inferInstance

/-- The signature underlying the bitvector model. -/
def Sig.ofBitVec : Sig.{0} where
  Ty := BitVecModel.BvTy
  formers := inferInstance
  Instr := BitVecModel.Instr
  Eff := Subtyping.Semantics.Eff
  pureEff := Subtyping.Semantics.Eff.pure
  hasTy := inferInstance
  hasEff := inferInstance

/-- Collapsing every effect to `pure` is an endomorphism of the null
signature: with no instructions there is nothing for `instr_eff` to
constrain, and `pure` is sent to `pure`. -/
def Sig.collapseNullEff : Sig.ofNull ⟶ Sig.ofNull where
  ty := id
  instr := id
  eff := fun _ => Subtyping.Semantics.Eff.pure
  ty_tensor _ _ := rfl
  ty_unit := rfl
  ty_coprod _ _ := rfl
  ty_empty := rfl
  instr_src f := f.elim
  instr_trg f := f.elim
  instr_eff f := f.elim
  eff_pure := rfl

theorem Sig.collapseNullEff_ne_id : Sig.collapseNullEff ≠ 𝟙 Sig.ofNull := by
  intro h
  have h' : Subtyping.Semantics.Eff.pure = Subtyping.Semantics.Eff.impure :=
    congrArg (fun F : Sig.ofNull ⟶ Sig.ofNull =>
      F.eff Subtyping.Semantics.Eff.impure) h
  exact absurd h' (by decide)

/-- Bitwise conjunction and addition have the same source type, target type
and effect, so replacing one by the other is an endomorphism of the bitvector
signature.  Signature morphisms therefore genuinely act on instructions, not
just on types. -/
def Sig.andToAdd : Sig.ofBitVec ⟶ Sig.ofBitVec where
  ty := id
  instr
    | .and n => .add n
    | f => f
  eff := id
  ty_tensor _ _ := rfl
  ty_unit := rfl
  ty_coprod _ _ := rfl
  ty_empty := rfl
  instr_src f := by cases f <;> rfl
  instr_trg f := by cases f <;> rfl
  instr_eff f := by cases f <;> rfl
  eff_pure := rfl

theorem Sig.andToAdd_ne_id : Sig.andToAdd ≠ 𝟙 Sig.ofBitVec := by
  intro h
  have h' : (BitVecModel.Instr.add 1) = BitVecModel.Instr.and 1 :=
    congrArg (fun F : Sig.ofBitVec ⟶ Sig.ofBitVec =>
      F.instr (BitVecModel.Instr.and 1)) h
  exact absurd h' (by decide)

end Isotope.LambdaIter
