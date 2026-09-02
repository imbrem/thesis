import Isotope.Elgot.ITree.Examples
import Isotope.LambdaIter.Semantics.Agreement.Iteration

/-!
# The Kleisli/Freyd structure carried by weak interaction trees

`Tree E : Type (u+1) → Type (u+1)` is homogeneous, so every downstream
construction in `Isotope/CategoryTheory/Monad/Elgot.lean` — which fixes
`m : Type w → Type w` — instantiates at `w := u + 1`.  This file records the
resulting structures by name so that they are elaborated (and hence checked)
rather than merely available in principle.

## Honest boundary

This is the *categorical* half of the connection only.  A concrete lambda-iter
denotation additionally needs `Semantics.TypeModel` and
`Semantics.InstructionModel` instances at a concrete type/instruction universe,
which no model in this repository currently supplies for any monad.  The one
model-specific obstruction to writing one is recorded in `interpObstruction`
below: an event signature `E : Type u → Type u` has responses in `Type u`, while
`TypeModel.interp` for `Tree E` must land in `Type (u+1)`, so every instruction
denotation built from `vis` pays a `ULift`.
-/

namespace Isotope.Elgot.ITree

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Kleisli.Type

universe u

variable (E : Type u → Type u)

/-- Iteration in the Kleisli category of weak interaction trees. -/
@[reducible] noncomputable def kleisliIteration : Iteration (Kleisli (TM (Tree E))) := inferInstance

/-- The Kleisli category of weak interaction trees is an Elgot category. -/
theorem kleisliElgotCategory : ElgotCategory (Kleisli (TM (Tree E))) := inferInstance

/-- Pure functions into weak interaction trees form an Elgot Freyd category. -/
@[reducible] noncomputable def elgotFreydCategory :
    ElgotFreydCategory (Kleisli.Adjunction.toKleisli (TM (Tree E))) := inferInstance

/-- The Freyd category is moreover strong. -/
@[reducible] noncomputable def strongElgotFreydCategory :
    StrongElgotFreydCategory (Kleisli.Adjunction.toKleisli (TM (Tree E))) := inferInstance

/-- The categorical contextual loop of lambda-iter agrees with tree iteration. -/
theorem contextualLoop_of {R A B : Type (u + 1)}
    (body : (Isotope.LambdaIter.Semantics.Categorical.typeJ (m := Tree E)).obj (R × A) ⟶
      (Isotope.LambdaIter.Semantics.Categorical.typeJ (m := Tree E)).obj (B ⨿ A : Type (u + 1)))
    (r : R) (a : A) :
    (Isotope.LambdaIter.Semantics.Categorical.contextualLoop
        (Isotope.LambdaIter.Semantics.Categorical.typeJ (m := Tree E)) body).of (r, a) =
      Isotope.Elgot.iter (m := Tree E) (fun a =>
        Isotope.Elgot.kcomp (m := Tree E) body.of (fun s =>
          (pure ((Types.binaryCoproductIso B A).hom s) : Tree E (B ⊕ A))) (r, a)) a :=
  Isotope.LambdaIter.Semantics.Categorical.contextualLoop_of (m := Tree E) body r a

/-- The universe obstruction to a set-valued lambda-iter model over `Tree E`:
event responses live in `Type u`, tree values in `Type (u+1)`, so a `vis`-built
instruction denotation returns a `ULift`ed response. -/
theorem interpObstruction {R : Type u} (e : E R) :
    (Isotope.Elgot.iter (m := Tree E)
        (fun _ : PUnit.{u + 2} =>
          (vis e (fun r => ret (Sum.inl (ULift.up r))) :
            Tree E (ULift.{u + 1} R ⊕ PUnit.{u + 2}))) PUnit.unit) =
      vis e (fun r => ret (ULift.up r)) := by
  rw [Isotope.Elgot.ITree.iterate_apply, vis_bind]
  refine congrArg (vis e) (funext fun r => ?_)
  change (pure (Sum.inl (ULift.up r)) : Tree E (ULift.{u + 1} R ⊕ PUnit.{u + 2})) >>= _ = _
  rw [pure_bind]
  rfl

end Isotope.Elgot.ITree
