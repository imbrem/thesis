import Isotope.Elgot.ITree.Examples
import Isotope.LambdaIter.Subtyping.Semantics.Agreement.Iteration

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
which no model in this repository currently supplies for any monad.

There is a model-specific obstruction to writing one, but it is **documented,
not proved**, and it is not provable here: an event signature
`E : Type u → Type u` has responses in `Type u`, whereas `Tree E` only accepts
value types in `Type (u+1)`, so `Tree E R` is not even a well-formed expression
for `R : Type u` and every `vis`-built instruction denotation must return a
`ULift`ed response.  That is a statement about which Lean expressions typecheck,
not a proposition about terms, so no theorem in this file asserts it; the
evidence is the elaborated type of `trigger`, namely
`trigger : E R → Tree E (ULift.{u+1} R)`.  `iterate_vis_exit` and
`iterate_trigger` below are ordinary computation lemmas about iteration; they
exhibit the `ULift` in a concrete denotation but claim no impossibility.
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
    (body : (Isotope.LambdaIter.Subtyping.Semantics.Categorical.typeJ (m := Tree E)).obj (R × A) ⟶
      (Isotope.LambdaIter.Subtyping.Semantics.Categorical.typeJ (m := Tree E)).obj (B ⨿ A : Type (u + 1)))
    (r : R) (a : A) :
    (Isotope.LambdaIter.Subtyping.Semantics.Categorical.contextualLoop
        (Isotope.LambdaIter.Subtyping.Semantics.Categorical.typeJ (m := Tree E)) body).of (r, a) =
      Isotope.Elgot.iter (m := Tree E) (fun a =>
        Isotope.Elgot.kcomp (m := Tree E) body.of (fun s =>
          (pure ((Types.binaryCoproductIso B A).hom s) : Tree E (B ⊕ A))) (r, a)) a :=
  Isotope.LambdaIter.Subtyping.Semantics.Categorical.contextualLoop_of (m := Tree E) body r a

/-- Iterating a body that performs one visible event and then exits performs
the event exactly once. -/
theorem iterate_vis_exit {A : Type (u + 1)} {R : Type u} (e : E R) (k : R → A) :
    (Isotope.Elgot.iter (m := Tree E)
        (fun _ : PUnit.{u + 2} =>
          (vis e (fun r => ret (Sum.inl (k r))) : Tree E (A ⊕ PUnit.{u + 2})))
      PUnit.unit) = vis e (fun r => ret (k r)) := by
  rw [Isotope.Elgot.ITree.iterate_apply, vis_bind]
  refine congrArg (vis e) (funext fun r => ?_)
  change (pure (Sum.inl (k r)) : Tree E (A ⊕ PUnit.{u + 2})) >>= _ = _
  rw [pure_bind]
  rfl

/-- The same computation for `trigger`, the canonical one-event denotation.
Its value type is `ULift.{u+1} R`: this *displays* the universe tax paid by any
`vis`-built instruction denotation, and does not prove that the tax is
unavoidable — see the honest boundary above. -/
theorem iterate_trigger {R : Type u} (e : E R) :
    (Isotope.Elgot.iter (m := Tree E)
        (fun _ : PUnit.{u + 2} =>
          (vis e (fun r => ret (Sum.inl (ULift.up r))) :
            Tree E (ULift.{u + 1} R ⊕ PUnit.{u + 2}))) PUnit.unit) =
      trigger e :=
  iterate_vis_exit E e ULift.up

end Isotope.Elgot.ITree
