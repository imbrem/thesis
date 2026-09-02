import Isotope.CategoryTheory.AddMonoidal.Elgot
import Isotope.Elgot.Nondet.Powerset
import Isotope.Elgot.ITree
import Isotope.Elgot.Trace
import Isotope.Elgot.Transformer.State
import Isotope.Elgot.Transformer.Writer

/-!
# Chosen coproducts and Elgot structure for the concrete monads

Instantiations of `Isotope.CategoryTheory.AddMonoidal.Kleisli` and
`Isotope.CategoryTheory.AddMonoidal.Elgot` at the monads formalized elsewhere in the
development.  Nothing here needs a proof: every instance is found by `inferInstance` from the
generic construction, which is the point — the chosen coproduct on a Kleisli category is
inherited from `Type u` for *any* monad, and the Elgot structure for *any* complete Elgot monad.
-/

universe u

namespace CategoryTheory.AddMonoidal.Examples

open CategoryTheory CategoryTheory.Kleisli.Type Isotope.Elgot
open scoped AddMonoidalCategory

/-! ### Any monad on `Type u` has a chosen coproduct on its Kleisli category -/

example : CocartesianMonoidalCategory (Kleisli (TM _root_.Part.{u})) := inferInstance
example : CocartesianMonoidalCategory (Kleisli (TM SetM.{u})) := inferInstance
example : CocartesianMonoidalCategory (Kleisli (TM Option.{u})) := inferInstance
example (E : Type u → Type u) :
    CocartesianMonoidalCategory (Kleisli (TM (ITree.Tree.{u} E))) := inferInstance
example (S : Type u) :
    CocartesianMonoidalCategory (Kleisli (TM (StateT.{u, u} S _root_.Part.{u}))) := inferInstance

/-! ### Every complete Elgot monad gives Elgot structure over that chosen coproduct -/

example : AddElgotCategory (Kleisli (TM _root_.Part.{u})) := inferInstance
example : AddElgotCategory (Kleisli (TM SetM.{u})) := inferInstance
example (E : Type u → Type u) :
    AddElgotCategory (Kleisli (TM (ITree.Tree.{u} E))) := inferInstance
example (Sigma : Type u) :
    AddElgotCategory (Kleisli (TM (FiniteTrace Sigma))) := inferInstance
example (S : Type u) :
    AddElgotCategory (Kleisli (TM (StateT.{u, u} S _root_.Part.{u}))) := inferInstance

/-! ### The structure computes

For `Part`, the chosen coproduct is `Sum` and the iteration operator is the monad's own `iter`,
with no comparison isomorphism interposed. -/

example (X Y : Kleisli (TM _root_.Part.{u})) : (X ⊕ₘ Y).of = (X.of ⊕ Y.of) := rfl

example (X Y : Kleisli (TM _root_.Part.{u})) (x : X.of) :
    (CocartesianMonoidalCategory.inl X Y).of x =
      (pure (Sum.inl x) : _root_.Part (X.of ⊕ Y.of)) := rfl

example {X Y : Kleisli (TM _root_.Part.{u})} (f : X ⟶ Y ⊕ₘ X) :
    (addIterate f).of =
      ((Isotope.Elgot.iter (f.of : X.of → _root_.Part (Y.of ⊕ X.of))) :
        X.of → _root_.Part Y.of) := rfl

end CategoryTheory.AddMonoidal.Examples
