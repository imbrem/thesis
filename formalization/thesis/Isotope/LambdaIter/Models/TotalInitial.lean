import Isotope.LambdaIter.Models.ReindexAlg
import Isotope.LambdaIter.Models.Initial
import Isotope.LambdaIter.Signature.Initial

/-!
# The quotiented syntax over the empty signature is the initial object

Three initiality statements are now available, and this file assembles them:

* **(a) fibrewise**, `Syn.isInitial` (`Models/Initial.lean`): for a fixed
  signature `S`, the quotiented syntax is the initial object of `Alg S`;
* **(b) globally**, `Total.synEmptyIsInitial` (here): the pair
  `(Sig.empty, Syn Sig.empty)` is the initial object of the total category of
  signatures and models;
* **(c) the fibre**, `Total.fibreEquiv` (`Models/Total.lean`): the morphisms of
  the total category lying over `𝟙 S` are exactly the morphisms of `Alg S`.

(b) is a *derivation*, not a fresh theorem.  It is the Grothendieck initiality
principle `Total.isInitialOfReindex` applied to `Sig.uniqueFromEmpty` (the
empty signature is initial) and to (a) at the reindexed model.  What made it
possible was the missing ingredient supplied by `Models/SigAction.lean` and
`Models/ReindexAlg.lean`: reindexing an *algebra*, which needs the action of a
signature morphism on typing and on `Eqv`.

## Honest boundary

"Model" still means *algebra of the equational presentation* — see
`Models/Alg.lean` and `Models/Initial.lean`.  So (b) reads: the quotiented
lambda-iter syntax over the empty signature is initial among pairs (signature,
algebra of the presentation over it).  It is **not** a statement about Freyd or
Elgot categories, and it does not become one; nothing in this repository
exhibits a Freyd category as such an algebra.
-/

namespace Isotope.LambdaIter

open LocallyNameless CategoryTheory

universe u

namespace Total

/-- The quotiented syntax over the empty signature, as an object of the total
category. -/
def synEmpty : Total.{u, u} where
  sig := Sig.empty
  alg := Syn Sig.empty

@[simp] theorem synEmpty_sig : (synEmpty.{u}).sig = Sig.empty := rfl
@[simp] theorem synEmpty_alg : (synEmpty.{u}).alg = Syn Sig.empty := rfl

/-- **Fibrewise initiality along a signature morphism.**  For every signature
`T`, every algebra `Y` over `T` and every signature morphism `g : S ⟶ T`, the
quotiented syntax over `S` admits a unique map of models into `Y` over `g`.

This is `Syn.uniqueHom` at the reindexed algebra, transported along the
universal property of reindexing. -/
noncomputable instance uniqueHomOver {S T : Sig.{u}} (g : S ⟶ T)
    (Y : Alg.{u, u} T) :
    Unique (Alg.HomOver (𝟙 S) (Syn S).toOps (Alg.Ops.reindex g Y.toOps)) :=
  (Alg.homOverIdEquiv (Syn S) (Alg.reindex g Y)).unique

/-- **The quotiented syntax over the empty signature is the initial object of
the total category of signatures and models.**

This is claim (b) of the fibred picture.  It is derived, not reproved: the
empty signature is initial among signatures (`Sig.uniqueFromEmpty`), the
quotiented syntax is initial in each fibre (`Syn.uniqueHom`), and
`Total.isInitialOfReindex` combines the two. -/
noncomputable def synEmptyIsInitial : Limits.IsInitial synEmpty.{u} :=
  isInitialOfReindex synEmpty
    (fun T => Sig.uniqueFromEmpty T)
    (fun Q g => uniqueHomOver g Q.alg)

noncomputable instance : Limits.HasInitial Total.{u, u} :=
  synEmptyIsInitial.hasInitial

/-- Restated: there is exactly one morphism from the quotiented empty-signature
syntax to any pair of a signature and a model over it. -/
noncomputable instance uniqueFromSynEmpty (Q : Total.{u, u}) :
    Unique (synEmpty.{u} ⟶ Q) :=
  ⟨⟨synEmptyIsInitial.to Q⟩, fun F => synEmptyIsInitial.hom_ext F _⟩

end Total

end Isotope.LambdaIter
