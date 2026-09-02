import Isotope.Elgot.ITree.Basic
import Isotope.Elgot.ITree.Monad
import Isotope.Elgot.ITree.Iteration
import Isotope.Elgot.ITree.Laws
import Isotope.Elgot.ITree.Bisim
import Isotope.Elgot.ITree.Examples
import Isotope.Elgot.ITree.Freyd

/-!
# Weak interaction trees as a complete Elgot monad

An interaction tree is presented by the coherent family of all of its finite
observations (`ITree/Basic.lean`).  Between two visible nodes observation is
partial: `Part.none` is silent divergence, `Part.some` exposes either a return
or a visible event.  Depth is charged only at visible events, so returns are
free and finite silent delays are not representable: `tau` is definitionally
the identity.

The three layers demanded by a weak-bisimulation presentation are kept apart:

* **raw, guarded**: `Tree.corec` unfolds an arbitrary `Part ∘ Visible E A`
  coalgebra, and `corec_unique` is the accompanying coinduction principle
  (`ITree/Basic.lean`);
* **relation**: `Bisim x y := ∀ n, x.observe n = y.observe n`, with its
  `Setoid` and congruence lemmas for `bind`, `vis`, `iter` and `corec`
  (`ITree/Bisim.lean`);
* **quotient**: the carrier `Tree E A` itself.  `bisim_iff_eq` shows `Bisim` is
  propositional equality here, and `quotientEquiv` exhibits
  `Quotient (setoid E A) ≃ Tree E A`.  Hence the Elgot equations hold as
  *equalities* on the quotient carrier and no further quotienting is needed.

`ITree/Monad.lean` proves `LawfulMonad (Tree E)`; `ITree/Iteration.lean` defines
the productive iteration operator; `ITree/Laws.lean` proves all four
Conway/complete-Elgot equations — fixpoint, naturality, codiagonal and pure
uniformity — and installs `LawfulElgotMonad (Tree E)`.  `ITree/Examples.lean`
and `ITree/Freyd.lean` exercise the model and instantiate the Kleisli/Freyd
bridge.

## Honest boundary

* The relation identified by equality of `Tree`s is *weak* bisimulation.
  Strong (tau-counting) bisimilarity is not expressible: there is no `Tau`
  constructor, so this module is the `eutt`-quotient of a Xia-style interaction
  tree library, not such a library itself.  That statement is a design fact
  argued in the docstrings, **not** an internal theorem: no tau-sensitive type
  of raw interaction trees is constructed here, so no quotient map from one is
  proved.
* `Tree E A ≅ Part (Visible E A (Tree E A))` (finality of the coalgebra) is
  *not* proved.  `corec` and `corec_unique` give the universal property in the
  direction needed for guarded definitions; `Tree.destruct` and the inverse
  isomorphism are absent.
* Uniformity is proved only along *pure* maps `h : A → C`, as the
  `LawfulElgotMonad` class asks.  Uniformity along effectful Kleisli arrows is
  neither stated nor claimed.
* Event responses live in `Type u` while tree values live in `Type (u+1)`, so
  every interpretation layer pays a `ULift` (see `ITree/Freyd.lean`).  No
  `Semantics.TypeModel` / `Semantics.InstructionModel` instance is supplied:
  only the categorical Kleisli/Freyd bridge is instantiated.
* There is no `sorry`, `admit`, `unsafe`, or new `axiom` anywhere in this
  development, and no law is postulated.
-/
