import Isotope.Elgot.ITree.Basic
import Isotope.Elgot.ITree.Shape
import Isotope.Elgot.ITree.Monad
import Isotope.Elgot.ITree.Iteration
import Isotope.Elgot.ITree.Laws
import Isotope.Elgot.ITree.Bisim
import Isotope.Elgot.ITree.Finality
import Isotope.Elgot.ITree.Examples
import Isotope.Elgot.ITree.Structural
import Isotope.Elgot.ITree.Handlers
import Isotope.Elgot.ITree.Freyd
import Isotope.Elgot.ITree.Events

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

## Finality

`ITree/Shape.lean` exhibits `Visible E A` in polynomial normal form —
a `Shape`, its `Visible.pos`itions, and the `Visible.child`ren at those
positions — and `ITree/Finality.lean` uses it to prove that the carrier is the
final coalgebra of the *visible-commitment* functor `Part ∘ Visible E A`:

* `Tree.destruct : Tree E A → Part (Visible E A (Tree E A))` is the structure
  map, inverse to `construct`; the isomorphism is `Tree.destructEquiv`;
* the universal property is `Tree.existsUnique_coalgebraHom`: every coalgebra
  `h : X → Part (Visible E A X)` admits a unique morphism into `Tree E A`,
  namely `corec h`, with `Tree.destruct_corec` and `Tree.corec_unique_destruct`
  as its two halves;
* Lambek's lemma is `Tree.corec_destruct : corec Tree.destruct = id`;
* the computation lemmas are `destruct_ret`, `destruct_vis`,
  `destruct_diverge`, `Tree.destruct_bind` (`ITree/Structural.lean`), together
  with the trichotomy `Tree.cases_three` and `Tree.destruct_eq_none_iff`;
* `Tree.eq_of_bisim` is the coinduction principle stated purely in terms of
  `destruct`, so tree equalities can be proved without touching `observe`.

Two structural facts drive the proof, both consequences of weakness: silence is
permanent (`Tree.dom_observe` — `Part.map` never changes `Dom`, so coherence
forces one domain at every depth, and `Part.none` means "no visible head, ever"
rather than "decide later"), and the head shape is already pinned at depth one
(`Tree.shape_get` — `Visible.map` cannot change shape).

`Tree.destruct` is a *computable* definition and the finality results are
choice-free: `#print axioms Tree.destructEquiv` reports `[propext, Quot.sound]`.
Only `Tree.cases_three` and the interpretation layer pull `Classical.choice`,
since they decide `Part.Dom`.

`ITree/Handlers.lean` puts the structure map to work: `translate` relabels
events along a signature morphism (computable, with `translate_ret`/`_diverge`/
`_vis`), and `interp` interprets a tree into an arbitrary `LawfulElgotMonad` by
iterating a head-exposing step, with `interp_ret` and `interp_vis`.

## Honest boundary

* The relation identified by equality of `Tree`s is *weak* bisimulation.
  Strong (tau-counting) bisimilarity is not expressible: there is no `Tau`
  constructor, so this module is the `eutt`-quotient of a Xia-style interaction
  tree library, not such a library itself.  That statement is a design fact
  argued in the docstrings, **not** an internal theorem: no tau-sensitive type
  of raw interaction trees is constructed here, so no quotient map from one is
  proved.  This is now the only gap of that kind in the module.
* `corec_unique` on its own does **not** give finality.  `corec_hyp_iff` shows
  its hypothesis is exactly the `construct`-fixpoint equation, i.e. that
  `(Tree E A, construct)` is a *corecursive algebra*; and
  `corecursive_not_lambek` exhibits a corecursive algebra whose structure map is
  not injective.  So `Tree.destruct` cannot be obtained from `corec_unique` by
  Lambek's lemma, and `ITree/Finality.lean` is a genuinely separate
  ω-continuity argument rather than a repackaging.
* Coalgebra carriers in `Tree.existsUnique_coalgebraHom` are restricted to
  `Type (u + 1)`.  A coalgebra on a smaller type has to be transported through
  `ULift` — the same universe tax already documented for the interpretation
  layer below and in `ITree/Freyd.lean`.
* Uniformity is proved only along *pure* maps `h : A → C`, as the
  `LawfulElgotMonad` class asks.  Uniformity along effectful Kleisli arrows is
  neither stated nor claimed.
* Event responses live in `Type u` while tree values live in `Type (u+1)`, so
  every interpretation layer pays a `ULift` (see `ITree/Freyd.lean` and the
  handler type in `ITree/Handlers.lean`).  No `Semantics.TypeModel` /
  `Semantics.InstructionModel` instance is supplied: only the categorical
  Kleisli/Freyd bridge is instantiated.
* `interp` is proved to compute on `ret` and `vis` only (`interp_ret`,
  `interp_vis`).  The monad-morphism law
  `interp h (t >>= k) = interp h t >>= interp h ∘ k`, and the corresponding
  `interp_iter`, are **not** proved here.  `translate`, by contrast, is complete:
  `translate_bind` (monad morphism) and `translate_id` / `translate_translate`
  (functoriality in the signature) are proved in `ITree/Handlers.lean`.
* There is no `sorry`, `admit`, `unsafe`, or new `axiom` anywhere in this
  development, and no law is postulated.
-/
