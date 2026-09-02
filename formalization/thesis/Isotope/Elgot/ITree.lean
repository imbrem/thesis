import Isotope.Elgot.ITree.Basic
import Isotope.Elgot.ITree.Shape
import Isotope.Elgot.ITree.Monad
import Isotope.Elgot.ITree.Iteration
import Isotope.Elgot.ITree.Laws
import Isotope.Elgot.ITree.Bisim
import Isotope.Elgot.ITree.Finality
import Isotope.Elgot.ITree.Examples
import Isotope.Elgot.ITree.Structural
import Isotope.Elgot.ITree.Raw
import Isotope.Elgot.ITree.Handlers
import Isotope.Elgot.ITree.Events
import Isotope.Elgot.ITree.Refinement
import Isotope.Elgot.ITree.Relation
import Isotope.Elgot.ITree.Combinators
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
* the computation lemmas are `destruct_ret`, `destruct_vis`, `destruct_diverge`,
  together with the trichotomy `Tree.cases_three`, the inversions
  `Tree.eq_ret_of_destruct` / `Tree.eq_vis_of_destruct`, and
  `Tree.destruct_eq_none_iff`;
* `Tree.eq_of_bisim` is coinduction stated in terms of `destruct`, and
  `Tree.eq_of_bisim'` is its transport-free trichotomy form, which is what
  downstream proofs use.  Tree equalities can now be proved without touching
  `observe`.

Two structural facts drive the proof, both consequences of weakness: silence is
permanent (`Tree.dom_observe` — `Part.map` never changes `Dom`, so coherence
forces one domain at every depth, and `Part.none` means "no visible head, ever"
rather than "decide later"), and the head shape is already pinned at depth one
(`Tree.shape_get` — `Visible.map` cannot change shape).

`Tree.destruct` is a *computable* definition and the finality results are
choice-free: `#print axioms Tree.destructEquiv` reports `[propext, Quot.sound]`.
Only `Tree.cases_three` and the interpretation layer pull `Classical.choice`,
since they decide `Part.Dom`.

## The layers built on finality

* `ITree/Structural.lean` restates the monad and iteration structure at the head
  level: `Tree.destruct_bind`, `Tree.destruct_map` and `Tree.destruct_iterate`
  (the Elgot fixpoint law in head form), plus the `map` computation lemmas.
* `ITree/Handlers.lean` defines `translate φ`, which relabels events along a
  signature morphism — computable, functorial (`translate_id`,
  `translate_translate`) and a monad morphism (`translate_bind`) — and `interp`,
  which interprets a tree into an arbitrary `LawfulElgotMonad` by iterating a
  head-exposing step.  Proved for `interp`: `interp_ret`, `interp_vis`,
  `interp_trigger`, `interp_diverge` (divergence goes to `divergent M`, the
  target's own divergent element), `interp_map` and `interp_translate`.
* `ITree/Events.lean` is the signature algebra: the coproduct `Sum1 E F` with
  `Sum1.case1`, the `Subevent` class with its three instances, `send` for
  raising a whole tree, and the `translate_case1_*` computation lemmas.  Without
  this, handlers do not compose.
* `ITree/Refinement.lean` develops divergence refinement `Refines`, the greatest
  post-fixed point of `RefinesStep`: a partial order (`Tree.partialOrder`) with
  `diverge` least, congruent for `vis`, `bind`, `map` and `translate`.
  Antisymmetry is where finality earns its keep — it runs through
  `Tree.eq_of_bisim'`.
* `ITree/Relation.lean` generalises both `Bisim` and `Refines` to heterogeneous
  lifting `Tree.Rel RA`, this carrier's `eutt`, with `Tree.rel_eq_iff` showing
  `Tree.Rel Eq` is equality.
* `ITree/Combinators.lean` adds `forever` and worked examples that only the
  head-level API makes expressible.

## Honest boundary

* The relation identified by equality of `Tree`s is *weak* bisimulation.
  Strong (tau-counting) bisimilarity is not expressible on `Tree`: there is no
  `Tau` constructor, so this module is the `eutt`-quotient of a Xia-style
  interaction tree library.  That is now a **theorem**, not a docstring claim:
  `ITree/Raw.lean` builds the tau-sensitive carrier `Raw E A` over the extended
  signature `Sum1 E TauEv`, in which silent steps are observable
  (`silent_ret_ne`, `spin_ne_diverge'`), and
  `rawQuotientEquiv : Quotient (weakSetoid E A) ≃ Tree E A` exhibits `Tree` as
  its weak-bisimulation quotient, with `weak_iff_bisim` identifying the two
  relations.  `Raw` is a witness carrier for that statement, not a full
  tau-sensitive library: `eq_itree`, `euttge`, the `eqit` hierarchy, `burn`,
  and up-to-tau/paco infrastructure are deliberately absent.
* `corec_unique` on its own does **not** give finality.  `corec_hyp_iff` shows
  its hypothesis is exactly the `construct`-fixpoint equation, i.e. that
  `(Tree E A, construct)` is a *corecursive algebra*; and
  `corecursive_not_lambek` exhibits a corecursive algebra whose structure map is
  not injective.  So `Tree.destruct` cannot be obtained from `corec_unique` by
  Lambek's lemma, and `ITree/Finality.lean` is a genuinely separate
  ω-continuity argument rather than a repackaging.
* Coalgebra carriers in `Tree.existsUnique_coalgebraHom` are restricted to
  `Type (u + 1)`.  A coalgebra on a smaller type has to be transported through
  `ULift` — the same universe tax as below.
* Uniformity is proved only along *pure* maps `h : A → C`, as the
  `LawfulElgotMonad` class asks.  Uniformity along effectful Kleisli arrows is
  neither stated nor claimed.
* Consequently the monad-morphism law for `interp`, namely
  `interp h (t >>= k) = interp h t >>= interp h ∘ k`, is **not** proved, and not
  for want of trying: interpreting `t >>= k` at a return head of `t` takes one
  step where the composite takes two, so no *lock-step* simulation square
  relates the two iterations, and pure uniformity is exactly a lock-step
  principle.  Closing it needs dinaturality (equivalently a Bekić/pairing law),
  which is not one of the four `LawfulElgotMonad` axioms and is not derived
  anywhere in this repository.  `interp_map`, `interp_translate` and
  `interp_diverge` are the cases where the square *is* lock-step, and those are
  proved.  `interp_iter`, and `interp (fun _ e => trigger e) = id`, are likewise
  open here.
* `Refines` is proved to be a congruence for `vis`, `bind`, `map` and
  `translate`, but **not** for `Isotope.Elgot.iter`: establishing one refinement
  step for a loop can require unboundedly many unfoldings of the body, which the
  one-step `RefinesStep` does not see.
* Event responses live in `Type u` while tree values live in `Type (u+1)`, so
  every interpretation layer pays a `ULift` (see `ITree/Freyd.lean` and the
  handler type in `ITree/Handlers.lean`).  No `Semantics.TypeModel` /
  `Semantics.InstructionModel` instance is supplied: only the categorical
  Kleisli/Freyd bridge is instantiated.
* The `Part ∘ Visible E A` endofunctor is not packaged as a
  `CategoryTheory.Functor`, and finality is not restated as `IsTerminal` in its
  category of coalgebras; `Tree.existsUnique_coalgebraHom` carries the
  mathematical content in elementary form.
* There is no `sorry`, `admit`, `unsafe`, or new `axiom` anywhere in this
  development, and no law is postulated.
-/
