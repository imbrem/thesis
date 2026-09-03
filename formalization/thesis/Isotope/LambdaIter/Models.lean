import Isotope.LambdaIter.Models.Alg
import Isotope.LambdaIter.Models.Limits
import Isotope.LambdaIter.Models.Examples
import Isotope.LambdaIter.Models.Setoid
import Isotope.LambdaIter.Models.Syntax
import Isotope.LambdaIter.Models.SynCategory
import Isotope.LambdaIter.Models.SynCoproduct
import Isotope.LambdaIter.Models.SynIteration
import Isotope.LambdaIter.Models.SynUniformity
import Isotope.LambdaIter.Models.SynElgot
import Isotope.LambdaIter.Models.Initial
import Isotope.LambdaIter.Models.HomOver
import Isotope.LambdaIter.Models.Total
import Isotope.LambdaIter.Models.Reindex
import Isotope.LambdaIter.Models.SigAction
import Isotope.LambdaIter.Models.ReindexAlg
import Isotope.LambdaIter.Models.TotalInitial
import Isotope.LambdaIter.Models.Monadic

/-!
# Models of lambda-iter, and the category they form

`Alg S` is the category of algebras of the equational presentation of
lambda-iter over the signature `S`: a carrier indexed by bound context and
result type, one operation per term former, and two propositional obligations
(coherence in the typing derivation, soundness for `Eqv`).

| file | content |
|---|---|
| `Models/Alg.lean` | `Alg.Ops`, `Alg`, `Alg.Hom`, `Category (Alg S)`, `Hom.map_denote` |
| `Models/Limits.lean` | terminal model, binary products (with `IsLimit`), powers by a type |
| `Models/Examples.lean` | constant models, and morphisms that are not identities |
| `Models/Setoid.lean` | the setoid `Eqv` induces on typable terms, and its quotient |
| `Models/Syntax.lean` | `Syn S : Alg S`, the quotient as a model; `Syn.denote_mk` |
| `Models/SynCategory.lean` | the one-variable syntactic *category* (three category laws) |
| `Models/SynCoproduct.lean` | binary coproducts in it; iteration on hom-sets |
| `Models/SynIteration.lean` | fixpoint, naturality and codiagonal for it |
| `Models/SynUniformity.lean` | pure morphisms as a wide subcategory; uniformity |
| `Models/SynElgot.lean` | those three in Mathlib's `⨿`; `ElgotCategory` modulo an initial object |
| `Models/Initial.lean` | `Syn.uniqueHom`, `Syn.isInitial`, equational completeness |
| `Models/HomOver.lean` | maps of models over a signature morphism; identity, composition |
| `Models/Total.lean` | the total category of pairs `(signature, model)`, the fibre |
| | inclusion, and the Grothendieck initiality principle |
| `Models/Reindex.lean` | reindexing of operations along a signature morphism, with |
| | its universal property and its functoriality |
| `Models/SigAction.lean` | `HasType.map`, `Eqv.map`: the action on typing and on `Eqv` |
| `Models/ReindexAlg.lean` | `Alg.reindex`, via `Alg.Ops.reindex_denote` |
| `Models/TotalInitial.lean` | `(Sig.empty, Syn Sig.empty)` is initial in the total category |
| `Models/Monadic/` | the monadic bridge: `Alg.ofModel` turns any lawful Elgot |
| | monad with an interpretation of the signature into an algebra |

## The monadic bridge

`Models/Monadic/` closes what used to be the central gap of this directory:
`Alg.ofModel` builds an algebra from any monad `m` with `[LawfulMonad m]`,
`[Iterate m]`, `[LawfulElgotMonad m]` together with a set-valued
interpretation of the signature's types (`Monadic.Model`), assuming the two
binary type formers are injective and disjoint (`InjectiveFormers`).  Both
propositional fields are discharged:

* `sound` — the four Elgot laws are used one per iteration axiom, and
  `Eqv.ax`'s raw axiom schemes are handled by inverting one endpoint's
  derivation and building the other's.
* `coh` — a coupling (parametricity) argument.  Lambda-iter typing is *not*
  unique, and the naive statement ("derivations at different types agree after
  any continuation") is false; `Monadic/Coupling.lean` says instead that the
  two denotations are projections of a single computation over related pairs,
  which for `iter` needs Elgot naturality and uniformity.

`Monadic/Examples.lean` instantiates this at `Part` over the empty signature
and separates a divergent loop from a value, so the algebra is not terminal
and the equational theory provably does not identify them.

## Honest boundary

* A model here is an algebra of the *presentation*.  It is **not** a Freyd or
  Elgot category, and nothing in this directory proves that a *Freyd* category
  gives such an algebra; that is still the work the two coherence classes
  (`Semantics.Categorical.TypingCoherent` and `.LawfulModel`) represent.  The
  monadic case is proved.
* Apart from the syntactic model `Syn S` and the monadic algebras, every
  algebra constructed here is terminal, constant, or built from those by
  products and powers.
* Initiality (`Models/Initial.lean`) is initiality **in `Alg S`**, that is,
  among algebras of the presentation — a class that now provably contains the
  monadic models, so the statement has semantic content.  Likewise
  `Syn.eqv_of_denote_eq` is completeness with respect to algebras.  Neither
  may be restated as initiality or completeness for Freyd/Elgot *categories*:
  that would still require an `Alg` built from a Freyd category.
* The syntactic category (`Models/SynCategory.lean`, `Models/SynCoproduct.lean`)
  is proved to be a category with binary coproducts, and its iteration
  operator is proved well defined on classes and to satisfy the **fixpoint,
  naturality and codiagonal** laws — verbatim the three fields of
  `CategoryTheory.ElgotCategory`; `Models/SynElgot.lean` checks that
  correspondence rather than asserting it, and proves
  `ElgotCategory (SynCat S)` **under the hypothesis**
  `HasFiniteCoproducts (SynCat S)`.  That instance is nevertheless **not**
  registered, because the hypothesis is not known to hold: it needs an initial
  object, and the empty type is not shown to be one (see
  `Models/SynCoproduct.lean`).  **No strength, and no premonoidal, monoidal or
  distributive structure, is proved**, so the syntactic category is not shown
  to be a Freyd or Elgot Freyd category.  Issue #57's request for the
  syntactic Elgot model therefore remains open; what is closed is the
  quotient, the category and coproduct laws, well-definedness of iteration,
  the four equational Elgot laws, the unique interpretation into every algebra,
  and completeness with respect to algebras.
* Reindexing is available at both levels: `Alg.Ops.reindex` on operations
  (`Models/Reindex.lean`) and `Alg.reindex` on algebras
  (`Models/ReindexAlg.lean`), the latter through the action of a signature
  morphism on typing and on `Eqv` (`Models/SigAction.lean`).  With it, all
  three initiality statements of the fibred picture hold: fibrewise
  (`Syn.isInitial`), globally (`Total.synEmptyIsInitial`), and the fibre
  description (`Total.fibreEquiv`, near-tautological by construction — see its
  docstring).  All of them are statements about **algebras of the
  presentation**, never about Freyd or Elgot categories.
-/
