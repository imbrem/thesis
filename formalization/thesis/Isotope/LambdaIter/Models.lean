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

/-!
# Models of lambda-iter, and the category they form

`Alg S` is the category of algebras of the equational presentation of
lambda-iter over the signature `S`: a carrier indexed by bound context and
result type, one operation per term former, and two propositional obligations
(coherence in the typing derivation, soundness for `Eqv`).

| file | content |
|---|---|
| `Models/Alg.lean` | `Alg.Ops`, `Alg.Ops.denote`, `Alg`, `Alg.Hom`, `Category (Alg S)`, `Alg.Hom.map_denote` |
| `Models/Limits.lean` | terminal model, binary products (with `IsLimit`), powers by a type |
| `Models/Examples.lean` | constant models, and morphisms that are not identities |
| `Models/Setoid.lean` | the setoid `Eqv` induces on typable terms, and its quotient |
| `Models/Syntax.lean` | `Syn S : Alg S`, the quotiented syntax as a model, and `Syn.denote_mk` |
| `Models/SynCategory.lean` | the one-variable syntactic *category* (three category laws) |
| `Models/SynCoproduct.lean` | binary coproducts in it, and iteration on hom-sets |
| `Models/SynIteration.lean` | the fixpoint, naturality and codiagonal laws for it |
| `Models/SynUniformity.lean` | pure morphisms as a wide subcategory, and the uniformity law |
| `Models/SynElgot.lean` | those three laws in Mathlib's `⨿` vocabulary, and `ElgotCategory` modulo an initial object |
| `Models/Initial.lean` | `Syn.uniqueHom`, `Syn.isInitial`, and equational completeness |
| `Models/HomOver.lean` | maps of models over a signature morphism; identity and composition |
| `Models/Total.lean` | the total category of pairs `(signature, model)`, the fibre inclusion, and the Grothendieck initiality principle |
| `Models/Reindex.lean` | reindexing of operations along a signature morphism, its universal property and its functoriality |
| `Models/SigAction.lean` | `HasType.map` and `Eqv.map`: a signature morphism acts on typing and on the equational theory |
| `Models/ReindexAlg.lean` | `Alg.reindex`, reindexing an *algebra*, via `Alg.Ops.reindex_denote` |
| `Models/TotalInitial.lean` | `(Sig.empty, Syn Sig.empty)` is the initial object of the total category |

## Honest boundary

* A model here is an algebra of the *presentation*.  It is **not** a Freyd or
  Elgot category, and nothing in this directory proves that a monad or a Freyd
  category gives such an algebra.  Doing so means discharging the fields `coh`
  and `sound`, which are exactly the two coherence classes
  (`Semantics.Categorical.TypingCoherent` and `.LawfulModel`) that have no
  instance anywhere in this repository.
* Apart from the syntactic model `Syn S`, every algebra constructed here is
  terminal, constant, or built from those by products and powers; none has
  semantic content.  `Syn S` does distinguish `Eqv`-inequivalent terms — by
  construction, since it *is* the quotient — which is what makes the
  completeness corollary non-vacuous.  Whether an algebra with genuinely
  semantic content (a monad, a Freyd category) exists is still open.
* Initiality (`Models/Initial.lean`) is initiality **in `Alg S`**, that is,
  among algebras of the presentation.  Likewise `Syn.eqv_of_denote_eq` is
  completeness with respect to algebras.  Neither may be restated as
  initiality or completeness for Freyd/Elgot models: that would require an
  `Alg` built from a Freyd category, which needs exactly the two missing
  coherence instances above.
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
