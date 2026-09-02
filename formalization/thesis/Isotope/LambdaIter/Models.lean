import Isotope.LambdaIter.Models.Alg
import Isotope.LambdaIter.Models.Limits
import Isotope.LambdaIter.Models.Examples
import Isotope.LambdaIter.Models.Setoid
import Isotope.LambdaIter.Models.Syntax
import Isotope.LambdaIter.Models.SynCategory
import Isotope.LambdaIter.Models.Initial

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
| `Models/SynCategory.lean` | the one-variable syntactic *category* (three category laws only) |
| `Models/Initial.lean` | `Syn.uniqueHom`, `Syn.isInitial`, and equational completeness |

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
* `Models/SynCategory.lean` proves the three *category* laws for the quotient
  and nothing else.  No premonoidal, coproduct, distributive or Elgot
  structure on the syntactic category is constructed, so issue #57's request
  for the syntactic Elgot model remains open; what is closed is the quotient,
  the category laws, the unique interpretation into every algebra, and
  completeness with respect to algebras.
-/
