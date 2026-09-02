import Isotope.LambdaIter.Models.Alg
import Isotope.LambdaIter.Models.Limits
import Isotope.LambdaIter.Models.Examples
import Isotope.LambdaIter.Models.HomOver
import Isotope.LambdaIter.Models.Total
import Isotope.LambdaIter.Models.Reindex

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
| `Models/HomOver.lean` | maps of models over a signature morphism; identity and composition |
| `Models/Total.lean` | the total category of pairs `(signature, model)`, the fibre inclusion, and the Grothendieck initiality principle |
| `Models/Reindex.lean` | reindexing of operations along a signature morphism, its universal property and its functoriality |

## Honest boundary

* A model here is an algebra of the *presentation*.  It is **not** a Freyd or
  Elgot category, and nothing in this directory proves that a monad or a Freyd
  category gives such an algebra.  Doing so means discharging the fields `coh`
  and `sound`, which are exactly the two coherence classes
  (`Semantics.Categorical.TypingCoherent` and `.LawfulModel`) that have no
  instance anywhere in this repository.
* Consequently every algebra constructed here is either terminal, constant, or
  built from those by products and powers.  None has semantic content, and the
  question of whether an algebra distinguishing two `Eqv`-inequivalent terms
  exists is left open — that is precisely the content of a syntactic model.
* No initiality statement is made here.  This directory supplies the *category*
  in which such a statement would live, together with
  `Total.isInitialOfFibrewise` and `Total.isInitialOfReindex`, which say what
  a construction of the quotiented syntax would have to supply.
* Reindexing along a signature morphism is built at the level of `Alg.Ops`,
  the *operations* of a model, not of `Alg`: promoting it to algebras needs
  the functorial action of a signature morphism on the syntax and on `Eqv`
  (`Tm.map`, `HasType.map`, `Eqv.map` and their commutation with `rename`,
  `bsubst` and `instantiate`), which is **not** built here.  See the honest
  boundary in `Models/Reindex.lean`.
-/
