import Isotope.LambdaSeq.Models.Alg
import Isotope.LambdaSeq.Models.Limits
import Isotope.LambdaSeq.Models.Examples
import Isotope.LambdaSeq.Models.Setoid
import Isotope.LambdaSeq.Models.Syntax
import Isotope.LambdaSeq.Models.Initial
import Isotope.LambdaSeq.Models.Comparison

/-!
# Models of lambda-seq, the category they form, and the initial one

`Alg S` is the category of algebras of the equational presentation of
lambda-seq over the signature `S : Isotope.LambdaIter.Sig`: a carrier indexed
by bound context and result type, three operations, and two propositional
obligations (coherence in the typing derivation, soundness for `Equiv`).

| file | content |
|---|---|
| `Models/Alg.lean` | `Alg.Ops`, `Alg.Ops.denote`, `Alg`, `Alg.Hom`,
  `Category (Alg S)`, `Alg.Hom.map_denote` |
| `Models/Limits.lean` | terminal model, binary products (with `IsLimit`), powers by a type |
| `Models/Examples.lean` | constant models, and morphisms that are not identities |
| `Models/Setoid.lean` | the syntactic setoid: typable terms modulo `Equiv` |
| `Models/Syntax.lean` | the syntactic model `Syn S : Alg S` |
| `Models/Initial.lean` | existence and uniqueness of the interpretation; completeness |
| `Models/Comparison.lean` | restriction of lambda-case models, and
  agreement with the term embedding |

## What is proved

* `Syn.toHom` — **existence**: an interpretation `Syn S ⟶ X` for every model.
* `Syn.hom_eq_toHom` — **uniqueness**: every morphism `Syn S ⟶ X` is that one.
* `Syn.uniqueHom`, `Syn.isInitial` — `Syn S` is initial.
* `Syn.equiv_of_denote_eq` — **equational completeness with respect to
  algebras**.
* `Alg.ofCaseFunctor`, `Syn.toCase_mk` — the restriction functor from
  lambda-case models, and the fact that the map it forces out of the initial
  lambda-seq model is the term embedding.

## Honest boundary

A model here is an algebra of the *presentation*.  It is **not** a Freyd
category, and nothing in this directory proves that a monad or a Freyd
category gives such an algebra; that would mean discharging `coh` and `sound`,
and this repository proves no soundness theorem for any lambda-seq denotation
with respect to `Equiv`.  `Syn.isInitial` says: initial *among algebras of the
equational presentation*.

The syntactic *category* (types as objects, one-variable terms as morphisms) is
not built here: composition in it needs stability of `Equiv` under typed
renaming, which lambda-seq does not have — it has no typed renaming metatheory
at all.  That is not needed for initiality.
-/
