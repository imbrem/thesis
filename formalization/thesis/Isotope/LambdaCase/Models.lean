import Isotope.LambdaCase.Models.Alg
import Isotope.LambdaCase.Models.Limits
import Isotope.LambdaCase.Models.Examples
import Isotope.LambdaCase.Models.Setoid
import Isotope.LambdaCase.Models.Syntax
import Isotope.LambdaCase.Models.Initial

/-!
# Models of lambda-case, the category they form, and the initial one

`Alg S` is the category of algebras of the equational presentation of
lambda-case over the signature `S`: a carrier indexed by bound context and
result type, one operation per term former, and two propositional obligations
(coherence in the typing derivation, soundness for `Equiv`).  The signature
`S : Isotope.LambdaIter.Sig` is shared with lambda-iter, since its components
are exactly the parameters lambda-case's judgments take.

| file | content |
|---|---|
| `Models/Alg.lean` | `Alg.Ops`, `Alg.Ops.denote`, `Alg`, `Alg.Hom`, `Category (Alg S)`, `Alg.Hom.map_denote` |
| `Models/Limits.lean` | terminal model, binary products (with `IsLimit`), powers by a type |
| `Models/Examples.lean` | constant models, and morphisms that are not identities |
| `Models/Setoid.lean` | the syntactic setoid: typable terms modulo `Equiv` |
| `Models/Syntax.lean` | the syntactic model `Syn S : Alg S` |
| `Models/Initial.lean` | existence and uniqueness of the interpretation; completeness |

## What is proved

* `Syn.toHom` — **existence**: an interpretation `Syn S ⟶ X` for every model
  `X`.
* `Syn.hom_eq_toHom` — **uniqueness**: every morphism `Syn S ⟶ X` is that one.
* `Syn.uniqueHom`, `Syn.isInitial` — the two together: `Syn S` is initial.
* `Syn.equiv_of_denote_eq` — **equational completeness with respect to
  algebras**, the corollary.

## Honest boundary

* A model here is an algebra of the *presentation*.  It is **not** a Freyd
  category, and nothing in this directory proves that a monad or a Freyd
  category gives such an algebra.  Doing so means discharging the fields `coh`
  and `sound`, which are exactly the coherence and lawfulness conditions that
  have no instance anywhere in this repository.  In particular there is still
  no theorem in this repository saying that the monadic or categorical
  denotation of lambda-case respects `Equiv`.
* `Syn.isInitial` therefore says: initial *among algebras of the equational
  presentation*.  It does not say initial among Freyd categories, and it must
  not be restated that way.
* The syntactic *category* (types as objects, one-variable terms as morphisms)
  is **not** built here.  Composition in it would need stability of `Equiv`
  under typed renaming, which lambda-case does not have: unlike lambda-iter,
  lambda-case does not factor its axioms through a raw axiom relation, so every
  one of its fifteen axioms carries its own typing witnesses that a renaming
  would have to rebuild.  That is a separate piece of metatheory, and it is not
  needed for initiality.
* The empty type is likewise not exhibited as an initial object of any
  syntactic category: `Equiv.emptyInitial` fires only when the scrutinee of a
  `let` is literally of the form `.abort a`, so it does not prove
  `bv 0 ≈ abort (bv 0)` at the empty type.  This is a gap in the presentation
  rather than a proof of non-derivability — no separating model is built here.
-/
