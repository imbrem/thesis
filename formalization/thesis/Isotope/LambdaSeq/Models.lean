import Isotope.LambdaSeq.Models.Alg
import Isotope.LambdaSeq.Models.Limits
import Isotope.LambdaSeq.Models.Examples
import Isotope.LambdaSeq.Models.Setoid
import Isotope.LambdaSeq.Models.Syntax
import Isotope.LambdaSeq.Models.Initial
import Isotope.LambdaSeq.Models.Comparison
import Isotope.LambdaSeq.Models.SynCategory
import Isotope.LambdaSeq.Models.Monadic

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
| `Models/SynCategory.lean` | the one-variable syntactic category and its three
  category laws |

## What is proved

* `Syn.toHom` — **existence**: an interpretation `Syn S ⟶ X` for every model.
* `Syn.hom_eq_toHom` — **uniqueness**: every morphism `Syn S ⟶ X` is that one.
* `Syn.uniqueHom`, `Syn.isInitial` — `Syn S` is initial.
* `Syn.equiv_of_denote_eq` — **equational completeness with respect to
  algebras**.
* `Syn.SynCat.instCategory` — the one-variable syntactic category.
* `Alg.ofCaseFunctor`, `Syn.toCase_mk` — the restriction functor from
  lambda-case models, and the fact that the map it forces out of the initial
  lambda-seq model is the term embedding.

* `Alg.ofSeqModel` (`Models/Monadic/`) — **every lawful monad with an
  interpretation of the signature is an algebra**: the monadic denotation is
  coherent in the typing derivation (`denote_coh`) and sound for `Equiv`
  (`sound`).  Hypotheses: `[Monad m]`, `[LawfulMonad m]`; no iteration
  operator, no type former.  `Monadic/Examples.lean` instantiates it at the
  partiality monad and exhibits two terms it separates, so the model class is
  not merely the terminal algebra.

## Honest boundary

A model here is an algebra of the *presentation*.  It is **not** a Freyd
category, and nothing in this directory proves that a *Freyd* category gives
such an algebra.  What is proved is the monadic case: `Alg.ofSeqModel` turns a
lawful monad into an algebra, so `Syn.isInitial` is initiality among a class
that contains genuine semantic models.  It still says: initial *among algebras
of the equational presentation*.

The syntactic *category* of `Models/SynCategory.lean` carries exactly the three
category laws.  No monoidal, premonoidal or Freyd structure is built on it, and
none could be: lambda-seq has no type formers at all, so there is nothing to
make a tensor or a coproduct out of.

Its composition rests on `LocallyNameless.Equiv.rename` in
`Isotope/LambdaSeq/Metatheory/Renaming.lean`, which also supplies lambda-seq's
first typed renaming metatheory (`HasType.rename`, `.lift`, `.underBinder`).
-/
