import Isotope.LambdaCase.Models.Alg
import Isotope.LambdaCase.Models.Limits
import Isotope.LambdaCase.Models.Examples
import Isotope.LambdaCase.Models.Setoid
import Isotope.LambdaCase.Models.Syntax
import Isotope.LambdaCase.Models.Initial
import Isotope.LambdaCase.Models.CompareIter
import Isotope.LambdaCase.Models.SynCategory
import Isotope.LambdaCase.Models.SynCoproduct
import Isotope.LambdaCase.Models.Monadic

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
| `Models/Alg.lean` | `Alg.Ops`, `Alg.Ops.denote`, `Alg`, `Alg.Hom`,
  `Category (Alg S)`, `Alg.Hom.map_denote` |
| `Models/Limits.lean` | terminal model, binary products (with `IsLimit`), powers by a type |
| `Models/Examples.lean` | constant models, and morphisms that are not identities |
| `Models/Setoid.lean` | the syntactic setoid: typable terms modulo `Equiv` |
| `Models/Syntax.lean` | the syntactic model `Syn S : Alg S` |
| `Models/Initial.lean` | existence and uniqueness of the interpretation; completeness |
| `Models/CompareIter.lean` | restriction of lambda-iter models, and
  agreement with the term embedding |
| `Models/SynCategory.lean` | the one-variable syntactic category and its three
  category laws |
| `Models/SynCoproduct.lean` | binary coproducts in that category, with the
  full universal property |

## What is proved

* `Syn.toHom` — **existence**: an interpretation `Syn S ⟶ X` for every model
  `X`.
* `Syn.hom_eq_toHom` — **uniqueness**: every morphism `Syn S ⟶ X` is that one.
* `Syn.uniqueHom`, `Syn.isInitial` — the two together: `Syn S` is initial.
* `Syn.equiv_of_denote_eq` — **equational completeness with respect to
  algebras**, the corollary.
* `Syn.SynCat.instCategory` — the one-variable syntactic category, whose
  composition is well defined because of
  `LocallyNameless.Equiv.rename` in `Metatheory/EquivSubst.lean`; and
  `Syn.SynCat.hasBinaryCoproducts` — the object-language coproduct really is a
  coproduct there.
* `Alg.ofIterFunctor`, `Syn.toIter_mk` — the restriction functor from
  lambda-iter models, and the fact that the map initiality forces out of the
  lambda-case syntactic model computes the lambda-iter denotation of the
  embedded term.  This rests on
  `LocallyNameless.Equiv.embedIter` in `Metatheory/EmbedIter.lean`, the
  stability of the lambda-case theory under the inclusion into lambda-iter that
  `Equiv.lean` had left deferred.

* `Alg.ofModel` (`Models/Monadic/`) — **every lawful monad with an
  interpretation of the signature is an algebra**.  Soundness for `Equiv` is
  `Monadic/Alg.lean`; coherence in the typing derivation is
  `Monadic/Coherence.lean`, a coupling (parametricity) argument, needed
  because lambda-case typing is genuinely non-unique.  Hypotheses:
  `[Monad m]`, `[LawfulMonad m]`, `[InjectiveFormers S.Ty]` — no iteration
  operator and no Elgot law.  `Monadic/Examples.lean` instantiates at the
  partiality monad and separates the two booleans.

## Honest boundary

* A model here is an algebra of the *presentation*.  It is **not** a Freyd
  category, and nothing in this directory proves that a *Freyd* category gives
  such an algebra.  The monadic case is proved: `Alg.ofModel` discharges both
  `coh` and `sound` for the monadic denotation.
* `Syn.isInitial` therefore says: initial *among algebras of the equational
  presentation* — a class that now provably contains the monadic models.  It
  does not say initial among Freyd categories, and it must not be restated
  that way.
* The syntactic *category* of `Models/SynCategory.lean` carries exactly the
  three category laws, and `Models/SynCoproduct.lean` adds binary coproducts.
  No premonoidal, Freyd, cartesian-value or distributive structure is
  constructed on it, and none is claimed.  In particular the value/pure
  subcategory has no definition, because `Pure` is nowhere proved stable under
  `Equiv`.
* The empty type is **not** exhibited as an initial object of the syntactic
  category, and no `HasFiniteCoproducts` instance is registered:
  `Equiv.emptyInitial` fires only when the scrutinee of a `let` is literally of
  the form `.abort a`, so it does not prove `bv 0 ≈ abort (bv 0)` at the empty
  type.  This is a gap in the presentation rather than a proof of
  non-derivability — no separating model is built here.
-/
