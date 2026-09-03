import Isotope.LambdaIter.Models.Monadic.Model
import Isotope.LambdaIter.Models.Monadic.Coupling
import Isotope.LambdaIter.Models.Monadic.Free
import Isotope.LambdaIter.Models.Monadic.Denotation
import Isotope.LambdaIter.Models.Monadic.Coherence
import Isotope.LambdaIter.Models.Monadic.Soundness
import Isotope.LambdaIter.Models.Monadic.Alg
import Isotope.LambdaIter.Models.Monadic.Push
import Isotope.LambdaIter.Models.Monadic.Examples
import Isotope.LambdaIter.Models.Monadic.Concrete

/-!
# The monadic bridge

The semantic input to the algebras of all three equational presentations, and
the bridge theorems that turn a monad into an algebra.

| file | content |
|---|---|
| `Monadic/Model.lean` | `SeqModel`, `Model`, `Env`, `InjectiveFormers` |
| `Monadic/Coupling.lean` | `VRel`, `VPair`, `Coupled`, `proj_iterate'`,
  `Coupled.iterate` — the machinery coherence needs |
| `Monadic/Free.lean` | the free set model of the empty signature over `Part` |
| `Monadic/Denotation.lean` | `denote` for lambda-iter, renaming and
  substitution, purity, and `Eqv.regular` |
| `Monadic/Coherence.lean` | `denote_coupled`, `denote_coh` |
| `Monadic/Soundness.lean` | one lemma per axiom, including the four Elgot laws |
| `Monadic/Alg.lean` | derivation inversions, `sound_ax`, `sound`,
  `Alg.ofModel` |
| `Monadic/Examples.lean` | the partiality algebra separates a divergent loop
  from a value |

The three bridges are stacked by hypothesis strength:

* lambda-seq: `[Monad m]`, `[LawfulMonad m]`.
* lambda-case: those plus `[InjectiveFormers S.Ty]`.
* lambda-iter: those plus `[Iterate m]` and `[LawfulElgotMonad m]`.

Iteration enters the *coherence* proof as well as soundness: `Coupled.iterate`
runs two loops as one loop over related pairs and needs Elgot naturality and
uniformity to identify its projections.
-/
