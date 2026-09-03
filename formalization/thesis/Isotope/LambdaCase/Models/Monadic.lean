import Isotope.LambdaCase.Models.Monadic.Denotation
import Isotope.LambdaCase.Models.Monadic.Coherence
import Isotope.LambdaCase.Models.Monadic.Alg
import Isotope.LambdaCase.Models.Monadic.Examples

/-!
# The monadic bridge for lambda-case

| file | content |
|---|---|
| `Monadic/Denotation.lean` | `denote`, its renaming and substitution lemmas,
  purity, and `Equiv.regular` |
| `Monadic/Coherence.lean` | the coupling theorem and `denote_coh`, i.e. the
  `coh` field of `Alg` |
| `Monadic/Alg.lean` | one lemma per axiom, `sound`, and `Alg.ofModel` |
| `Monadic/Examples.lean` | the partiality model separates the two booleans,
  hence they are not equated by the theory |

`Alg.ofModel` needs `[Monad m]`, `[LawfulMonad m]` and
`[InjectiveFormers S.Ty]`.  It needs **no** iteration operator and **no**
Elgot law; that is the hypothesis split that distinguishes lambda-case from
lambda-iter.
-/
