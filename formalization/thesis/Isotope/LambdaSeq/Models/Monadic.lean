import Isotope.LambdaSeq.Models.Monadic.Denotation
import Isotope.LambdaSeq.Models.Monadic.Alg
import Isotope.LambdaSeq.Models.Monadic.Examples

/-!
# The monadic bridge for lambda-seq

| file | content |
|---|---|
| `Monadic/Denotation.lean` | `denote`, its renaming and substitution lemmas,
  purity, and the missing lambda-seq metatheory (`HasType.bsubst`,
  `HasType.instantiate`, `Equiv.regular`) |
| `Monadic/Alg.lean` | `HasType.uniq`, `denote_agree`, `denote_coh`, the four
  axiom lemmas, `sound`, and `Alg.ofSeqModel` |
| `Monadic/Examples.lean` | the partiality monad over the empty signature, and
  two terms it separates |

`Alg.ofSeqModel` needs `[Monad m]` and `[LawfulMonad m]` and nothing else.
-/
