# Issue #60 LambdaIter migration

| Previous API/path | Current API/path | Role |
| --- | --- | --- |
| `LambdaIter.NoSubtyping.Named.HasType` | `LambdaIter.Named.HasType` (`Isotope.LambdaIter.Typing`) | exact named typing |
| `LambdaIter.NoSubtyping.LocallyNameless.HasType` | `LambdaIter.LocallyNameless.HasType` (`Isotope.LambdaIter.Typing`) | exact locally nameless typing |
| `LambdaIter.NoSubtyping.{Named,LocallyNameless}.Eqv` | `LambdaIter.{Named,LocallyNameless}.Eqv` (`Isotope.LambdaIter.Equiv`) | exact equations |
| `LambdaIter.NoSubtyping.LocallyNameless` metatheory | `LambdaIter.LocallyNameless` (`Isotope.LambdaIter.Metatheory*`) | exact renaming/substitution metatheory |
| `LambdaIter.Named.HasType` | `LambdaIter.Subtyping.Named.HasType` (`Isotope.LambdaIter.Subtyping.Named.Typing`) | proof-relevant subtyping variant |
| `LambdaIter.LocallyNameless.HasType` | `LambdaIter.Subtyping.LocallyNameless.HasType` (`Isotope.LambdaIter.Subtyping.LocallyNameless.Typing`) | proof-relevant subtyping variant |
| `LambdaIter.Semantics.*` | `LambdaIter.Subtyping.Semantics.*` (`Isotope.LambdaIter.Subtyping.Semantics.*`) | proof-relevant derivation semantics |
| `LambdaIter.NoSubtyping.LocallyNameless.Categorical` | `LambdaIter.LocallyNameless.Categorical` (`Isotope.LambdaIter.Semantics.Categorical`) | exact categorical semantics |

## Import-path moves

| Previous import | Current import |
| --- | --- |
| `Isotope.LambdaIter.NoSubtyping.Typing` | `Isotope.LambdaIter.Typing` |
| `Isotope.LambdaIter.NoSubtyping.Equiv` | `Isotope.LambdaIter.Equiv` |
| `Isotope.LambdaIter.NoSubtyping.Metatheory` | `Isotope.LambdaIter.Metatheory` |
| `Isotope.LambdaIter.NoSubtyping.Metatheory.Syntax` | `Isotope.LambdaIter.Metatheory.Syntax` |
| `Isotope.LambdaIter.NoSubtyping.Metatheory.EquivSubst` | `Isotope.LambdaIter.Metatheory.EquivSubst` |
| `Isotope.LambdaIter.NoSubtyping.MinimalElaboration` | `Isotope.LambdaIter.MinimalElaboration` |
| `Isotope.LambdaIter.NoSubtyping.Semantics.Categorical` | `Isotope.LambdaIter.Semantics.Categorical` |
| `Isotope.LambdaIter.NoSubtyping.Semantics.Soundness` | `Isotope.LambdaIter.Semantics.Soundness` |
| `Isotope.LambdaIter.Named.Typing` | `Isotope.LambdaIter.Subtyping.Named.Typing` |
| `Isotope.LambdaIter.Named.Structural` | `Isotope.LambdaIter.Subtyping.Named.Structural` |
| `Isotope.LambdaIter.Named.Equiv` | `Isotope.LambdaIter.Subtyping.Named.Equiv` |
| `Isotope.LambdaIter.Named.EquivStructural` | `Isotope.LambdaIter.Subtyping.Named.EquivStructural` |
| `Isotope.LambdaIter.Named.Examples` | `Isotope.LambdaIter.Subtyping.Named.Examples` |
| `Isotope.LambdaIter.LocallyNameless.Typing` | `Isotope.LambdaIter.Subtyping.LocallyNameless.Typing` |
| `Isotope.LambdaIter.LocallyNameless.TypingSubst` | `Isotope.LambdaIter.Subtyping.LocallyNameless.TypingSubst` |
| `Isotope.LambdaIter.LocallyNameless.Equiv` | `Isotope.LambdaIter.Subtyping.LocallyNameless.Equiv` |
| `Isotope.LambdaIter.LocallyNameless.TypedEquiv` | `Isotope.LambdaIter.Subtyping.LocallyNameless.TypedEquiv` |
| `Isotope.LambdaIter.LocallyNameless.Examples` | `Isotope.LambdaIter.Subtyping.LocallyNameless.Examples` |
| `Isotope.LambdaIter.Semantics.Model` | `Isotope.LambdaIter.Subtyping.Semantics.Model` |
| `Isotope.LambdaIter.Semantics.Instruction` | `Isotope.LambdaIter.Subtyping.Semantics.Instruction` |
| `Isotope.LambdaIter.Semantics.Denotation` | `Isotope.LambdaIter.Subtyping.Semantics.Denotation` |
| `Isotope.LambdaIter.Semantics.Substitution` | `Isotope.LambdaIter.Subtyping.Semantics.Substitution` |
| `Isotope.LambdaIter.Semantics.Purity` | `Isotope.LambdaIter.Subtyping.Semantics.Purity` |
| `Isotope.LambdaIter.Semantics.IterationDiagrams` | `Isotope.LambdaIter.Subtyping.Semantics.IterationDiagrams` |
| `Isotope.LambdaIter.Semantics.Agreement` | `Isotope.LambdaIter.Subtyping.Semantics.Agreement` |
| `Isotope.LambdaIter.Semantics.Agreement.Combinators` | `Isotope.LambdaIter.Subtyping.Semantics.Agreement.Combinators` |
| `Isotope.LambdaIter.Semantics.Agreement.Iteration` | `Isotope.LambdaIter.Subtyping.Semantics.Agreement.Iteration` |
| `Isotope.LambdaIter.Semantics.Agreement.Full` | `Isotope.LambdaIter.Subtyping.Semantics.Agreement.Full` |

Raw named and locally nameless terms and their contexts remain shared at
`LambdaIter.Named` and `LambdaIter.LocallyNameless`. Named substitution,
alpha-equivalence, and named-to-locally-nameless translation also remain over
that shared raw syntax.
