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

Raw named and locally nameless terms and their contexts remain shared at
`LambdaIter.Named` and `LambdaIter.LocallyNameless`. Named substitution,
alpha-equivalence, and named-to-locally-nameless translation also remain over
that shared raw syntax.
