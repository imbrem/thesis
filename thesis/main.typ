#import "/lib/prelude.typ": *

#show: thesis.with(
  title: "Categorical Imperative Programming",
  subtitle: "Type theory, refinement, and semantics for SSA",
)

#include "intro/main.typ"

#include "type-theoretic-ssa/main.typ"

#include "category-theory/main.typ"

#include "lambda-ssa/main.typ"

#include "equational-theory/main.typ"

#include "denotational-semantics/main.typ"

#include "models/main.typ"

#include "refinement/main.typ"

#include "related-work/main.typ"

#pagebreak()
#bibliography("refs.bib")

// --- Appendix ---

#pagebreak()
#show: appendix

#include "appendix/main.typ"
