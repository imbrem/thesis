#import "/lib/prelude.typ": *

#show: thesis.with(
  title: "Categorical Imperative Programming",
  subtitle: "Type theory, refinement, and semantics for SSA",
)

#include "intro/main.typ"

#include "type-theoretic-ssa/main.typ"

#pagebreak()
#bibliography("refs.bib")

// --- Appendix ---

#pagebreak()
#show: appendix

#include "appendix/main.typ"
