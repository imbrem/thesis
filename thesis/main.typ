#import "/lib/prelude.typ": *

#show: thesis.with(
  title: "Categorical Imperative Programming",
  subtitle: "Type theory, refinement, and semantics for SSA",
  author: "Jad-Elkhaleq Ghalayini",
  date: datetime(day: 28, month: 3, year: 2026),
)

#include "intro/main.typ"

#include "type-theoretic-ssa/main.typ"

#pagebreak()
#bibliography("refs.bib")

// --- Appendix ---

#pagebreak()
#show: appendix

#include "appendix/main.typ"
