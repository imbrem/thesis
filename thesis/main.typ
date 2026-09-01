#import "/lib/prelude.typ": *

#show: thesis.with(
  title: "Categorical Imperative Programming",
  subtitle: "Type theory, refinement, and semantics for SSA",
)

// Non-rendered decision queue. These remain queryable through `make todo` and
// `make status` without turning editorial planning into thesis body text.
#todo(kind: "question", owner: "author", source: "agent", visible: false)[Choose whether the thesis spine presents the unrefined calculi first and refinement as a conservative extension.]
#todo(kind: "question", owner: "author", source: "agent", visible: false)[Choose whether the equational theory precedes semantics for motivation or follows soundness.]
#todo(kind: "question", owner: "author", source: "agent", visible: false)[Choose whether categorical background is standalone or introduced just in time before abstract models.]
#todo(kind: "question", owner: "author", source: "agent", visible: false)[Choose the canonical SSA surface syntax: paper where-blocks or the new brace-based variant; retain both until a comparison theorem and migration path exist.]
#todo(kind: "plan", owner: "author", source: "agent", visible: false)[Decide which translations are thesis-critical and map each claim to current Lean evidence before editing the surrounding prose.]
#todo(kind: "question", owner: "author", source: "agent", visible: false)[Decide whether full SSA soundness and completeness belongs in an appendix, leaving translation soundness in the main development.]
#todo(kind: "plan", owner: "author", source: "agent", visible: false)[Fuse the two imported related-work sections only after deciding which topic-specific passages should move beside the relevant technical sections.]
#todo(kind: "question", owner: "author", source: "agent", visible: false)[Specify the theorem and abstraction layer for equivalence with previous work when refinement is symmetric.]

#include "intro/main.typ"

#todo[Decide whether the thesis spine should introduce the unrefined iteration calculus before the broader type-theoretic SSA development, matching the refinement paper's progression.]

#include "type-theoretic-ssa/main.typ"

#include "category-theory/main.typ"

#include "lambda-ssa/main.typ"

#include "equational-theory/main.typ"

#include "denotational-semantics/main.typ"

#include "models/main.typ"

#include "refinement/main.typ"

#include "related-work/main.typ"

#todo[Decide whether to move the two imported related-work discussions into one dedicated chapter, with topic-specific material floated to the relevant technical chapters only after their overlap has been mapped.]

#todo[Decide whether the full soundness-and-completeness development for the SSA equational theory belongs in the main narrative or an appendix, especially if the main text later presents the distributive-Freyd-category account via an intermediate calculus.]

// --- Appendix ---

#pagebreak()
#show: appendix

#include "appendix/main.typ"

#pagebreak()
#bibliography("refs.bib")
