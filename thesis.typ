#import "@preview/wordometer:0.1.5": word-count
#show: word-count.with(exclude: (<no-wc>, <appendix>))

#let production = false;

#import "thesis-template.typ": *
#import "todos.typ": *

#import "syntax.typ": *

#show: show-syntax

#show ref: it => {
  let el = it.element
  if el == none or el.func() != figure {
    it
  } else {
    link(el.location(), el.supplement)
  }
}

// TODO: think of a better way to go fix ∅...
// #show math.equation: set text(font: "STIX Two Math")

#set text(lang: "en")

#set heading(numbering: "1.")

#show heading.where(level: 0): set heading(supplement: [Chapter])

#set document(
  title: [
    Categorical imperative programming
    //: type theory, refinement, and semantics for SSA
  ],
  author: "Jad-Elkhaleq Ghalayini",
  date: datetime(day: 12, month: 1, year: 2026),
)

#align(center + horizon)[
  #title()

  *Type theory, refinement, and semantics for SSA*

  \

  \

  #context document.author.at(0)

  \

  \

  #context document.date.display("[month repr:long] [year]")

  \

  \


  #image("ucam-cs-colour.svg", width: 15em)

  \

  \

  \

  #stats-box(production)
]

#pagebreak()

#statement-of-originality

#todo[

  We should factor this template, and have a global TODOs list, maybe outside the document...

  What's the right way to format this?

  Do we put the acknowledgements here or after the abstract?

]

#todo[go make a proper listing function for code...]

#todo[go follow the outline I came up with with Neel...]

#pagebreak()

#align(center + horizon)[
  Is _this_ abstract enough?
  #todo[Actually write an abstract]
]

#pagebreak()

#outline()

#pagebreak()

#(thesis-state.update)(body-state)

= Introduction

#todo[
  TFW I need a thesis statement
]

= Static Single Assignment (SSA)

#[
  #set heading(offset: 1)
  #include "content/static-single-assignment.typ"
]

= Conventions and Notation

#[
  #set heading(offset: 1)
  #include "content/background/conventions.typ"
]

= Type-Theoretic SSA

#[
  #set heading(offset: 1)
  #include "content/type-theoretic-ssa/inductive-ssa.typ"
]

= Substructural SSA

#[
  #set heading(offset: 1)
  #include "content/type-theoretic-ssa/substructural-ssa.typ"
]

= Basic (Enriched) Category Theory

#[
  #set heading(offset: 1)
  #include "content/background/category-theory.typ"
]

= Semantics of Imperative Programming

#[
  #set heading(offset: 1)

  #include "content/semantics/imperative.typ"
]

= Semantics of SSA

#[
  #set heading(offset: 1)

  #include "content/semantics/cart-ssa.typ"
]

#the-bibliography

#pagebreak()

#let appendix(body) = {
  set heading(numbering: "A", supplement: [Appendix])
  counter(heading).update(0)
  (thesis-state.update)(appendix-state)
  [ #body <appendix> ]
}

#show: appendix
