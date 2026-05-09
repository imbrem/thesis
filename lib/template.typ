// Document templates and standalone compilation logic.

#import "@preview/ctheorems:1.1.3": thmrules

/// Standalone wrapper for a part (e.g. type-theoretic-ssa/main.typ).
/// Level-1 headings become part titles.
#let part(body) = {
  set heading(numbering: "1.")
  show: thmrules
  body
}

/// Standalone wrapper for a chapter (e.g. s-expressions/main.typ).
/// Level-1 headings become chapter titles.
#let chapter(body) = {
  set heading(numbering: "1.")
  show: thmrules
  body
}
