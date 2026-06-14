// Document templates and standalone compilation logic.

#import "@preview/ctheorems:1.1.3": thmrules

/// Thesis metadata defaults.
#let thesis-info = (
  author: "Jad-Elkhaleq Ghalayini",
  date: datetime(day: 28, month: 3, year: 2026),
  affiliation: "University of Cambridge",
)

/// Nesting depth: 0 at top level, incremented by each document wrapper.
#let _nesting-depth = state("_nesting-depth", 0)

/// Standalone wrapper for a part (e.g. type-theoretic-ssa/main.typ).
/// When standalone, shows an article-style title and sets document metadata.
/// When nested, the title becomes a top-level heading and all body headings
/// are shifted down by the nesting offset.
#let part(title: none, body) = {
  _nesting-depth.update(n => n + 1)
  set heading(numbering: "1.")
  show: thmrules
  context {
    let depth = _nesting-depth.get()
    let offset = depth - 1
    if offset == 0 {
      set document(title: title, author: thesis-info.author)
      if title != none {
        align(center)[
          #text(size: 20pt, weight: "bold", title)
          #v(1em)
        ]
      }
      body
    } else {
      if title != none {
        heading(depth: 1, title)
      }
      set heading(offset: offset)
      body
    }
  }
  _nesting-depth.update(n => n - 1)
}

/// Standalone wrapper for a chapter (e.g. s-expressions/main.typ).
/// Same nesting logic as `part`.
#let chapter(title: none, body) = {
  _nesting-depth.update(n => n + 1)
  set heading(numbering: "1.")
  show: thmrules
  context {
    let depth = _nesting-depth.get()
    let offset = depth - 1
    if offset == 0 {
      set document(title: title, author: thesis-info.author)
      if title != none {
        align(center)[
          #text(size: 18pt, weight: "bold", title)
          #v(1em)
        ]
      }
      body
    } else {
      if title != none {
        heading(depth: 1, title)
      }
      set heading(offset: offset)
      body
    }
  }
  _nesting-depth.update(n => n - 1)
}
