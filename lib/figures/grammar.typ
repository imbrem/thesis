// Grammar figures.
//
// A grammar is a list of *productions*, each pairing a metavariable (the
// left-hand side) with a sequence of alternative right-hand sides. The
// rendering is deliberately factored out into a handful of tweakable knobs
// (`delim`, `alt-sep`, gutters, the alternatives-column width) so we can
// restyle every grammar in the thesis from one place later.

// A single production: `nonterm ::= alt_1 | alt_2 | ...`.
//   nonterm: the metavariable(s) on the left, e.g. `$a, b, c$`
//   alts:    the alternative right-hand sides, as positional arguments
#let production(nonterm, ..alts) = (
  nonterm: nonterm,
  alts: alts.pos(),
)

// Render a sequence of `production`s as an aligned three-column table:
// the metavariables, the production delimiter, and the alternatives.
//
// Knobs (tweak here to restyle every grammar at once):
//   delim:        production symbol drawn between lhs and rhs (default `::=`)
//   alt-sep:      separator drawn between alternatives (default a vertical bar)
//   col-gutter:   horizontal space between the three columns
//   row-gutter:   vertical space between productions
//   alts-width:   track sizing for the alternatives column; `1fr` lets long
//                 right-hand sides wrap, `auto` keeps them on one line
#let grammar(
  ..prods,
  delim: $::=$,
  alt-sep: $space.med | space.med$,
  col-gutter: 0.75em,
  row-gutter: 0.7em,
  alts-width: 1fr,
) = {
  let render-alts(alts) = {
    let out = ()
    for (i, a) in alts.enumerate() {
      if i != 0 { out.push(alt-sep) }
      out.push(a)
    }
    out.join()
  }
  let cells = ()
  for p in prods.pos() {
    cells.push(p.nonterm)
    cells.push(delim)
    cells.push(render-alts(p.alts))
  }
  grid(
    columns: (auto, auto, alts-width),
    column-gutter: col-gutter,
    row-gutter: row-gutter,
    align: (right + top, center + top, left + top),
    ..cells,
  )
}
