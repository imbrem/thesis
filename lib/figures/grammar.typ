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
// To split a long production over several lines, insert a `linebreak()`
// between alternatives; continuation lines are prefixed with `cont-sep` so
// they read as ordinary BNF.
//
// Knobs (tweak here to restyle every grammar at once):
//   delim:        production symbol drawn between lhs and rhs (default `::=`)
//   alt-sep:      separator drawn between alternatives (default a vertical bar)
//   cont-sep:     prefix drawn at the start of a continuation line
//   col-gutter:   horizontal space between the three columns
//   row-gutter:   vertical space between productions
//   alts-width:   track sizing for the alternatives column; `1fr` lets long
//                 right-hand sides wrap, `auto` keeps them on one line
#let grammar(
  ..prods,
  delim: $::=$,
  alt-sep: $space.med | space.med$,
  cont-sep: $| space.med$,
  col-gutter: 0.75em,
  row-gutter: 0.7em,
  alts-width: 1fr,
) = {
  let render-alts(alts) = {
    let out = ()
    let started = false    // emitted an alternative on the current line yet?
    let line-start = true  // at the beginning of a (continuation) line?
    for a in alts {
      if type(a) == content and a.func() == linebreak {
        out.push(linebreak())
        started = false
        line-start = true
        continue
      }
      if started {
        out.push(alt-sep)
      } else if line-start and out.len() != 0 {
        out.push(cont-sep)
      }
      out.push(a)
      started = true
      line-start = false
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
