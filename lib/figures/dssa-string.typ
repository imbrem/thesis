// Native versions of the string diagrams in The Denotational Semantics of SSA.

#import "@preview/cetz:0.3.4"

#let _canvas(width: 7, height: 4.5, body) = cetz.canvas(length: 9mm, {
  import cetz.draw: *
  body((
    wire: (..pts) => line(..pts.pos(), stroke: black),
    state: (..pts) => line(..pts.pos(), stroke: (paint: red, dash: "dashed")),
    dot: p => circle(p, radius: 0.07, fill: black, stroke: black),
    box: (p, label, w: 0.9) => {
      rect((p.at(0) - w / 2, p.at(1) - 0.23), (p.at(0) + w / 2, p.at(1) + 0.23), fill: white, stroke: black)
      content(p, label)
    },
    text: (p, label) => content(p, label),
    curve: (a, b, c, d) => bezier(a, b, c, d),
  ))
})

#let coproduct-cfg-diagram() = _canvas(d => {
  (d.text)((1, 4.2), $A$); (d.text)((2.2, 4.2), $B$)
  (d.box)((1.6, 3.35), [subprogram 1], w: 1.65)
  (d.box)((0.7, 2.25), [subprogram 2], w: 1.65)
  (d.box)((2.75, 2.25), [subprogram 3], w: 1.65)
  (d.box)((2.15, 1.15), [subprogram 4], w: 1.65)
  (d.dot)((3.2, 3.05)); (d.dot)((1.25, 0.35))
  (d.wire)((1, 4), (1.25, 3.58)); (d.wire)((2.2, 4), (1.95, 3.58))
  (d.wire)((1.2, 3.12), (0.7, 2.48)); (d.wire)((2, 3.12), (2.75, 2.48))
  (d.wire)((0.4, 2.02), (1.25, 0.35)); (d.wire)((1, 2.02), (1.75, 1.38))
  (d.wire)((2.45, 2.02), (2.05, 1.38)); (d.wire)((3.05, 2.02), (2.45, 1.38))
  (d.wire)((2.15, 0.92), (1.25, 0.35), (1.25, 0))
  (d.wire)((3.2, 3.05), (3.2, 2.48))
  (d.text)((4.7, 3.1), [Zero morphism]); (d.text)((4.7, 2.25), [Region]); (d.text)((4.7, 0.4), [Codiagonal morphism])
})

#let elgot-trace-diagram(kind: "trace") = _canvas(d => {
  let fix = kind == "fixpoint"
  (d.text)((0.7, 4.1), $A$); (d.box)((0.7, 2.25), if fix { $f^dagger$ } else { $sans("Tr")_(A,B)^C(f)$ }, w: 1.25); (d.text)((0.7, 0.2), $B$)
  (d.wire)((0.7, 3.9), (0.7, 2.48)); (d.wire)((0.7, 2.02), (0.7, 0.4)); (d.text)((2, 2.25), $=$)
  (d.text)((3.2, 4.1), $A$); (d.box)((3.2, 2.25), $f$, w: 0.8); (d.text)((3.05, 0.2), $B$)
  if fix { (d.dot)((3.2, 3.15)); (d.wire)((3.2, 3.9), (3.2, 3.15), (3.2, 2.48)) } else { (d.wire)((3.2, 3.9), (3.05, 2.48)) }
  (d.wire)((3.05, 2.02), (3.05, 0.4)); (d.wire)((3.45, 2.02), (4.15, 1.4))
  (d.curve)((4.15, 1.4), (4.65, 1.4), (4.65, 3.15), (if fix { (3.3, 3.15) } else { (3.45, 2.48) }))
  (d.text)((4.75, 2.25), if fix { $A$ } else { $C$ })
})

#let premonoidal-state-diagram() = _canvas(d => {
  (d.text)((0.8, 4.1), $bb(N)$); (d.dot)((0.8, 3.55)); (d.box)((0.6, 2.85), [print], w: 1); (d.box)((1.8, 2), $dot + 2$); (d.box)((0.9, 1.05), [print], w: 1)
  (d.wire)((0.8, 3.9), (0.8, 3.55), (0.8, 3.08)); (d.wire)((0.9, 3.55), (1.8, 2.23)); (d.wire)((1.8, 1.77), (1.15, 1.28))
  (d.state)((0.1, 4), (0.1, 3.08), (0.35, 3.08)); (d.state)((0.35, 2.62), (0.65, 1.28)); (d.state)((0.65, 0.82), (0.65, 0.1))
  (d.text)((3, 2.1), $eq.not$)
  (d.text)((4.7, 4.1), $bb(N)$); (d.dot)((4.7, 3.55)); (d.box)((5.5, 2.85), $dot + 2$); (d.box)((4.55, 2), [print], w: 1); (d.box)((5.35, 1.05), [print], w: 1)
  (d.wire)((4.7, 3.9), (4.7, 3.55), (5.5, 3.08)); (d.wire)((4.7, 3.55), (4.55, 2.23)); (d.wire)((5.5, 2.62), (5.6, 1.28))
  (d.state)((4, 4), (4, 2.23), (4.3, 2.23)); (d.state)((4.8, 1.77), (5.1, 1.28)); (d.state)((5.1, 0.82), (5.1, 0.1))
})

#let environment-naturality-diagram(which) = _canvas(d => {
  let labels = (($A$, $B$, $C$), ($A$, $B$, $C$), ($A$, $B$, $C$))
  let x = 0.8 + which * 0.7
  (d.text)((0.45, 4.1), $R$); (d.text)((1.2, 4.1), $A$); (d.text)((2.1, 4.1), $B$); (d.text)((3, 4.1), $C$)
  (d.box)((x + 0.7, 2.2), if which == 0 { $f$ } else if which == 1 { $g$ } else { $h$ }, w: 0.8)
  (d.state)((0.05, 4), (0.05, 2.45), (x + 0.25, 2.45)); (d.state)((x + 0.25, 1.95), (0.05, 0.2))
  (d.wire)((0.45, 3.9), (x + 0.45, 2.45));
  for i in range(3) { let px = 1.2 + i * 0.9; if i == which { (d.wire)((px, 3.9), (x + 0.7, 2.45)); (d.wire)((x + 0.7, 1.95), (px, 0.2)) } else { (d.wire)((px, 3.9), (px, 0.2)) } }
})

#let environment-centrality-diagram() = _canvas(d => {
  (d.text)((0.5, 4.1), $R$); (d.dot)((0.8, 3.5)); (d.text)((1.6, 4.1), $A$); (d.text)((2.7, 4.1), $B$); (d.box)((1.35, 2.45), $f$); (d.box)((2.45, 1.35), $g$)
  (d.wire)((0.5, 3.9), (0.8, 3.5)); (d.wire)((0.8, 3.5), (1.05, 2.68)); (d.wire)((0.8, 3.5), (2.15, 1.58)); (d.wire)((1.6, 3.9), (1.65, 2.68)); (d.wire)((2.7, 3.9), (2.75, 1.58)); (d.text)((3.35, 2.2), $=$)
  (d.text)((4, 4.1), $R$); (d.dot)((4.3, 3.5)); (d.text)((5.1, 4.1), $A$); (d.text)((6.2, 4.1), $B$); (d.box)((4.85, 1.35), $f$); (d.box)((5.95, 2.45), $g$)
  (d.wire)((4, 3.9), (4.3, 3.5)); (d.wire)((4.3, 3.5), (4.55, 1.58)); (d.wire)((4.3, 3.5), (5.65, 2.68)); (d.wire)((5.1, 3.9), (5.15, 1.58)); (d.wire)((6.2, 3.9), (6.25, 2.68))
})
