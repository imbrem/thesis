// Reusable string diagrams for Conway iteration.

#import "@preview/cetz:0.3.4"

#let _panel(kind) = cetz.canvas(length: 5.5mm, {
  import cetz.draw: *

  let wire(..points, stroke: black) = line(..points.pos(), stroke: stroke)
  let node(pos) = circle(pos, radius: 0.07, fill: black, stroke: black)
  let box-node(pos, label, width: 0.72) = {
    let (x, y) = pos
    rect((x - width / 2, y - 0.22), (x + width / 2, y + 0.22),
      fill: white, stroke: black)
    content(pos, label)
  }
  let endpoint(pos, label) = content(pos, label)
  let equals() = content((3.15, 2), $=$)
  let loop(from, to, x: 2.35) = {
    bezier(from, (x, to.at(1)), (x, from.at(1)), (x, to.at(1)))
  }
  let boundary(a, b, label) = {
    rect(a, b, stroke: (paint: gray, dash: "dashed"))
    content(((a.at(0) + b.at(0)) / 2, a.at(1) - 0.2),
      text(size: 6pt, label), anchor: "north")
  }

  if kind == "fixpoint" {
    // f† = f ; [id, f†]
    endpoint((0.8, 4), $A$)
    node((0.8, 3.25))
    box-node((0.8, 2.15), $f$)
    endpoint((0.8, 0), $B$)
    wire((0.8, 3.85), (0.8, 3.25), (0.8, 2.37))
    wire((0.8, 1.93), (0.8, 0.15))
    wire((1.05, 1.93), (1.55, 1.45))
    bezier((1.55, 1.45), (0.92, 3.25), (2.1, 1.45), (2.1, 3.25))
    wire((0.92, 3.25), (0.8, 3.25))

    equals()

    endpoint((5.3, 4), $A$)
    box-node((5.3, 3.05), $f$)
    node((5.3, 2.35))
    box-node((5.3, 1.55), $f$)
    node((5.3, 0.8))
    endpoint((5.3, 0), $B$)
    wire((5.3, 3.85), (5.3, 3.27))
    wire((5.3, 2.83), (5.3, 2.35), (5.3, 1.77))
    wire((5.3, 1.33), (5.3, 0.8), (5.3, 0.15))
    wire((5.55, 2.83), (6.05, 2.35))
    bezier((6.05, 2.35), (5.4, 0.8), (6.55, 2.35), (6.55, 0.8))
    wire((5.4, 0.8), (5.3, 0.8))
  } else if kind == "naturality" {
    // (f ; (g + id))† = f† ; g
    endpoint((0.8, 4), $A$)
    node((0.8, 3.35))
    box-node((0.8, 2.55), $f$)
    box-node((0.8, 1.55), $g$, width: 0.5)
    endpoint((0.8, 0), $C$)
    wire((0.8, 3.85), (0.8, 3.35), (0.8, 2.77))
    wire((0.8, 2.33), (0.8, 1.77), (0.8, 0.15))
    wire((1.05, 2.33), (1.55, 1.75))
    bezier((1.55, 1.75), (0.92, 3.35), (2.1, 1.75), (2.1, 3.35))
    wire((0.92, 3.35), (0.8, 3.35))
    boundary((0.15, 1.1), (2.25, 3.65), $\(f ; \[g, sans("id")\]\)^dagger$)

    equals()

    endpoint((5.3, 4), $A$)
    node((5.3, 3.25))
    box-node((5.3, 2.35), $f$)
    box-node((5.3, 1.1), $g$, width: 0.5)
    endpoint((5.3, 0), $C$)
    wire((5.3, 3.85), (5.3, 3.25), (5.3, 2.57))
    wire((5.3, 2.13), (5.3, 1.32), (5.3, 0.15))
    wire((5.55, 2.13), (6.05, 1.65))
    bezier((6.05, 1.65), (5.42, 3.25), (6.55, 1.65), (6.55, 3.25))
    wire((5.42, 3.25), (5.3, 3.25))
    boundary((4.65, 1.55), (6.7, 3.55), $f^dagger$)
  } else if kind == "codiagonal" {
    // (f†)† = (f ; [id, inr])†
    endpoint((0.8, 4), $A$)
    node((0.8, 3.3))
    box-node((0.8, 2.15), $f$, width: 0.8)
    node((0.8, 1.15))
    endpoint((0.8, 0), $B$)
    wire((0.8, 3.85), (0.8, 3.3), (0.8, 2.37))
    wire((0.8, 1.93), (0.8, 1.15), (0.8, 0.15))
    wire((1.0, 1.93), (1.45, 1.5))
    bezier((1.45, 1.5), (0.92, 3.3), (1.95, 1.5), (1.95, 3.3))
    wire((0.92, 3.3), (0.8, 3.3))
    wire((1.15, 1.93), (1.6, 1.15))
    bezier((1.6, 1.15), (0.92, 1.15), (2.2, 1.15), (2.2, 0.75))
    wire((0.92, 1.15), (0.8, 1.15))

    equals()

    endpoint((5.3, 4), $A$)
    node((5.3, 3.3))
    node((5.3, 2.85))
    box-node((5.3, 2.05), $f$, width: 0.8)
    endpoint((5.3, 0), $B$)
    wire((5.3, 3.85), (5.3, 3.3), (5.3, 2.85), (5.3, 2.27))
    wire((5.3, 1.83), (5.3, 0.15))
    wire((5.6, 1.83), (6.0, 1.25))
    bezier((6.0, 1.25), (5.42, 3.3), (6.55, 1.25), (6.55, 3.3))
    wire((5.42, 3.3), (5.3, 3.3))
    wire((5.45, 2.85), (6.0, 2.35))
    bezier((6.0, 2.35), (5.42, 2.85), (6.35, 2.35), (6.35, 2.85))
    wire((5.42, 2.85), (5.3, 2.85))
  } else {
    // (g ; [inl, h])† = g ; [id, (h ; [inl, g])†]
    endpoint((0.8, 4), $A$)
    box-node((0.8, 3.25), $g$, width: 0.5)
    node((0.8, 2.7))
    box-node((0.8, 1.9), $f$, width: 0.8)
    box-node((1.55, 1.05), $g$, width: 0.5)
    endpoint((0.8, 0), $B$)
    wire((0.8, 3.85), (0.8, 3.47), (0.8, 2.7), (0.8, 2.12))
    wire((0.8, 1.68), (0.8, 0.15))
    wire((1.08, 1.68), (1.55, 1.27), (1.55, 0.83))
    bezier((1.55, 0.83), (0.92, 2.7), (2.15, 0.83), (2.15, 2.7))
    wire((0.92, 2.7), (0.8, 2.7))

    equals()

    endpoint((5.3, 4), $A$)
    node((5.3, 3.3))
    box-node((5.3, 2.55), $g$, width: 0.5)
    box-node((5.3, 1.65), $f$, width: 0.8)
    endpoint((5.3, 0), $B$)
    wire((5.3, 3.85), (5.3, 3.3), (5.3, 2.77), (5.3, 2.33), (5.3, 1.87))
    wire((5.3, 1.43), (5.3, 0.15))
    wire((5.6, 1.43), (6.05, 0.95))
    bezier((6.05, 0.95), (5.42, 3.3), (6.65, 0.95), (6.65, 3.3))
    wire((5.42, 3.3), (5.3, 3.3))
  }
})

#let conway-axiom-diagrams() = grid(
  columns: (1fr, 1fr),
  gutter: 1em,
  align: center,
  [#_panel("fixpoint") #linebreak() #smallcaps[Fixpoint]],
  [#_panel("naturality") #linebreak() #smallcaps[Naturality]],
  [#_panel("codiagonal") #linebreak() #smallcaps[Codiagonal]],
  [#_panel("dinaturality") #linebreak() #smallcaps[Dinaturality]],
)

#let conway-axiom-diagram(kind) = _panel(kind)
