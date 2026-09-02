// Shared presentation helpers for imported program displays.
//
// These deliberately style only the display container. Language-specific
// syntax stays in the calling chapter so that old/new syntax remains
// independently searchable during migration.

#let fit-to-width(body) = layout(size => {
  let measured = measure(body)
  let ratio = calc.min(1, size.width / measured.width)
  if ratio < 1 {
    scale(x: ratio * 100%, y: ratio * 100%, reflow: true, body)
  } else {
    body
  }
})

#let semi-math-program(body, size: 8.5pt) = text(size: size, body)

#let semi-math-panel(
  body,
  caption: none,
  numbering: none,
  size: 8.5pt,
  body-height: auto,
) = figure(
  block(height: body-height, align(top, semi-math-program(body, size: size))),
  caption: caption,
  kind: "program-panel",
  supplement: [],
  numbering: numbering,
)

// Raw content otherwise causes Typst's automatic figure-kind detection to
// label the result as a Listing. This thesis treats pseudocode as a figure.
#let code-figure(body, caption: none) = figure(
  align(left, fit-to-width(body)),
  caption: caption,
  kind: "code-figure",
  supplement: [Figure],
)
