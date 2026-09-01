// Thesis template: title page, statement of originality, TOC, and document setup.

#import "@preview/ctheorems:1.1.3": thmrules
#import "/lib/template.typ": _nesting-depth, thesis-info

#let statement-of-originality = align(center + horizon, read("statement-of-originality.txt"))

#let cambridge-logo = image("ucam-cs-colour.svg", width: 15em)

#let _dependent-numbering(style) = (..numbers) => numbering(
  style,
  counter(heading).get().first(),
  ..numbers.pos(),
)

// Imported paper sections sometimes skip a Typst heading level, which leaves
// zero-valued counter components such as 6.1.0.2. Preserve the semantic source
// hierarchy while suppressing those conversion-only gaps in rendered numbers.
#let _compact-heading-numbering(style) = (..numbers) => numbering(
  style,
  ..numbers.pos().filter(number => number != 0),
)

#let _reset-at-chapter(counter) = heading => {
  if heading.level == 1 {
    counter.update(0)
  }
  heading
}

#let _chapter-numbered-figures(body) = {
  set figure(numbering: _dependent-numbering("1.1"))
  show heading: _reset-at-chapter(counter(figure.where(kind: image)))
  show heading: _reset-at-chapter(counter(figure.where(kind: table)))
  show heading: _reset-at-chapter(counter(figure.where(kind: raw)))
  show heading: _reset-at-chapter(counter(figure.where(kind: "thmenv")))
  body
}

#let title-page(
  title: none,
  subtitle: none,
  author: none,
  date: none,
  logo: cambridge-logo,
) = {
  align(center + horizon)[
    #text(size: 24pt, weight: "bold", title)

    #if subtitle != none [
      \
      *#subtitle*
    ]

    \
    \

    #author

    \
    \

    #date.display("[month repr:long] [year]")

    \
    \

    #logo
  ]
}

#let thesis(
  title: none,
  subtitle: none,
  author: thesis-info.author,
  date: thesis-info.date,
  logo: cambridge-logo,
  body,
) = {
  _nesting-depth.update(n => n + 1)
  set document(title: title, author: author, date: date)
  set text(lang: "en")
  set heading(numbering: _compact-heading-numbering("1."))
  show: thmrules
  show heading.where(level: 1): set heading(supplement: [Chapter])

  // --- Title page ---
  title-page(title: title, subtitle: subtitle, author: author, date: date, logo: logo)

  pagebreak()

  // --- Statement of originality ---
  statement-of-originality

  pagebreak()

  // --- Table of contents ---
  outline()

  pagebreak()

  // --- Body ---
  _chapter-numbered-figures(body)
  _nesting-depth.update(n => n - 1)
}

/// Show rule for appendix sections.
/// Use as `#show: appendix` before appendix content.
#let appendix(body) = {
  set heading(numbering: _compact-heading-numbering("A."), supplement: [Appendix])
  set figure(numbering: _dependent-numbering("A.1"))
  counter(heading).update(0)
  body
}
