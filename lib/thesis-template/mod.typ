// Thesis template: title page, statement of originality, TOC, and document setup.

#let statement-of-originality = align(center + horizon, read("statement-of-originality.txt"))

#let cambridge-logo = image("ucam-cs-colour.svg", width: 15em)

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
  author: none,
  date: none,
  logo: cambridge-logo,
  body,
) = {
  set document(title: title, author: author, date: date)
  set text(lang: "en")
  set heading(numbering: "1.")
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
  body
}

/// Show rule for appendix sections.
/// Use as `#show: appendix` before appendix content.
#let appendix(body) = {
  set heading(numbering: "A.", supplement: [Appendix])
  counter(heading).update(0)
  body
}