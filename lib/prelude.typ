// One-stop import for all shared libraries.
// Usage: #import "/lib/prelude.typ": *

#import "/lib/thesis-template/mod.typ": appendix, thesis

#let chapter-quote(
  body,
  attribution: none,
) = [
  #quote(body, attribution: attribution, block: true)
]
