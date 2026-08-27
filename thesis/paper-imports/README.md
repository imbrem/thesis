# Paper transcription ledger

This ledger tracks mechanical LaTeX-to-Typst ingestion. Imported prose remains
word-for-word; editorial or mathematical changes are recorded only as Typst
`#todo[...]` items.

## Conventions

- Begin each imported Typst leaf with a source-provenance comment containing
  the source paper, pinned repository commit, source section, and line range.
- Translate only markup, citations, labels, references, equations, figures,
  tables, and theorem environments.
- Do not silently fix prose, notation, citations, or mathematics.
- Put proposed corrections, transitions, cuts, and thesis-specific adaptations
  in `#todo[...]`.
- Preserve source labels where practical. Prefix replacement labels with a
  stable chapter identifier when collisions require renaming, and record the
  mapping below.
- If a LaTeX macro or figure cannot yet be represented, insert a TODO at the
  exact source position and record the omission below.
- Leaf transcription branches do not edit `thesis/main.typ` or chapter-level
  include graphs. Integration owns those files.

## Ledger

| Source paper | Pinned commit | Source section / lines | Destination | Branch | Status | Omissions / label mapping |
|---|---|---|---|---|---|---|
| Denotational Semantics of SSA | `afa82558acf643f53a3e038e635ed9520ace88c6` | Discussion and Related Work, lines 5218–5617 | `thesis/related-work/denotational-ssa.typ` | `transcription/dssa-related-work` | complete | Source label `ssec:tso` is represented by an inline TODO pending integration; the commented-out guarded-model paragraph at lines 5586–5591 is not rendered; all 51 cited bibliography records were mechanically imported from `papers/isotope/references.bib` into `thesis/refs.bib`. |
| Denotational Semantics of SSA | `afa82558acf643f53a3e038e635ed9520ace88c6` | Static SSA through syntactic metatheory, approximately 407–1614 | `thesis/lambda-ssa/overview.typ`, `type-theory.typ` | `transcription/dssa-lambda-ssa` | pending | — |
| Complete Refinement System for Substructural SSA | `afa82558acf643f53a3e038e635ed9520ace88c6` | Semantics / Models of lambda_iter, approximately 1653–2254 | `thesis/category-theory/refinement-models-raw.typ` | `transcription/refinement-category-theory` | pending | — |
