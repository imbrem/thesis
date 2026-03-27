# Papers

This directory provides context for AI agents helping write, revise, or explain the thesis. It contains the papers underlying the thesis and related/cited work.

All thesis papers are by **Jad Ghalayini** and **Neel Krishnaswami** (University of Cambridge).

## Directory layout

```
papers/
  CLAUDE.md               — this file (top-level context for AI agents)
  isotope/                — LaTeX sources, summaries, and errata for the thesis papers
    CLAUDE.md             — detailed per-paper metadata and agent glossary
    ERRORS.md             — known typos, math errors, and LaTeX issues
    <paper-name>/summary.md — detailed per-paper summaries
    *.tex                 — LaTeX sources
    references.bib        — shared bibliography
    string-diagrams.sty   — shared TikZ macros for string diagrams
    acmart.cls, ACM-*     — ACM formatting infrastructure
  cited/                  — PDFs and notes on related/cited work
    CLAUDE.md             — index of related papers
```

## Quick reference: the three papers

| # | Paper | File | Year | Status |
|---|-------|------|------|--------|
| 1 | The Denotational Semantics of SSA | `isotope/denotational-semantics-of-ssa.tex` | 2024 | Published (arXiv preprint) |
| 2 | A Complete Refinement System for Substructural SSA | `isotope/complete-refinement-ssa.tex` | 2025 | Under review |
| 3 | Sound and Complete Refinement for SSA with Substructural Effects | `isotope/hope.tex` | 2025 | Extended abstract (HOPE) |

See [isotope/CLAUDE.md](isotope/CLAUDE.md) for detailed summaries, section maps, and a glossary of key concepts.
