# PhD Thesis: Categorical Imperative Programming

**Author:** Jad Ghalayini, University of Cambridge
**Subtitle:** Type theory, refinement, and semantics for SSA
**Typesetting:** Typst

## Topic

SSA (Static Single Assignment) is the dominant compiler intermediate representation: every variable is assigned exactly once, making substitution valid and enabling efficient optimizations. This thesis gives SSA a type-theoretic and categorical foundation. It introduces lambda_SSA, a type theory whose terms are SSA programs, with an equational theory strong enough to validate standard compiler transformations. The categorical semantics uses Freyd categories (effectful computation), Elgot iteration (loops), and distributive coproducts (branching). The equational theory is proved sound and complete w.r.t. these categorical axioms. An extension adds substructural types and an effect system, lifting the theory from program equivalence to directed refinement.

## Layout

```
.
├── thesis/                 Thesis content (every .typ compiles independently)
│   ├── main.typ            Root entry point → full thesis PDF
│   ├── refs.bib            Bibliography
│   ├── intro/main.typ      Introduction
│   ├── .../                (chapter directories, each with main.typ + leaves)
│   └── appendix/main.typ   Appendix
│
├── lib/                    Shared Typst libraries
│   ├── prelude.typ         One-stop import (re-exports everything)
│   ├── notation/
│   │   └── mod.typ         Mathematical notation macros, split by domain
│   ├── figures/
│   │   └── mod.typ         Custom figure types (grammars, rules, diagrams)
│   ├── theorems.typ        Theorem/lemma/proof environments
│   ├── template.typ        Document templates + standalone compilation logic
│   └── todos.typ           TODOs, margin notes, word count
│
├── notes/                  Research notes (not part of thesis)
├── papers/                 LaTeX source papers (see papers/CLAUDE.md)
├── formalization/
│   ├── thesis/             Lean 4 formalization of thesis metatheory
│   └── papers/             Git submodules (reference only, not in CI)
│       ├── discretion/     github.com/imbrem/discretion
│       └── debruijn-ssa/   github.com/imbrem/debruijn-ssa
└── .github/                CI workflows (see .github/CLAUDE.md)
```

## Typst conventions

### Imports

Every `.typ` file starts with:

```typst
#import "/lib/prelude.typ": *
```

The leading `/` resolves to the repo root via `typst.toml`. Never use relative `../` imports for library code.

### Standalone compilation

Every `.typ` file under `thesis/` compiles to its own PDF. Files use a standalone wrapper from `lib/template.typ` that applies document formatting when compiled directly but becomes a no-op when included by a parent.

### File roles

- **`main.typ`** in each chapter directory: entry point that includes its siblings
- **Leaf `.typ` files**: individual sections, each independently compilable
- **`mod.typ`** in `lib/` subdirectories: re-exports submodule contents

### Notation

All mathematical notation lives in `lib/notation/`, split by domain.

## Build

```sh
make             # build thesis/main.pdf (default)
make papers      # build LaTeX papers
make all         # build everything
make submodules  # clone/update git submodules (formalization/papers/*)
make clean       # remove generated PDFs + LaTeX aux files
```

PDFs are generated in-place next to their `.typ` source and are gitignored.

## Source papers

Three papers underpin this thesis (see `papers/isotope/CLAUDE.md` for details):

1. **The Denotational Semantics of SSA** (2024) — type theory for SSA, equational theory, Freyd-Elgot categorical semantics
2. **A Complete Refinement System for Substructural SSA** (2025) — substructural types, effects, directed refinement
3. **Sound and Complete Refinement for SSA with Substructural Effects** (2025) — HOPE extended abstract

## Formalization

Lean 4 project in `formalization/thesis/`. Mechanizes metatheory from the papers.

`formalization/papers/` contains Git submodules for the paper formalizations (discretion, debruijn-ssa). These are reference-only and not built in CI. Run `make submodules` to clone them.
