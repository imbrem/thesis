# Categorical Imperative Programming

**Type theory, refinement, and semantics for SSA**

PhD thesis — Jad Ghalayini, University of Cambridge

- [Thesis PDF](https://imbrem.github.io/thesis/thesis/main.pdf)

## Papers

- [The Denotational Semantics of SSA](https://imbrem.github.io/thesis/papers/isotope/denotational-semantics-of-ssa.pdf) (2024)
- [A Complete Refinement System for Substructural SSA](https://imbrem.github.io/thesis/papers/isotope/complete-refinement-ssa.pdf) (2025)
- [Sound and Complete Refinement for SSA with Substructural Effects](https://imbrem.github.io/thesis/papers/isotope/hope.pdf) (HOPE 2025)

## Formalization

- [Isotope — Lean 4 API docs](https://imbrem.github.io/thesis/formalization/isotope/)
- [discretion](https://github.com/imbrem/discretion) — Lean 4 formalization (paper-era, reference only)
- [debruijn-ssa](https://github.com/imbrem/debruijn-ssa) — Lean 4 formalization (paper-era, reference only)

## Build

```sh
make             # build thesis/main.pdf (default)
make papers      # build LaTeX papers
make all         # build everything
make submodules  # clone/update git submodules (formalization/papers/*)
make clean       # remove generated PDFs + LaTeX aux files
```
