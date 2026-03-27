# Isotope Papers

LaTeX sources for the published/submitted papers underlying the thesis, plus summaries and errata for AI agents. All papers are by **Jad Ghalayini** and **Neel Krishnaswami**.

Known errors across all papers are catalogued in [ERRORS.md](ERRORS.md).

## Papers

### 1. The Denotational Semantics of SSA

- **File:** `denotational-semantics-of-ssa.tex`
- **Year:** 2024 (arXiv preprint)
- **Status:** Published/preprint
- **Detailed summary:** [denotational-semantics/summary.md](denotational-semantics/summary.md)

The foundational paper. Gives a type theory for SSA (lambda_SSA) with an equational theory strong enough to validate control- and data-flow transformations. Provides a categorical semantics using Freyd-Elgot categories, proves soundness and completeness of the type theory w.r.t. the categorical axiomatization. Demonstrates concrete models including TSO weak memory and Brookes-style concurrency. Metatheory and completeness proof mechanized in Lean.

### 2. A Complete Refinement System for Substructural SSA

- **File:** `complete-refinement-ssa.tex`
- **Year:** 2025 (submission)
- **Status:** Under review (anonymous)
- **Detailed summary:** [complete-refinement/summary.md](complete-refinement/summary.md)

Extends the first paper with substructural types and an effect system. Introduces lambda_iter, a calculus for reasoning about program *refinement* (not just equivalence) given an effect system with information about directed commutativity, linearity, and peephole rewrites. Proves the refinement calculus sound and complete w.r.t. a categorical axiomatization. Enables model-free verification of compiler optimizations.

### 3. Sound and Complete Refinement for SSA with Substructural Effects

- **File:** `hope.tex`
- **Year:** 2025
- **Status:** Extended abstract (HOPE workshop)
- **Detailed summary:** [hope/summary.md](hope/summary.md)

Short extended abstract summarizing the refinement work. No new contributions beyond paper 2.

## Relationship between papers

**Paper 1** establishes the core framework: type-theoretic SSA, equational theory, Freyd-Elgot categorical semantics, and soundness/completeness. **Paper 2** is the major extension, adding substructural types, effects, and *directed* refinement (not just equivalence). **Paper 3** is a brief workshop summary of paper 2.

## Shared infrastructure

- `references.bib` — shared bibliography
- `string-diagrams.sty` — TikZ macros for string diagrams
- `acmart.cls`, `ACM-Reference-Format.bst`, `acmauthoryear.cbx`, `acmnumeric.cbx` — ACM formatting
- `acm-jdslogo.png` — ACM logo asset

All `.tex` files reference these via relative paths. Keep everything in this directory together.

## Key concepts for agents

- **SSA (Static Single Assignment):** The dominant compiler IR. Every variable is defined exactly once, making substitution valid and enabling efficient optimizations.
- **lambda_SSA / lambda_iter:** The two type theories. lambda_SSA mirrors traditional SSA structure; lambda_iter is an expression language with iteration that is equivalent but easier to reason about syntactically.
- **Freyd-Elgot categories:** The categorical semantics. Freyd categories model effectful computation; Elgot structure (Conway iteration) models loops; distributive coproducts model branching.
- **Soundness and completeness:** Every equation/refinement valid in all models is provable in the type theory, and vice versa.
- **Refinement (not equivalence):** Paper 2's key shift. Optimizations are directed: the output's behaviours must be a *subset* of the input's.
- **Substructural effects:** Effects classified by commutativity (left/right-mover), linearity (affine, relevant, linear), and peephole rewrites.
