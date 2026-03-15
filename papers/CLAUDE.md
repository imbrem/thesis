# Papers

LaTeX sources for the published/submitted papers underlying this thesis. All use the ACM `acmart` document class and share `references.bib`, `string-diagrams.sty`, and the ACM style files.

## 1. The Denotational Semantics of SSA

- **File:** `denotational-semantics-of-ssa.tex`
- **Authors:** Jad Ghalayini, Neel Krishnaswami
- **Year:** 2024 (arXiv preprint)
- **Status:** Published/preprint

**Summary:** The foundational paper. Gives a type theory for SSA (lambda_SSA) with an equational theory strong enough to validate control- and data-flow transformations. Provides a categorical semantics using Freyd-Elgot categories, proves soundness and completeness of the type theory w.r.t. the categorical axiomatization. Demonstrates concrete models including TSO weak memory and Brookes-style concurrency. Metatheory and completeness proof mechanized in Lean.

**Key sections:**
- Introduction, SSA form (three-address code to SSA, type-theoretic SSA)
- Type theory and metatheory
- Equational theory (expressions, regions, standard SSA)
- Denotational semantics (Freyd-Elgot categories, string diagrams, soundness/completeness)
- Concrete models (monads/transformers, trace models, TSO weak memory, Brookes-style)
- Appendices: records/enums, Bohm-Jacopini for SSA, environment comonad, full proofs

**Thesis chapters covered:** Type-Theoretic SSA, Basic Enriched Category Theory, Semantics of Imperative Programming

## 2. A Complete Refinement System for Substructural SSA

- **File:** `complete-refinement-ssa.tex`
- **Authors:** Jad Ghalayini, Neel Krishnaswami
- **Year:** 2025 (submission)
- **Status:** Under review (anonymous)

**Summary:** Extends the first paper with substructural types and an effect system. Introduces lambda_iter, a calculus for reasoning about program *refinement* (not just equivalence) given an effect system with information about directed commutativity, linearity, and peephole rewrites. Proves the refinement calculus sound and complete w.r.t. a categorical axiomatization. Enables model-free verification of compiler optimizations.

**Key sections:**
- Introduction
- SSA
- lambda_iter expression language (syntax, typing, metatheory, refinement theory)
- Semantics (models of lambda_iter, semantics of expressions)
- SSA typing and semantics (typing rules, denotational semantics, interconversion with lambda_iter)
- Concrete models (UB, heaps, concurrency)
- Completeness proof (syntactic model, packing/unpacking)
- Compiling expressions to SSA (ANF expressions, ANF to SSA)
- Models (poset-enriched Elgot monads, UB, monad transformers, Brookes-style concurrency)

**Thesis chapters covered:** Type-Theoretic SSA, Substructural SSA, Semantics of Imperative Programming

## 3. Sound and Complete Refinement for SSA with Substructural Effects

- **File:** `hope.tex`
- **Authors:** Jad Ghalayini, Neel Krishnaswami
- **Year:** 2025
- **Status:** Extended abstract (workshop paper, likely HOPE)

**Summary:** Short extended abstract summarizing the refinement work. Introduces the motivation for effect-generic reasoning about compiler optimizations using directed commutativity, linearity, and peephole rewrites. Describes lambda_iter and its equivalence with substructural SSA, sound and complete denotational semantics, and models supporting weak memory and separation logic.

**Thesis chapters covered:** Overview of Substructural SSA and Semantics

## Shared infrastructure

- `references.bib` — shared bibliography
- `string-diagrams.sty` — TikZ macros for string diagrams
- `acmart.cls`, `ACM-Reference-Format.bst`, `acmauthoryear.cbx`, `acmnumeric.cbx` — ACM formatting
- `acm-jdslogo.png` — ACM logo asset

## Relationship between papers

Paper 1 (denotational semantics) establishes the core framework: type-theoretic SSA, equational theory, Freyd-Elgot categorical semantics, and soundness/completeness. Paper 2 (complete refinement) is the major extension, adding substructural types, effects, and *directed* refinement (not just equivalence). Paper 3 (HOPE) is a brief summary of paper 2.
