# Summary: A Complete Refinement System for Substructural SSA

**File:** `complete-refinement-ssa.tex`
**Authors:** Jad Ghalayini, Neel Krishnaswami (2025, under review)

## Motivation

The first paper (denotational semantics of SSA) established an equational theory — but compiler optimizations are fundamentally *directed* rewrites, not equations. The output of an optimization must be a *refinement* of the input: its possible behaviours must be a subset of the original's. Furthermore, which rewrites are valid depends on effects: substitution is valid for pure operations but not in general; UB can be eliminated but not introduced; nondeterminism can be discarded but not duplicated in the same way.

The paper observes that many practical optimizations (loop hoisting, mem2reg, SCCP) depend not on model-specific details but on high-level effect information:

1. **Directed commutativity** — how effects commute as refinements (e.g., UB is a right-mover w.r.t. everything, but only a left-mover w.r.t. non-blocking effects)
2. **Linearity/substructural properties** — whether effects can be duplicated, discarded, or fused (e.g., UB is eliminable and duplicable but not introducible; nondeterminism is affine and fusable)
3. **Peephole rewrites** — model-specific facts about individual operations (e.g., store-then-load elimination for mem2reg)

## Core Contributions

### 1. lambda_iter: an expression language for SSA with substructural effects

The paper introduces lambda_iter, a calculus with:

- **Substructural types** tracking how variables may be used (linear, affine, relevant, unrestricted)
- **An effect system** parameterized by information about commutativity, linearity, and peephole rewrites
- **Iteration** as a primitive (replacing the `where`-based recursion of the first paper)

The key idea is that the *refinement theory* of lambda_iter is parameterized by an abstract effect specification rather than a concrete model. This enables model-free verification of optimizations.

### 2. Equivalence with substructural SSA (lambda_SSA)

lambda_iter looks very different from SSA (it's an expression language with iteration), but the paper shows it is equivalent to a substructural variant of lambda_SSA via meaning-preserving translations in both directions. This means reasoning about lambda_iter (which has nicer syntactic properties) transfers directly to SSA.

The translation goes through ANF (A-normal form) as an intermediate step: expressions are first ANF-converted, then translated to SSA.

### 3. Categorical semantics and completeness

The categorical axiomatization extends the first paper's Freyd-Elgot categories with:

- **Poset-enrichment** — morphisms are ordered by refinement, not just equated
- **Effect-indexed subcategories** — capturing which morphisms have which effects
- **Substructural constraints** — the categorical structure respects linearity

Soundness and completeness are proved: the syntactic model (lambda_iter quotiented by the refinement theory) is initial among all models. This means the refinement calculus captures *exactly* what holds in all models — no missing refinements.

### 4. Concrete models

- **Undefined behaviour** — UB as a bottom element in a refinement ordering; UB is eliminable, duplicable, and a right-mover
- **Heaps/state** — modelling memory with read/write operations, separation-logic-style reasoning about aliasing
- **Monad transformers** — systematic construction of models via `StateT`, `ExceptT`, etc.
- **Brookes-style concurrency** — release/acquire weak memory, extending the first paper's models to the refinement setting

### 5. Compilation from expressions to SSA

The paper gives a formal compilation pipeline: lambda_iter expressions → ANF → SSA, and proves it correct. This connects the abstract calculus to a concrete compilation strategy.

## Paper structure

| Section | Content |
|---------|---------|
| 1. Introduction | Motivation (directed rewrites, effect-dependent reasoning), running examples (UB + substitution) |
| 2. SSA | Review of SSA, type-theoretic presentation |
| 3. lambda_iter | Syntax, typing, metatheory, refinement theory |
| 4. Semantics | Models of lambda_iter, denotational semantics of expressions |
| 5. SSA Typing & Semantics | Typing rules, denotational semantics, interconversion with lambda_iter |
| 6. Concrete Models | UB, heaps, concurrency |
| 7. Discussion & Related Work | Comparison with related approaches |
| 8. Completeness | Syntactic model construction, packing/unpacking lemmas |
| 9. Compiling Expressions to SSA | ANF expressions, ANF-to-SSA translation |
| 10. Models | Poset-enriched Elgot monads, UB, monad transformers, Brookes-style concurrency |
