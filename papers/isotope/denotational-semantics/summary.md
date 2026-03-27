# Summary: The Denotational Semantics of SSA

**File:** `denotational-semantics-of-ssa.tex`
**Authors:** Jad Ghalayini, Neel Krishnaswami (2024, arXiv preprint)

## Motivation

SSA has been the dominant compiler IR since the late 1980s, but its correctness has historically been handled informally. This is no longer adequate: modern hardware has weak memory, compilers exploit undefined behaviour aggressively, and language semantics are increasingly complex. The paper proposes studying the *equational theory* of SSA as a clean interface between compiler writers (who rely on equations to justify optimizations) and hardware/language designers (who validate models against equations).

## Core Contributions

### 1. A type theory for SSA (lambda_SSA)

The paper gives a type-theoretic presentation of SSA with explicit typing rules and a well-defined equational theory. Unlike traditional SSA presentations based on basic blocks and phi-functions, this formulation uses a structured syntax with:

- **Expressions:** the data-flow fragment (let-bindings, case splits, pairs, injections, abort)
- **Regions:** the control-flow fragment (basic blocks with branching and loops, via `where`-expressions)

The key insight is that SSA's single-assignment discipline corresponds to a type-theoretic requirement that every variable has a unique definition site with a known type.

### 2. Equational theory

The equational theory is strong enough to validate a variety of standard control- and data-flow transformations. It includes:

- Beta/eta rules for expressions
- Commuting conversions (reordering let-bindings, pushing operations into branches)
- Rules for control flow (loop unrolling, dead code elimination, block inlining)
- A notion of "standard SSA" that captures the traditional flat-CFG presentation within the structured syntax

### 3. Categorical semantics via Freyd-Elgot categories

The denotational semantics interprets SSA in *distributive Elgot categories*, which combine:

- **Freyd categories** (premonoidal categories with a cartesian centre) — for modelling sequencing of effectful computations
- **Distributive coproducts** — for modelling conditionals/branching
- **Strong Conway iteration** — for modelling loops

String diagrams provide a visual calculus for these categories, making equational reasoning more intuitive.

### 4. Soundness and completeness

- **Soundness:** every equation provable in the type theory holds in all distributive Elgot categories.
- **Completeness:** the syntax quotiented by the equational theory yields the *initial* distributive Elgot category. This means every equation valid in all models is provable syntactically — there are no missing equations.

This is a surprising result: SSA turns out to be the first syntactic presentation of distributive Elgot categories, establishing a deep connection between compiler IRs and category theory.

### 5. Concrete models

The paper demonstrates the axiomatization's utility with several concrete models:

- **Monads and monad transformers** — state, exceptions, nondeterminism, nontermination (via `StateT`, `ExceptT`, etc.)
- **Trace models** — a partial-trace-based semantics
- **TSO weak memory** — based on Jagadeesan, Jeffrey, and Riely's "sparky" semantics; the first proof that SSA-based loop transformations are compatible with weak memory
- **Brookes-style concurrency** — instantiable to release/acquire concurrency

### 6. Lean mechanization

The syntactic metatheory (substitution lemmas), the completeness proof (initiality of the syntactic model), and the SPARC TSO model are mechanized in Lean 4.

## Paper structure

| Section | Content |
|---------|---------|
| 1. Introduction | Motivation, contributions |
| 2. SSA Form | From three-address code to SSA; type-theoretic SSA |
| 3. Type Theory | Typing rules, metatheory (substitution) |
| 4. Equational Theory | Equations for expressions, regions, standard SSA |
| 5. Denotational Semantics | Freyd-Elgot categories, string diagrams, soundness/completeness |
| 6. Concrete Models | Monads/transformers, traces, TSO, Brookes-style |
| 7. Discussion & Related Work | Lean formalization, related work, future directions |
| Appendices | Records/enums, Bohm-Jacopini theorem for SSA, environment comonad, full proofs |
