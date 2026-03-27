# Summary: Sound and Complete Refinement for SSA with Substructural Effects

**File:** `hope.tex`
**Authors:** Jad Ghalayini, Neel Krishnaswami (2025, extended abstract / HOPE workshop)

## Overview

This is a short extended abstract summarizing the refinement work of the second paper for a workshop audience. It is not a standalone contribution but rather a concise presentation of the key ideas.

## Content

The abstract motivates effect-generic reasoning about compiler optimizations. It frames the problem around the observation that many optimizations depend on three kinds of high-level effect information:

1. **Directed commutativity** — how effects commute (as refinements, not just equations). E.g., UB commutes with nondeterminism and memory access, but not with nontermination. Sometimes commutativity is one-directional: UB followed by nontermination refines to nontermination, but not vice versa.

2. **Peephole rewrites** — model-specific facts about individual operations. E.g., store-then-load elimination for mem2reg.

3. **Linearity** — whether effects can be duplicated, discarded, or fused. E.g., nontermination is relevant (duplicable), nondeterminism is affine (discardable) and fusable.

It then briefly describes lambda_iter, its equivalence with substructural SSA, the sound and complete denotational semantics, and models supporting weak memory and separation logic.

## Relationship to other papers

This is a condensed summary of the main results of `complete-refinement-ssa.tex` (paper 2), targeted at a workshop audience. It does not contain new results beyond that paper.

## Known issues

The file has corrupted content in the CCSXML block (body text spliced into an XML tag) and a typo ("rewrties" → "rewrites"). See [ERRORS.md](ERRORS.md) for details.
