# Likely Errors in Papers

## 1. `hope.tex` — Sound and Complete Refinement for SSA with Substructural Effects

### Corrupted Content

| Line | Issue | Fix |
|------|-------|-----|
| 281–292 | Body text about strong Conway iteration operators is spliced into the middle of the `<concept_desc>` CCSXML tag. The tag should just contain `Theory of computation~Type theory` but instead contains a large chunk of paper content before the closing tag. | Remove the spliced content from the XML block. It appears to belong elsewhere in the paper (or in the full version `complete-refinement-ssa.tex`). |

### Typos

| Line | Issue | Fix |
|------|-------|-----|
| 357 | `Peephole rewrties` | `Peephole rewrites` |

---

## 2. `denotational-semantics-of-ssa.tex` — The Denotational Semantics of SSA

### Corrected expression equations and completeness

This is the maintained LaTeX source for the equality calculus in the expression
completeness theorem at `69a8126`, line 4408. The arXiv entry points to the
`debruijn-ssa` mechanization, whose artifact branch contains Lean. The separate
`complete-refinement-ssa.tex` submission presents directed substructural
refinement. The thesis LambdaIter chapter also presents a separate iterative
calculus. The repository and publication records identify no standalone
LambdaIter manuscript governing this theorem. [arXiv v2](https://arxiv.org/abs/2411.09347v2) · [artifact branch](https://github.com/imbrem/debruijn-ssa/tree/toplas-artifact)

- The rule figures now use the right summand type in `case`, both primed
  components in pair congruence, explicit primitive congruence, capture-avoiding
  substitution of the pure argument into the body in unary beta, and the
  product's two component types in `let1-let2`. In `let1-abort`, the scrutinee
  must be the premise `a : 0`; the printed `b` is a continuation under `y : A`.
  The corrected rule with `b = y`, bracketed by let eta, gives
  `abort a ≈ let x = a; abort x` even at an impure bound. The pinned Lean
  mechanization already uses this conversion in `Eqv.seq_zero` and
  `Eqv.packed_abort_den`. [Pinned rewrite](https://github.com/imbrem/debruijn-ssa/blob/316bd9a6511d165b5d1d0042956a72e0f5547091/DeBruijnSSA/BinSyntax/Syntax/Rewrite/Term/Step.lean#L28) · [Pinned abort calculation](https://github.com/imbrem/debruijn-ssa/blob/316bd9a6511d165b5d1d0042956a72e0f5547091/DeBruijnSSA/BinSyntax/Rewrite/Term/Compose/Sum.lean#L446)
- Silmaril's `PaperExpression.Wf` uses invariant types, a common upper effect
  bound, and bottom-annotated binders. The displayed manuscript contexts are
  the all-bottom instance. Its `Source.Eqv` uses a structurally initial pure
  slot for the initial rule. Such a slot gives a pure term of type `0` by
  destructuring a product or casing on a sum of initial types. Conversely,
  given any pure `e : 0`, let-bind it to a fresh variable, use initiality
  under that binder, and eliminate the let by pure beta on each side. Thus
  the written pure-witness form and the slot-based form generate the same
  initial equations. [Written typing](https://github.com/hiloopai/silmaril-lean/blob/570a0b75f62f4cab39908f86596e8f08d2ff1fa3/Silmaril/SSA/Isotope/LetIter/PaperExpression/Defs.lean#L70) · [Source equations](https://github.com/hiloopai/silmaril-lean/blob/570a0b75f62f4cab39908f86596e8f08d2ff1fa3/Silmaril/SSA/Isotope/LetIter/PaperExpression/Source/Defs.lean#L15)
- Native exact LetIter has a genuine missing equation. `closedReflection_fails`
  separates `abort (op true ())` from its sequenced form in the exact
  quotient despite equality of their categorical denotations. `AbortEquiv`
  adds the two orientations as typed primitive steps. The corrected written
  calculus derives them already. The thesis's pure let distribution over
  abort also gives the equation for a pure scrutinee by let eta. Its directed
  distribution rule carries a polarity, a mover premise, and an unrestricted
  effect quantity. The abort calculation here uses symmetric equality with
  no such refinement premises. [Native obstruction #2522](https://github.com/hiloopai/silmaril-lean/pull/2522) · [Repair #2670](https://github.com/hiloopai/silmaril-lean/pull/2670) · [Source derivation #2894](https://github.com/hiloopai/silmaril-lean/pull/2894) · [Thesis abort rules](https://github.com/imbrem/thesis/blob/69a8126f2d3eb6d32050e0bd9511251b33dbcea7/thesis/type-theoretic-ssa/lambda-iter/theory.typ#L723)
- The paper's expression models are distributive Freyd categories with a
  wide pure subcategory and shared finite coproducts, including the empty
  coproduct. The top-effect syntactic model takes the image of pure arrows
  under effect weakening as its wide pure subcategory. Native categorical
  validity theorems quantify over typing-coherent strong Elgot Freyd models
  with shared tensor, central unit, and pure interpretations of pure
  primitives. The first theorem uses the signature universe for objects and
  homs. The locally small version uses small signatures, `Type 1` objects
  and `Category.{0}` homs. Both allow arbitrary finite bound contexts and
  empty free context. The named variant additionally allows free contexts
  with all slots addressable by name. The conclusion is native `AbortEquiv`.
  [Same universe #2753](https://github.com/hiloopai/silmaril-lean/pull/2753) · [Locally small #2759](https://github.com/hiloopai/silmaril-lean/pull/2759) · [Named #2778](https://github.com/hiloopai/silmaril-lean/pull/2778)
- Fixed-bound packing and unpacking are inverse. Reflecting equality after
  weakening to top additionally requires injectivity on the packed hom-set.
  Native validity and reflection of individual native generators leave open
  proofs with above-bound or iterative intermediate terms. The mixed-signature
  conservativity theorems handle arbitrary native intermediates with two
  written endpoints at their original bound. #3163 covers atomic results,
  #3190 covers arbitrary result types, and #3201 covers arbitrary pure finite
  contexts. The first two require pure atomic inputs. All use decidable base
  sorts and finite-arity primitives with atomic arguments and either an
  atomic result or a binary sum of atomic payloads, with non-bottom sum
  instructions. Empty result endpoints are impossible at atomic inputs
  under these hypotheses. The two directions at top and at the original
  bound imply injectivity for the supported signature. General primitive
  profiles, including pure sum instructions and arbitrary compound or
  empty primitive endpoints, require a further source reflection argument
  or a direct proof of effect-weakening injectivity. [Fixed-effect quotient #2837](https://github.com/hiloopai/silmaril-lean/pull/2837) · [Atomic results #3163](https://github.com/hiloopai/silmaril-lean/pull/3163) · [Structured results #3190](https://github.com/hiloopai/silmaril-lean/pull/3190) · [Pure contexts #3201](https://github.com/hiloopai/silmaril-lean/pull/3201)
- The opt-in intrinsic API in #3218 exposes `abortClass_eq_iff` for
  `AbortEquiv pe` at fixed contexts, result type, and endpoint effect bound.
  The default thesis `Syn.setoid` uses exact `LocallyNameless.Eqv`.
  At bottom purity, `abortClass_ofLowering_eq_iff` restates #3201 as
  equality of intrinsic classes under the same hypotheses. Identifying
  these classes with the paper's syntactic expression model is a separate
  comparison. [Pinned intrinsic API](https://github.com/hiloopai/silmaril-lean/tree/936ebcfcb7d19c28387a3d2ac441da1770ff4b29/Silmaril/SSA/Isotope/LetIter/AbortSequence/Intrinsic)
- The native nonrepresentability theorem uses an iterate that makes a
  visible sum request, returning on a left reply and looping on a right
  reply. It has observable prefixes of unbounded length. Each candidate
  written expression has a finite visible-depth bound in the same model.
  This excludes a readback for that native endpoint. Source-to-source
  conservativity compares two endpoints in the image of the translation.
  [Nonrepresentability #3152](https://github.com/hiloopai/silmaril-lean/pull/3152)

### Typos/Spelling Errors

| Line | Issue | Fix |
|------|-------|-----|
| 287 | `progam` | `program` |
| 306 | `millenium` | `millennium` |
| 567 | `We can we intuitively` | `We can intuitively` (duplicate "we") |
| 568 | `it sunique definition site` | `its unique definition site` |
| 647 | `requring` | `requiring` |
| 1607 | `substititon` | `substitution` |
| 2637 | `auxilliary` | `auxiliary` |
| 3038 | `reased` | `erased` |
| 3381–3382 | `Kliesli` (x2) | `Kleisli` |
| 5405 | `oF` | `of` |
| 7641 | `substitututions` | `substitutions` |

### Grammar/Missing Words

| Line | Issue | Fix |
|------|-------|-----|
| 892 | `many of techniques` | `many of the techniques` |
| 1909 | `it's` (possessive) | `its` |
| 2215 | `it's` (possessive) | `its` |
| 2219 | `it's` (possessive) | `its` |
| 3385 | `In particularly` | `In particular` |
| 3762 | `An distributive` | `A distributive` |
| 4436 | `given by given by` | `given by` (duplicate) |
| 8819 | `that that` | `that` (duplicate) |

### Mathematical Errors

| Line | Issue | Fix |
|------|-------|-----|
| 1505 | Substitution lemma (d): `\lbsubst{[\gamma]\sigma}{\Delta}` | Context argument appears swapped; should use `\Gamma` |
| 1538 | `[\lupg{\Gamma}_\Xi]` | Should be `[\lupg{\gamma}_\Xi]` (lowercase gamma = substitution, not context) |
| 2613 | `(\lhyp{\kappa_j}{B_j},)_{j \in I}` | Index set should be `J`, not `I` |
| 4952 | `d_A + B` | Should be `d_{A + B}` (subscript should include whole sum type) |
| 5571 | `P \lor C` | Should be `P \lor Q` (consistent with surrounding text) |
| 5649 | `\pi_r` typed as returning `A` | Should return `B` — right projection from `A \otimes B` |
| 6279 | `[R \otimes \iota_r, R \otimes \iota_l]` | Likely swapped: `[R \otimes \iota_l, R \otimes \iota_r]` |
| 7815 | `[\gamma, x \mapsto x]c` | Should be `[\gamma, y \mapsto y]c` — this is the `y : B` branch |

### LaTeX Errors

| Line | Issue | Fix |
|------|-------|-----|
| 1261 | Double period `..` | Remove one period |
| 4020/4023 | `\wbranch{\ell_i}{x_i}{t_i},)_i` | Missing opening parenthesis |
| 6500 | Stray backslash: `; \alpha \` | Remove trailing backslash |
| 7595 | Unmatched closing `)` | Fix parenthesization |
| 8562/8567 | Missing `\dnt{...}` wrapper around `\hasty` | Add `\dnt{}` |
| 8683 | `;\iota_r` inside `\dnt{...}` | Should be outside: `\dnt{...};\iota_r` |

### Content Issues

| Line | Issue |
|------|-------|
| 4426 | Missing word: `Objects $|\ms{Th}(\Gamma, \ms{L})|$ types` — missing "are" |
| 5879 | Incomplete sentence: `Note that the base case...` appears cut off |
| 8258 | Incomplete sentence ending with `since` followed by new `\item` |

---

## 3. `complete-refinement-ssa.tex` — A Complete Refinement System for Substructural SSA

### Paper build compatibility

The papers use `thmtools` for named theorem restatements. LaTeX 2026-06-01
also creates sibling-counter aliases, conflicting with `thmtools`' alias setup
([upstream issue #75](https://github.com/muzimuzhi/thmtools/issues/75)). The shared
`paper-theorems.sty` compatibility wrapper retains theorem naming and restatement
hooks while leaving alias creation to the new kernel. Older formats retain the
original package behavior. This fixes the `\c@conjecture already defined` error
reported by PR CI before reaching the corrected refinement rules.

### Corrected refinement-rule formation

The following corrections were checked while mechanizing the written calculus.
Line numbers in this subsection refer to commit
`3691b30e7a4e2f9cd263a9f6701507329b457d6b`. They are applied to the
LaTeX source and the corresponding Typst imports; unrelated entries below
remain an audit ledger, not a claim that all listed issues are fixed.

| Rule / original lines | Correction | Reason |
|---|---|---|
| `let1-beta`, 1177–1188; `let1-beta^p`, 1414–1424 | Use `alquant(Gamma^q_l)` in the resource bound. | This is the context typing the substituted expression `a`; `Gamma^q_r` types the body. |
| Both beta rules | Require the body to type under the ordinary binder `x : A` as well as `x : A^q`. | The former constructs the let-expression; the latter justifies substitution at the specified usage. Neither premise subsumes the other for arbitrary signatures. |
| Symmetric `let1-beta`, 1182 | Replace the undefined unpolarized effect quantity by the meet of its positive and negative quantities. | The equation uses both directed beta rules. |
| `let1-beta^p`, 1418; `unif^p`, 1519; `simp-unif^p`, 3354 | Add polarity `p` to the mover relation. | The negative rule requires the dual mover, as specified by the effect-system definition and the surrounding beta discussion. |
| `unif^p`, 1538 | Change the result type of the `S`-state body from `C + A` to `C + S`. | Its recursive summand must be the loop state `S`. |
| `simp-unif^p`, 3372 | Change the result type of the `S`-state body from `B + A` to `B + S`. | Same state-type check as full uniformity. |
| Typst full and simplified uniformity | Restore the context-splitting, unrestricted-context, iterable-effect, and typing side conditions. | These were present in the LaTeX `where` clauses but omitted from the imports. |

The categorical Elgot definition is also made explicitly asymmetric: the left
loop body has effect `epsilon`, the simulation map has effect `eta`, and the
right loop body is unrestricted. Its mover premise is `eta rightmove^p epsilon`,
matching the written rule. The original wording about uniformity *of the
subcategory* can be read as bounding both loop bodies, which does not cover the
rule's unrestricted `b'` and exit continuation `c`. This correction strengthens
the categorical requirement to match the calculus; it is not asserted to follow
from the narrower condition. Effect membership is explicitly not closed under
refinement, so the missing bound cannot be inferred from the premise inequality.

The additional beta formation premise is substantive. Take a linear type `A`,
a pure primitive `f : 1 -> A`, `a = f ()`, and body `b = ()` with binder quantity
zero. The quantitative body and the corrected resource bound hold in the empty
outer context. But `let x = f (); ()` cannot type under the ordinary let rule:
its default binder `x : A` cannot be discarded. The signature definition places
no quantity compatibility restriction on primitives. Explicit ordinary-binder
body typing excludes this case without adding such a restriction.

A separate issue remains open: the literal substitution-cons premise can reject
identity substitutions. For linear `A` and target context `x : A^top`, it demands
`top <= alquant(x : A^top) = linear`. Thus closure under the printed pure
substitutions alone must not be used to infer arbitrary rewrite-rule weakening.
The formal development states structural stability separately. Changing the
substitution premise to an effective target quantity would require a separate
metatheory audit; this correction does not make that change.

### Corrected directed copying condition

The model definition's copying condition now requires only
`f ; Delta_B <=^p Delta_A ; (f left-tensor f)`. The additional equality with
the right evaluation order has been removed, and the syntactic-model proof's
use of directed beta now carries the relation `<=^p` instead of `=`. These
corrections are synchronized in the categorical and appendix Typst imports.

A single directed copying inequality does not itself imply that equality.
For monotone computations with inflationary natural-number state, evaluating
once and copying the result is pointwise below both repeated evaluation orders.
In particular, `tick(s) = (s, s + 1)` gives `((s, s), s + 1)` after one
evaluation, versus `((s, s + 1), s + 2)` and `((s + 1, s), s + 2)` for the two
orders. The latter are unequal and incomparable. This is a local counterexample
to the proposed implication, not a claim that an interpretation of the entire
iterative calculus in this state model has been established. Exchange requires
a separate hypothesis; the syntactic-model argument only supplies the directed
copy law. The corrected model class is correspondingly weaker. The native
refinement rules are unchanged.

### Typos/Spelling Errors

| Line | Issue | Fix |
|------|-------|-----|
| 279 | `Our type theory is very rich one` | `Our type theory is a very rich one` (missing "a") |
| 332 | `then substitution is then a valid` | `then substitution is a valid` (doubled "then") |
| 382 | `Furtheremore` | `Furthermore` |
| 384 | `occurences` | `occurrences` |
| 425 | `the more dependent the are` | `the more dependent they are` |
| 431 | `assigment` | `assignment` |
| 472 | `multplicative` | `multiplicative` |
| 829 | `Becaise` | `Because` |
| 843 | `behinds the` | `behind the` |
| 1218 | `is corresponds to` | `corresponds to` (extra "is") |
| 1697 | `correpond` | `correspond` |
| 1714 | `intepret` | `interpret` |
| 2262 | `intepret` | `interpret` |
| 3027 | `lineary` | `linearity` |
| 3160 | `guve` | `give` |
| 3573 | `partiuclar` | `particular` |
| 6122 | `Strengh` | `Strength` |
| 6272 | `requires us to distributive over` | `requires us to distribute over` |

### Mathematical Errors

| Line | Issue | Fix |
|------|-------|-----|
| 2085 | `\mc{C}_\epsilon \subseteq \mc{E}` | Should be `\mc{C}_\epsilon \subseteq \mc{C}` — subcategories of C, not the effect system E |
| 3083–3084 | `\lambda p . \ms{if}\;p \in s\;\ms{then}\;s \setminus p\;\ms{else}\;\ubeff` | Missing state parameter — `s` is used in body without being bound |
| 6115 | `h^\uparrow\;f \tref g ; B + h^\uparrow` | Missing semicolon: `h^\uparrow ; f \tref g ; B + h^\uparrow` |
| 6117 | Same: `h^\uparrow\;f \antitref ...` | `h^\uparrow ; f \antitref ...` |
| 6423 | `g ; [\ms{id}, h ; f_i] \supseteq ... = g^\dagger` | Should end with `g_{i+1}` not `g^\dagger` (this is an induction step; compare with correct equation on line 6414) |

### LaTeX Errors

| Line | Issue | Fix |
|------|-------|-----|
| 2146 | `as follows: \subiterexp{}:` | Remove redundant trailing `\subiterexp{}:` |
| 2259 | `to the the underlying` | `to the underlying` (doubled "the") |
| 4101 | `$((), y))$` | `$((), y)$` (extra closing paren) |
| 4199 | `$\letexpr{((u_1, u_2), (u_3, u_4)}{...$` | Missing closing paren in pattern: `((u_1, u_2), (u_3, u_4))` (also lines 4249, 4299) |
| 5024 | `$\dnt{lwk{\Gamma}{...}{...}}$` | Missing backslash: `$\dnt{\lwk{...}}$` (also line 5041) |
| 5026 | `and , we have that` | Incomplete — text missing between "and" and the comma |
| 5680 | `\lwk` macro has malformed brace grouping | Second argument not properly enclosed |
| 6121–6122 | `\item \emph{Strengh}:` appears after `\end{itemize}` | Strength item is outside the itemize environment — move `\end{itemize}` after line 6123 |

### Logical/Notation Inconsistencies

| Line | Issue |
|------|-------|
| 1769–1770 | Left/right unitor definitions swapped vs standard convention (same issue as in paper 1) |
| 1158 vs 1197 | Two different substitution notations used: prefix `[x/a]b` vs postfix `b[a/x]` |
| 6327 vs 6331 | Inconsistent subscript font for Brookes monad: `\ms{c}` vs `\mc{C}` |
