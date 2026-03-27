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
| 1337 | Case typing rule: right branch has `\bhyp{y}{A}` | Should be `\bhyp{y}{B}` — when casing on `A + B`, right branch binds type `B` |
| 1505 | Substitution lemma (d): `\lbsubst{[\gamma]\sigma}{\Delta}` | Context argument appears swapped; should use `\Gamma` |
| 1538 | `[\lupg{\Gamma}_\Xi]` | Should be `[\lupg{\gamma}_\Xi]` (lowercase gamma = substitution, not context) |
| 1673 | Pair congruence rule: RHS is `(a', b)` | Should be `(a', b')` — both components primed |
| 1748 | Beta rule states `[b/x]a` | Should be `[a/x]b` — substitutes `a` for `x` in body `b` |
| 1779 | `A \times B` in let2-let2 rule | Should be `A \otimes B` (tensor product, consistent with rest of paper) |
| 1780 | `\bhyp{y}{C}` in let2-let2 rule | Should be `\bhyp{y}{B}` (second component of tensor) |
| 1802 | `\labort{b}` on RHS | Should be `\labort{a}` — aborting on the value of type `0` |
| 2613 | `(\lhyp{\kappa_j}{B_j},)_{j \in I}` | Index set should be `J`, not `I` |
| 3179–3180 | Left and right unitors swapped: `\lambda_A : A \otimes I \to A` and `\rho_A : I \otimes A \to A` | Standard convention: `\lambda_A : I \otimes A \to A` (left), `\rho_A : A \otimes I \to A` (right) |
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
