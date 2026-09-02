# Paper-to-Lean claim audit

Audit date: 2026-08-27. This report audits declarations, not filenames. Line
numbers refer to the checked-in paper sources. `ERRORS.md` corrections are part
of the statements below.

## Active thesis formalization boundary

The frozen-repository tables below remain implementation archaeology. The
active project at `formalization/thesis/` now contains a separate
`Isotope.LambdaIter` development and must be audited independently before
editing public mechanization claims. Source inspection at `5b3be1e` supports
the following deliberately narrow map:

| Thesis topic | Exact active evidence | Scope established by declaration inspection | Current class |
|---|---|---|---|
| Named and locally nameless `lambda_iter` syntax and typing | `Isotope/LambdaIter/Named/{Defs,Typing}.lean`; `LocallyNameless/{Syntax,Typing}.lean` | Syntax and typing judgments exist as separate variants. This is not an equivalence theorem between variants. | partial |
| Locally nameless weakening and typed substitution | `LocallyNameless/Typing.lean`, `HasType.weaken`; `TypingSubst.lean`, `HasType.rename`, `HasType.bsubst`, `HasType.instantiate` | Typing-preserving renaming/substitution infrastructure for the locally nameless calculus. | checked |
| Direct denotation and semantic substitution | `Semantics/Denotation.lean`, `denote`; `Semantics/Substitution.lean`, `denote_rename`, `denote_bsubst`, `denote_instantiate` | Denotation of locally nameless typed terms in the direct model and compatibility with the corresponding renaming, bound-substitution, and instantiation operations. | checked |
| Soundness of the locally nameless equational theory | `Semantics/Soundness.lean`, `sound`, `related_sound` | `sound` covers `LocallyNameless.Deriv` under its explicit lawful-model assumptions; `related_sound` transports the result through a relation respected by the model. It is not a completeness result. | checked |
| Direct/categorical agreement | `Semantics/Agreement/Full.lean`, `categorical_denote_eq` | Agreement of the two denotations for the implemented locally nameless term language and the concrete categorical construction used there. It does not establish initiality or arbitrary-model completeness. | checked |
| Generic categorical interfaces | `Semantics/Categorical.lean`, `TypeModel`, `InstructionModel`; `CategoryTheory/Monad/Kleisli.lean`, `toKleisliFreydCategory` | Interfaces and categorical infrastructure, including a Kleisli Freyd-category construction. No category of syntax models or initial object is declared. | partial |
| `lambda_SSA`, translations, refinement completeness, model equivalence | No matching active module/declaration found under `Isotope/` | These remain future formalization work; paper-reference repositories do not upgrade the active thesis claim. | missing |

No active `sorry`, `admit`, axiom declaration, or `unsafe` declaration was
found by source search under `formalization/thesis/Isotope/`; commented sketches
were excluded. This is not a kernel axiom audit. Before calling any row a
verified thesis capstone, preserve a successful `lake build Isotope` result and
`#print axioms` output for the exact declarations named above.

## Frozen baselines and build evidence

| Repository | Audited commit | Toolchain | Clean build / axiom evidence |
|---|---|---|---|
| `discretion` | `624b878a0e2a30c2bd01455f5db1e6e616c38a32` (submodule) | Lean `v4.20.0-rc5` | Blocked: the installed elan distribution has `lean` but no `lake` executable. No fresh `#print axioms` output is claimed. |
| `debruijn-ssa` | `316bd9a6511d165b5d1d0042956a72e0f5547091` (submodule) | Lean `v4.15.0-rc1` | Same environment blocker. Source inspection finds no active `sorry` in the cited capstone declarations; commented sketches are not evidence. |
| `sparky` | `82d782a8c37a05fd17a23bb6ed1d64945f5fbc61` (explicit upstream `main` HEAD) | Lean nightly `2023-06-20` | Not proof-complete: active `sorry`s occur in `PomIso`, `PomEquiv`, `PomReduce`, `SubPom`, and `OrderMonad`. No SSA-model construction exists. |
| `refined-ssa` | `956ba4208606c9afa3169333f72c79b850427c15` (explicit upstream `main` HEAD) | Lean `v4.16.0-rc2` | Partial development. It defines model interfaces and part of term denotation, but no refinement relation, soundness, completeness, or initial model. |

The two upstream commits are recorded explicitly because they are not thesis
submodules. They are snapshots for this audit, not reproducible dependency
pins. A clean build and `#print axioms` transcript must be added after the
toolchain restoration issues provide a working Lake binary.

## Classification key

- **checked**: an exact proof declaration covers the claim at the frozen source
  revision (subject to the historical-build caveat above).
- **partial**: material components exist, but not the full paper result.
- **interface-only**: definitions/typeclasses state the semantic structure but
  do not prove the result.
- **paper-only**: no corresponding Lean declaration was found.
- **contradicted**: the public mechanization claim is incompatible with the
  audited repository contents.
- **blocked**: source evidence is insufficient until a stated external blocker
  is resolved.

## Denotational semantics paper

Paper: `papers/isotope/denotational-semantics-of-ssa.tex`.

| Paper result (corrected statement) | Paper location | Exact Lean evidence; principal assumptions | Axioms | Class |
|---|---|---|---|---|
| Weakening preserves typing for expressions and regions. | 1392–1467 | `debruijn-ssa` `DeBruijnSSA/BinSyntax/Typing/Term/Basic.lean`, `Term.Wf.wk`; `Typing/Region/Basic.lean`, `Region.Wf.wk`. `EffInstSet`, ordered types/effects. | Pending executable Lake | checked |
| Well-typed variable substitution preserves expression typing. | 1470–1558; in the displayed substitution lemma, line 1505 must use context `\Gamma`, not `\Delta`; line 1538 uses substitution `\gamma`. | `Typing/Term/Subst.lean`, `Term.Wf.subst` and `Term.InS.subst`; corresponding region theorem in `Typing/Region/VSubst.lean`, `Region.Wf.vsubst`. | Pending executable Lake | checked |
| Well-typed label substitution preserves region typing. | 1559–1612 | `Typing/Region/LSubst.lean`, `Region.Subst.Wf` and `Region.Wf.lsubst`; typed wrappers `Region.Subst.InS`. | Pending executable Lake | checked |
| The rewrite relation is a congruence and substitution respects it. | 1635–1933, 2678–2729; corrected rules include `(a',b')` at 1673, `[a/x]b` at 1748, tensor/right-binder corrections at 1779–80, and `abort a` at 1802. | `Rewrite/Term/Setoid.lean`, `Rewrite/Region/Setoid.lean`; lifted operations in `Rewrite/{Term,Region}/Eqv.lean`; substitution congruence in `Rewrite/Term/Eqv.lean` (`Eqv.subst`) and `Rewrite/Region/Eqv.lean` (`Eqv.vsubst`, `Eqv.lsubst`). | Pending executable Lake | checked |
| The quotient syntax supports composition, products, coproducts, distributivity, and iteration equations. | 3096–3394, 4238–4430 | Internal syntactic operations and laws in `Rewrite/Term/Compose/*` and `Rewrite/Region/Compose/*`; e.g. `Region.Eqv.seq`, `coprod`, `distl`, `fixpoint`, `fixpoint_uniformity`. There is **no** Mathlib `Category`/model instance: `BinSyntax/CategoricalRewrite.lean` contains only namespaces. | Pending executable Lake | partial |
| Uniformity and the paper's dinaturality rewrite are available syntactically. | 2176–2729, 3385–94 | `Rewrite/Region/Setoid.lean`, `Region.InS.uniform`, `Region.InS.dinaturality`; quotient results `Region.Eqv.uniform`; `Structural/Letc.lean`, `Eqv.dinaturality_letc`. A more categorical `Eqv.fixpoint_dinaturality` is only commented out in `Compose/Elgot.lean`; therefore no generic Elgot-category theorem is checked. | Pending executable Lake | partial |
| Arbitrary-model denotation of `lambda_SSA` expressions/regions. | 3748–4078 | No model typeclass, interpretation function, or functor from syntax was found in `debruijn-ssa`. Its README expressly calls the categorical semantics “otherwise unformalized.” | n/a | paper-only |
| Soundness of semantic substitution in an arbitrary model. | 4125–4231 | No arbitrary-model denotation exists. The paper itself says at 399 that denotation and soundness of substitution are on paper. | n/a | paper-only |
| Soundness of the equational theory in every valid model. | 4241–4262 | No semantic equality theorem exists. `Term.Eqv.sound`, `Region.Eqv.sound`, and `Subst.Eqv.sound` in the respective `Eqv.lean` files are direct calls to `Quotient.sound`; they prove equality of quotient representatives, not semantic soundness. | Quotient kernel theorem only; no semantic capstone | paper-only |
| Initiality/completeness: quotient syntax supplies the syntactic initial-model construction. | 4265–4760 | Substantial construction in `Rewrite/Region/Structural/{Product,Sum}.lean` (packing/unpacking) and `Rewrite/Region/Compose/Completeness.lean`, including `Eqv.packed_br_den`, `packed_let1_den`, `packed_let2_den`, `packed_case_den`, and `packed_cfg_den`. These prove denotation-shape equalities **inside the syntactic quotient**. No category of models or unique model morphism is defined, so literal initiality and completeness with respect to all arbitrary models are not Lean theorems. | Pending executable Lake for the cited shape theorems | partial |
| `lambda_SSA` to ANF and lexical SSA is typing- and equivalence-preserving; reverse/interconversion correctness. | 2812–3093 | No `ANF`/`toANF`/`toSSA` definitions or correctness declarations were found in the audited repositories. Packing/unpacking is categorical-normal-form machinery, not the paper's ANF/SSA algorithm. | n/a | paper-only |
| SPARC TSO forms a valid SSA model. | 388, 396–99 and model section 4750–5160 | `sparky` at the recorded commit contains POM infrastructure only, with active proof holes. It has neither the SPARC TSO operations/obligations nor an SSA model interface/instance. | Not applicable; proof holes present | contradicted |

### Public-claim boundary

The abstract's “completeness proof has been mechanized” (line 234) and the
contribution claim that syntax forms the initial model (lines 396–99) are only
supportable in the narrower sense that the hard syntactic packing/unpacking and
shape equations are mechanized. Literal categorical initiality is not a Lean
declaration. The same contribution paragraph's claim that SPARC TSO forms a
valid model is contradicted by the audited `sparky` snapshot.

## Refinement paper

Paper: `papers/isotope/complete-refinement-ssa.tex`.

| Paper result (corrected statement) | Paper location | Exact Lean evidence; principal assumptions | Axioms | Class |
|---|---|---|---|---|
| Substructural contexts, weakening, renaming, and raw substitution algebra. | 700–1082, appendix 3311 onward | `refined-ssa` `RefinedSSA/Ctx.lean`, e.g. `Ctx.Wk.comp_assoc`, `Var.Ix.wk_comp`; `Syntax.lean`, `ren_comp`, `subst_comp`, and `Subst.instMonoid`. These are raw syntax/context results, not typing-preservation for the full calculus. | Pending executable Lake | partial |
| Categorical model interface for types, variables, instructions, effects, and refinement order. | 1656–2285; corrected effect subcategory at line 2085 is `C_epsilon subseteq C`. | `RefinedSSA/Model.lean`: `TyModel`, `VarModel`, `SigModel`; `Mon/Model.lean`: `MonModel`; hom-order assumption appears in term semantics. | Interface definitions | interface-only |
| Denotation of well-typed terms in an arbitrary model. | 2250–2382 | `Mon/Extrinsic/Semantics.lean`, `Term.MonD.den`, covers the constructors implemented by `MonD`; associated context semantics are in `Mon/Semantics/OptCtx.lean`. No regions/iteration/refinement semantics appear. | Pending executable Lake | partial |
| Soundness of substitution. | 2383–2423 | No theorem relating `Term.MonD.den` to syntactic substitution was found. | n/a | paper-only |
| Soundness of generated refinement. | 2427–2451 | No refinement judgment or validation theorem exists in `refined-ssa`. | n/a | paper-only |
| Completeness via the syntactic initial model. | 2457–2494 and appendix 3523–4040 | No syntactic model, model morphism, reflection theorem, or completeness declaration exists. The paper's line 3742 “see formalization” for chosen coproducts/initial object has no corresponding declaration in this repository. | n/a | paper-only |
| Directed Conway laws, strength, uniformity, and derivation of dinaturality. | 1869–2136; 3832–39 | No iteration operator occurs in `refined-ssa`; `discretion` supplies categorical infrastructure but not a refinement-calculus soundness theorem. Corrections at 6115/6117 and the induction target correction at 6423 do not change this status. | n/a | paper-only |
| `lambda_iter`/`lambda_SSA` interconversion preserves typing and refinement/equivalence. | 639–643 and appendices 4943–5680 | No SSA or ANF datatype/translation is present in `refined-ssa`; none is present in the other audited snapshots. | n/a | paper-only |
| ANF conversion and ANF-to-SSA correctness. | 4943–5680 | No declarations found. | n/a | paper-only |
| Release-acquire and TSO model obligations validate the advertised rewrites. | 2967–3219 and 6054–6448 | No such models occur in `refined-ssa`. `sparky` is incomplete POM infrastructure and has no refinement-model instance. | n/a | paper-only |

The sentence “many of the results in this paper have been mechanized” (line
459) is safe only if read as referring to infrastructure and partial term
semantics. It must not be used to claim mechanized refinement soundness,
completeness, iteration, interconversion, or memory-model validation.

## Corrections affecting audited statements

All mathematical corrections in `papers/isotope/ERRORS.md` were checked while
matching statements. The corrections that directly affect matrix rows are
spelled out above. The remaining corrections are local categorical/model
notation fixes and do not create Lean evidence. In particular, neither the
standard left/right-unitor correction nor the corrected right projection type
can turn the internal syntax API into an arbitrary categorical model.

## Required follow-up

1. Restore historical Lake executables and run clean builds at all four frozen
   revisions.
2. Add a small audit file per repository containing `#print axioms` for the
   exact capstones cited above; preserve the output in this report.
3. Implement an explicit generic SSA model/interpretation before using
   “semantic soundness” for any `Eqv.sound` declaration.
4. Treat SPARC TSO, refinement soundness/completeness, and ANF/SSA
   interconversion as new proof work, not ports of completed capstones.
