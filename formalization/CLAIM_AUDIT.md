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
| SPARC TSO pomsets, monad, and operations (narrow) | `Isotope/Pomset/*.lean`, `Pom.instMonoid`, `Pom.par_assoc`/`par_comm`/`par_one`, `PrePom.ofList_deq_iff`, `Pom.mk_seq_ne_mk_par`; `Isotope/Elgot/WS.lean`, `WS.instLawfulMonad`, `WS.instLawfulElgotMonad`; `Isotope/Elgot/TSO/*.lean`, `Buf.toPom_inj`, `Buf.peek_nil`/`peek_append_self`/`peek_append_other`, `pflush_kcomp_pflush`, `pflush_ne_pure`, `pflush_kcomp_read`/`read_kcomp_pflush`/`pflush_kcomp_write`/`write_kcomp_pflush`/`pflush_kcomp_fence`/`fence_kcomp_pflush`, `not_drainable_pure`, `not_drainable_iter`; `Isotope/CategoryTheory/Ide.lean`, `Ide.id_eq`, `PTSO.id_eq` | Finite pomsets modulo the delta-quotient with the paper's concatenation monoid; a monoid-generic complete Elgot monad `WS S M`; the TSO alphabet, buffers as linear pomsets (injectively), the buffer lookup, `pflush`/`read`/`write`/`fence`, idempotence of `pflush`, the `pflush` sandwich equations, the paper's own negative result that `pflush ; id ; pflush != id`, and `PTSO = Ide(Set_TSO, pflush)` as a Mathlib `Category`. Infinite pomsets, `trim`, the stream action, divergence/`P+`, fork-join parallel composition of morphisms, the validity post-filter, and the `Ide` inheritance chain (coproducts, Elgot, premonoidal, distributive, Freyd) are **not** formalised. **This row does not discharge the "SPARC TSO forms a valid SSA model" row in the denotational-semantics table below, which stays `contradicted`.** | checked |
| `lambda_SSA`, translations, refinement completeness, model equivalence | No matching active module/declaration found under `Isotope/` | These remain future formalization work; paper-reference repositories do not upgrade the active thesis claim. | missing |

No active `sorry`, `admit`, axiom declaration, or `unsafe` declaration was
found by source search under `formalization/thesis/Isotope/`; commented sketches
were excluded. This is not a kernel axiom audit. Before calling any row a
verified thesis capstone, preserve a successful `lake build Isotope` result and
`#print axioms` output for the exact declarations named above.

For the SPARC TSO row specifically, `lake build Isotope` succeeds at
`leanprover/lean4:v4.29.0-rc8` with Mathlib `v4.29.0-rc8`, and `#print axioms`
on the declarations named in that row reports only `propext`,
`Classical.choice`, and `Quot.sound` (`Classical.choice` enters solely through
Mathlib's `Equiv`/`Fintype` API). The module docstring of
`Isotope/Elgot/TSO.lean` carries the corresponding honest-boundary statement.

### The empty signature and its two model theorems

`Isotope/LambdaIter/Signature/Empty.lean` makes the empty base-type set
(`EmptyTy = Ty PEmpty`) and the empty instruction set (`EmptyInstr = PEmpty`)
first-class, shared verbatim by `lambda_{iter, seq, case}`;
`Subtyping/Semantics/Models/Empty.lean` proves that this signature has a model
in every monad and in every Freyd category, and
`Subtyping/Semantics/Models/CategoricalFree.lean` supplies the type model of
`Ty alpha` in an arbitrary cartesian value category with finite coproducts
(the previous categorical type model, `Categorical.ofTypeModel`, was hard-wired
to `V = Type v`).

| Claim | Exact evidence | Scope | Class |
|---|---|---|---|
| Empty base-type set and instruction set are first-class and shared by all three calculi | `LambdaIter/Signature/Empty.lean`: `EmptyBase`, `EmptyTy`, `EmptyInstr`, `EmptyEff`, `instHasTyEmpty`, `instHasEffEmpty`, `instSignatureEmpty`; `EmptyTy.instInfinite` | The universe is non-trivial (infinitely many types, no base types). `Models/Null.lean` is re-derived from it. | checked |
| Free categorical type model in an arbitrary value category | `Models/CategoricalFree.lean`: `Categorical.Free.typeModel`, `Categorical.Free.lawfulTypeModel`; `LambdaSeq.Semantics.Categorical.freeTypeModel` | Lawful in every cartesian monoidal `V` with finite coproducts. Type formers are interpreted on the nose, so all six laws are near-trivial. | checked |
| A model in every monad | `Models/Empty.lean`: `emptyTypeModel`, `emptyLawfulTypeModel`, `emptyInstructionModel`, and `EmptySignature.denote{Seq,Case,Iter}` | A total denotation exists for lambda-seq and lambda-case in every `[Monad m]`, and for lambda-iter in every `[Monad m] [Iterate m]`. The instruction half is vacuous (`PEmpty.elim`). | checked |
| A model in every Freyd category | `Models/Empty.lean`: `Categorical.emptyTypeModel`, `Categorical.emptyLawfulTypeModel`, `Categorical.emptyInstructionModel`, and `EmptySignature.denote{Seq,Case,Iter,IterExact}Freyd` | lambda-seq needs plain `FreydCategory`; lambda-case needs `DistributiveFreydCategory` (a plain Freyd category does **not** suffice); lambda-iter needs `StrongElgotFreydCategory`. | checked |

**Honest boundary for these four rows.** They are *interface* theorems. What is
proved is that the empty signature supplies a `TypeModel` and an
`InstructionModel`, hence a total `denote`, in every such frame. It is **not**
proved that every monad or every Freyd category is a *lawful* model in the
sense of validating the equational theory: that requires instances of
`LocallyNameless.Categorical.TypingCoherent` and of the `LawfulModel`-style
classes, and no such instance exists anywhere under `Isotope/` for these three
calculi. The instruction half of both theorems is vacuous by construction; the
genuine content of the categorical theorem is the type model. No soundness,
adequacy, initiality, or completeness statement is added by this work, and the
two gaps recorded elsewhere in this file — no category of models, no unique
model morphism, no initial object — remain open.

### Signatures, the total category, and reindexing

`Isotope/LambdaIter/Signature/Category.lean` makes signatures and their strict
morphisms a category; `Signature/Initial.lean`, `Models/HomOver.lean`,
`Models/Total.lean` and `Models/Reindex.lean` build the fibred picture over it.

| Claim | Exact evidence | Scope | Class |
|---|---|---|---|
| Signatures form a category | `Signature/Category.lean`: `Sig`, `Sig.Hom`, `Sig.instCategory` | Objects carry a type universe with its four formers, an instruction set with typing, an effect set with a pure effect. **No `Subtyping` component**; morphisms preserve the formers strictly. | checked |
| The empty signature is the initial object of `Sig` | `Signature/Initial.lean`: `Sig.empty`, `Sig.fromEmpty`, `Sig.uniqueFromEmpty`, `Sig.isInitialEmpty` | Existence and uniqueness both proved; the three components are separated (`fromEmpty_ty_unique` is freeness of `Ty PEmpty`, `fromEmpty_instr_unique` is emptiness of `PEmpty`, `fromEmpty_eff_unique` needs `eff_pure` *and* `EmptyEff` being a singleton). `Sig.ofNull_not_isInitial` records that emptiness of the base and instruction sets alone does not suffice. | checked |
| Pairs `(signature, model)` form a category | `Models/HomOver.lean`: `Alg.HomOver`, `HomOver.id`, `HomOver.comp`, `id_comp`, `comp_id`, `assoc`; `Models/Total.lean`: `Total`, `Total.Hom`, `Total.instCategory` | The Hom is defined directly, not as `Sigma g, X to g^* Y`; reindexing is only pseudofunctorial in the signature, so a Grothendieck construction over a strict functor is unavailable. | checked |
| The fibre over a fixed signature is the category of its models | `Models/Total.lean`: `Alg.homOverIdEquiv`, `Total.incl`, `Total.inclFaithful`, `Total.fibreEquiv` | **Near-tautological by construction**: the fibre is *defined* as the morphisms whose signature component is the identity. Its Lean content is `BoundCtx.map_id` plus one transport cancellation, and its docstring says so. | checked |
| The fibre inclusion is faithful but **not** full | `Models/Total.lean`: `Total.inclFaithful`, `Total.incl_not_full` | The non-fullness witness is explicit: the effect-collapsing endomorphism of `Sig.ofNull` acting on terminal models. This is the substantive statement neighbouring the tautological one. | checked |
| Reindexing along a signature morphism, contravariantly | `Models/Reindex.lean`: `Alg.Ops.reindex`, `proj`, `reindexEquiv`, `reindexMap`, `reindexMap_id`, `reindexMap_comp`; `Total.homEquiv` | Universal property (cartesian lift) and functoriality both proved. **At the level of `Alg.Ops` only** — see the boundary below. | checked |
| Initiality in the total category, conditionally | `Models/Total.lean`: `Total.isInitialOfFibrewise`; `Models/Reindex.lean`: `Total.isInitialOfReindex` | These are *reductions*, not initiality theorems: they say that an initial signature plus fibrewise uniqueness gives an initial object of `Total`. Their hypotheses are not discharged here. | interface-only |

**Honest boundary for these rows.**

1. **No object of `Total` is shown to be initial.** That needs a model whose
   maps out are unique, i.e. the quotiented syntax, which is not constructed on
   this branch. `Sig.uniqueFromEmpty` discharges the *signature* half of
   `Total.isInitialOfReindex` at `Sig.empty`; the model half is open.
2. **Reindexing is built for `Alg.Ops`, not for `Alg`.** An `Alg` additionally
   carries `coh` and `sound`, and discharging those for a reindexed model needs
   the functorial action of a signature morphism on the syntax and on the
   equational theory (`Tm.map`, `HasType.map`, `Pure.map`, the four axiom
   schemes, `Eqv.map`, and their commutation with `rename`, `bsubst` and
   `instantiate`). That action is not built here. So there is **no** proved
   functor `Alg T` to `Alg S`.
3. A "model" throughout this directory means an algebra of the equational
   presentation (`Alg`), whose `coh` and `sound` are *fields*. It does not mean
   a Freyd or Elgot category, and nothing here shows that a monad or a Freyd
   category gives such an algebra.
4. Signature morphisms carry no subtyping component. This is a deliberate scope
   decision recorded in `Signature/Category.lean`, not an oversight; it means
   the request's "type universe with its type formers and subtyping" is
   delivered without the subtyping half.

### The quotiented syntax, its category, and the three initiality statements

`Isotope/LambdaIter/Models/{Setoid,Syntax,SynCategory,SynCoproduct,SynIteration,SynElgot,Initial,SigAction,ReindexAlg,TotalInitial}.lean`
build the quotient of the exact (subtyping-free) lambda-iter syntax by its
equational theory `Eqv` and prove it initial.  These rows supersede items 1 and
2 above, and discharge the two gaps recorded elsewhere in this file ("No
category of syntax models or initial object is declared"; "No category of
models or unique model morphism is defined").

| Claim | Exact evidence | Scope | Class |
|---|---|---|---|
| `Eqv` induces a setoid on typable terms, and the quotient exists | `Models/Setoid.lean`: `Syn.Carrier`, `Syn.setoid`, `Syn.El`, `Syn.mk`, `Syn.ind`, `Syn.eqv_of_mk_eq` | The carrier is forced to be a subtype: `Eqv.refl` takes a typing derivation, so there is no setoid on raw `Tm`. Reflexivity is choice-free. | checked |
| The quotient is a model | `Models/Syntax.lean`: `Syn S : Alg S`, `Syn.denote_mk` | All twelve operations, iteration included, are `Quotient` lifts of the matching congruence rule of `Eqv`. `coh` and `sound` hold for structural reasons (proof irrelevance; `Quotient.sound`), not as theorems about lambda-iter. The theorem about lambda-iter is `Syn.denote_mk`. | checked |
| The one-variable quotient is a category | `Models/SynCategory.lean`: `SynCat`, `instCategory`, `id'_comp`, `comp_id'`, `comp_assoc` | Category laws only, from `letEta`, `letBeta` at `Pure.bv`, and `bindLet`. No premonoidal, monoidal or distributive structure. | checked |
| It has binary coproducts | `Models/SynCoproduct.lean`: `isColimitBinaryCofan`, `hasBinaryCoproducts`, `injl_desc`, `injr_desc`, `desc_uniq` | Coproducts in the whole (effectful) category. The **empty type is not shown to be initial**: `StructuralAxiom.emptyInitial` fires only on a scrutinee of the literal form `.abort a`, so it gives no route to `bv 0 ≈ abort (bv 0)`. Reported as a gap, not proved underivable. | checked |
| Iteration is well defined on quotient morphisms and satisfies three Elgot laws | `Models/SynCoproduct.lean`: `iterate`; `Models/SynIteration.lean`: `iterate_fixpoint`, `iterate_naturality`, `iterate_codiagonal`; `Models/SynElgot.lean`: the same three in Mathlib's `⨿` vocabulary, and `elgotCategory_of_hasFiniteCoproducts` | Fixpoint, naturality and codiagonal — verbatim the three fields of `CategoryTheory.ElgotCategory`. **Uniformity and strength are not proved**, and the `ElgotCategory` instance is *not* registered: it needs `HasFiniteCoproducts`, hence the missing initial object. Issue #57 therefore remains open. | partial |
| (a) For a fixed signature, the quotient is the initial model | `Models/Initial.lean`: `Syn.toHom`, `Syn.hom_eq_toHom`, `Syn.uniqueHom`, `Syn.isInitial` | Initiality **in `Alg S`**, the category of algebras of the presentation. | checked |
| Equational completeness | `Models/Initial.lean`: `Syn.eqv_of_denote_eq`, `Syn.denote_eq_iff_eqv` | Completeness **with respect to algebras** in `Type u`. Not completeness against Freyd or Elgot models. | checked |
| A signature morphism acts on typing and on the equational theory | `Metatheory/MapInstr.lean`: `Tm.mapInstr` and its commutations, `Pure.mapInstr`, the three axiom schemes; `Models/SigAction.lean`: `HasType.map`, `Eqv.map` | This is the action item 2 above records as missing. | checked |
| Reindexing lifts from operations to algebras | `Models/ReindexAlg.lean`: `Alg.Ops.reindex_denote`, `Alg.reindex` | `coh` and `sound` of the reindexed algebra come from those of the target through `Eqv.map`. | checked |
| (b) The quotient over the empty signature is the initial object of the total category | `Models/TotalInitial.lean`: `Total.synEmpty`, `Total.synEmptyIsInitial` | Derived from `Sig.uniqueFromEmpty`, (a), and `Total.isInitialOfReindex`; not reproved. Initial among pairs (signature, algebra of the presentation). | checked |
| (c) The fibre over `𝟙 S` is `Alg S` | `Models/Total.lean`: `Total.fibreEquiv`, `Alg.homOverIdEquiv` | **Near-tautological by construction**, as its docstring says: the fibre is *defined* as the morphisms whose signature component is `𝟙`. The substantive neighbour is `Total.incl_not_full`. | checked |

**Honest boundary for this block.** Every occurrence of "model" above means
*algebra of the equational presentation*, whose `coh` and `sound` are fields of
the structure. None of these statements is about Freyd or Elgot categories, and
no monad or Freyd category is exhibited as such an algebra anywhere in this
repository; that would require instances of
`Semantics.Categorical.TypingCoherent` and `LawfulModel`, which do not exist.
In particular, soundness (`Subtyping/Semantics/Soundness.lean`, over a Freyd
frame and about `TypedEquiv.Deriv`) and the completeness above (over `Alg` and
about `Eqv`) do **not** quantify over the same model class, which is one of
issue #57's acceptance criteria and is still open. Also still open from #57:
uniformity, strength, packing/reflection, and the comparison with the
lambda-case fragment; and no quotient, initiality or completeness statement is
made for lambda-case or lambda-seq (issue #54).

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
