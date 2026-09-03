import Isotope.LambdaIter.Subtyping.Semantics.Models.Free
import Isotope.LambdaIter.Subtyping.Semantics.Models.CategoricalFree
import Isotope.LambdaIter.Subtyping.Semantics.Models.Empty
import Isotope.LambdaIter.Subtyping.Semantics.Models.EmptyExamples
import Isotope.LambdaIter.Subtyping.Semantics.Models.Null
import Isotope.LambdaIter.Subtyping.Semantics.Models.BitVec
import Isotope.LambdaIter.Subtyping.Semantics.Models.Nat
import Isotope.LambdaIter.Subtyping.Semantics.Models.Brookes
import Isotope.LambdaIter.Subtyping.Semantics.Models.Brookes.Compile
import Isotope.LambdaIter.Subtyping.Semantics.Models.Brookes.SSA

/-!
# Concrete type and instruction models

Until this directory the repository had **no** `TypeModel` instance at all, so
`Semantics.denote` and `Semantics.sound` could never be applied: every result
about them was conditional on hypotheses nothing satisfied.  Several honest
boundaries across the development record exactly that gap.  These are the first
instances that close it.

The **empty signature** (`Models/Empty.lean`, over
`Isotope/LambdaIter/Signature/Empty.lean`) is the first-class version of the
former ad-hoc `Null` model: no base types, no instructions, one effect.  It
carries the two theorems that make it usable everywhere — a model in every
monad and a model in every Freyd category — and `Null` is now a named example
of it at a two-element effect set.  `Models/CategoricalFree.lean` is the
categorical counterpart of `Models/Free.lean`, giving a type model in an
arbitrary cartesian value category with finite coproducts.

All four set-valued models are instances of one construction, `Models/Free.lean`: an
interpretation `β : α → Type v` of the base types of `Ty α` extends uniquely to
an interpretation of every type, and of every proof-relevant subtyping
derivation, and the result satisfies `LawfulTypeModel`.

| model | base types `α` | base interpretation | instructions |
|---|---|---|---|
| `Empty` | `PEmpty` | none | none |
| `Null` | `PEmpty` | none | none |
| `BitVecModel` | `Nat` (widths) | `BitVec n` | `const`, `add`, `and`, `not`, `eqz` |
| `NatModel` | `Unit` | `Nat` | `zero`, `succ`, `add`, `case` |
| `BrookesModel` | `loc`, `val` | `Loc`, `Val` | `read`, `write` |
| `BrookesModel` (coarse) | `loc`, `val` | `Loc`, `Val` | `skip`, `assign`, `test` |

Effects are the two-element lattice `Eff`, with `⊥ = Eff.pure`.  Every
instruction of the bitvector and natural-number signatures is pure, so
`denotePure` is total and `denote_pure` holds definitionally; the effectful
`denote` is `pure ∘ denotePure` in every monad.  This keeps those models usable
with any `[Monad m]`.

`BrookesModel` is the exception, and is the reason the interface has an
effectful half at all.  Its two instructions are annotated `Eff.impure`, so
`denotePure` is vacuous, and they denote `SeqCst.read` and `SeqCst.write` in the
Brookes trace monad `SeqCst.Comp Loc Val` — a *fixed* monad, not an arbitrary
one.  It is the first model of this directory that is tied to a particular
monad, and the first whose instructions are not pure.

## The three-way comparison

* **`BitVecModel.bitTy_equiv`** — for every width `n`, `BitVec n` is isomorphic
  to the null-model type `bool ^ n` where `bool = 1 ⊕ 1`.  So the bitvector
  universe introduces no types the null universe lacks.
* **`Null.fintypeInterp`** — every null-universe type denotes a *finite* type.
* **`NatModel.natTy_not_null`** — hence no null type denotes anything isomorphic
  to `Nat`.  The natural-number model is therefore strictly richer, and the
  contrast with the bitvector case is not an accident of presentation.

## Honest boundary

* **The bitvector/null equivalence is proved only at the level of TYPES.**
  `bitTy_equiv` gives an isomorphism of interpretations; it does **not** show
  the two *models* are equivalent.  That additionally requires translating the
  instructions — `add`, `and`, `not`, `eqz` — into null-model terms and proving
  the translation preserves denotations, i.e. that bitvector arithmetic is
  definable from `1`, `⊕`, `⊗` and iteration.  Nothing here proves that, and
  the isomorphism above is deliberately stated as `Nonempty (… ≃ …)` rather
  than as a distinguished map, since the counting argument that produces it is
  not the structural map a translation would need.
* **Soundness is instantiated only at the Brookes model.**  The pure models
  supply `TypeModel`/`LawfulTypeModel`/`InstructionModel` instances but are
  never connected to `Semantics.sound` at a named monad; `BrookesModel` is.
* **The instruction sets are deliberately small and total.**  They are chosen to
  be enough to exercise the interfaces, not to be a complete or canonical ISA.
  In particular the bitvector signature has no shifts, comparisons, or
  multiplication, and the natural-number signature has no subtraction or
  recursion combinator beyond `case`.
* **`BrookesModel`'s fine-grained signature is sound, not complete.**
  Instantiating `Semantics.sound` at it gives `BrookesModel.brookes_sound`: the
  lambda-iter equational theory is sound for Brookes trace semantics.  It does
  not give the converse.
* **The fine-grained signature does *not* match Brookes's own `Com`, and this is
  now a theorem.**  `SeqCst.write` is atomic (`BrookesModel.write_eq_atom`), but
  the composite `read y >>= write x` is not: it admits traces whose store changes
  between the read and the write, so
  `BrookesModel.not_readWrite_le_den_assign` and
  `BrookesModel.readWrite_ne_den_assign` separate one concrete pair, assuming
  two distinct values; nothing here quantifies over compilers.  `Models/Brookes/Compile.lean` therefore ships a
  second, coarse-atom signature `CInstr` — whole `skip`s, assignments and tests —
  for which `BrookesModel.den_compile` does hold, and derives full abstraction
  against the operational contextual preorder of `Brookes/SeqCst/Op`
  (`BrookesModel.lambdaIter_fullAbstraction`).
* **The compilable fragment is narrow.**  It is closed, `unit`-typed at every
  slot, and never `let`-binds a control value; its image is exactly the
  `∥`-free, `await`-free sublanguage of `Com`
  (`BrookesModel.exists_compilable`, `BrookesModel.sequential_compile`).  No
  lambda-iter term is compiled to a *parallel* command: concurrency enters only
  through the contexts quantified over on the right-hand side of full
  abstraction.
* **The SSA bridge reaches the loop-free fragment only.**
  `Models/Brookes/SSA.lean` composes what exists: typing composes for the whole
  compilable fragment (`BrookesModel.compile_region_hasType`), the ANF leg
  composes for the whole fragment (`BrookesModel.anfDen_eq_den_compile`, with
  `BrookesModel.anf_fullAbstraction`), and the SSA leg composes for `skip`,
  `assign` and `;` (`BrookesModel.loopfree_region_denotes`, from the generic
  `SSABridge.straight_denotes`).  What is missing is the CFG case: `ToSSA`
  compiles a `case` to a one-block and an `iter` to a two-block control-flow
  graph, and contracting those back to the source `Elgot.iter` needs uniformity,
  codiagonal and a naturality theory for `renameVars` that does not exist here.
  Two further obstacles are structural, and are why even the loop-free result is
  a `RegionDenotes` rather than an equation: `Region.denote` is a
  `Classical.choice` pick whose uniqueness needs
  `RegionTypingCoherent`, and `LabelDen [unit]` is a colimit with no inverse for
  `labelInject 0`.
-/
