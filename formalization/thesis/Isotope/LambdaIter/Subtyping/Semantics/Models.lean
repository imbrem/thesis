import Isotope.LambdaIter.Subtyping.Semantics.Models.Free
import Isotope.LambdaIter.Subtyping.Semantics.Models.Null
import Isotope.LambdaIter.Subtyping.Semantics.Models.BitVec
import Isotope.LambdaIter.Subtyping.Semantics.Models.Nat

/-!
# Concrete type and instruction models

Until this directory the repository had **no** `TypeModel` instance at all, so
`Semantics.denote` and `Semantics.sound` could never be applied: every result
about them was conditional on hypotheses nothing satisfied.  Several honest
boundaries across the development record exactly that gap.  These are the first
instances that close it.

All three are instances of one construction, `Models/Free.lean`: an
interpretation `β : α → Type v` of the base types of `Ty α` extends uniquely to
an interpretation of every type, and of every proof-relevant subtyping
derivation, and the result satisfies `LawfulTypeModel`.

| model | base types `α` | base interpretation | instructions |
|---|---|---|---|
| `Null` | `Empty` | none | none |
| `BitVecModel` | `Nat` (widths) | `BitVec n` | `const`, `add`, `and`, `not`, `eqz` |
| `NatModel` | `Unit` | `Nat` | `zero`, `succ`, `add`, `case` |

Effects are the two-element lattice `Eff`, with `⊥ = Eff.pure`.  Every
instruction in all three signatures is pure, so `denotePure` is total and
`denote_pure` holds definitionally; the effectful `denote` is `pure ∘ denotePure`
in every monad.  This keeps the models usable with any `[Monad m]` while leaving
the effectful case genuinely open for a future signature with memory operations.

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
* **No soundness or adequacy result is instantiated.**  These models supply the
  `TypeModel`/`LawfulTypeModel`/`InstructionModel` instances the generic
  semantics asks for; connecting them to `Semantics.sound` at a concrete monad
  is separate work.
* **The instruction sets are deliberately small and total.**  They are chosen to
  be enough to exercise the interfaces, not to be a complete or canonical ISA.
  In particular the bitvector signature has no shifts, comparisons, or
  multiplication, and the natural-number signature has no subtraction or
  recursion combinator beyond `case`.
* **All instructions are pure**, so none of these models exercises the effectful
  half of `InstructionModel`.  A memory-operation signature over one of the weak
  memory models would.
-/
