import Isotope.LambdaSeq.Models.Monadic.Alg
import Isotope.LambdaCase.Models.Monadic.Alg
import Isotope.LambdaIter.Models.Monadic.Nondet

/-!
# Where nondeterminism stops being a model: the boundary is iteration

This module assembles the three-way result, all of it at **one** signature
(`Isotope.LambdaIter.Monadic.raySig`), **one** interpretation of its types
(`rayInterp`) and **one** interpretation of its single instruction (the
two-way branching ray `n ↦ {inl n, inr (n + 1)}`).  Only the monad changes.

| calculus | finite nondeterminism `FinSet` | countable nondeterminism `CSet` |
|---|---|---|
| lambda-seq  | `finSeqAlg` — an algebra | `csetSeqAlg` — an algebra |
| lambda-case | `finCaseAlg` — an algebra | `csetCaseAlg` — an algebra |
| lambda-iter | **impossible** (`finSet_not_alg_lambdaIter`) | `csetIterAlg` — an algebra |

## Why the boundary falls exactly at iteration

The monadic bridge is stacked by hypothesis strength, and the stack is tight:

* `LambdaSeq.Alg.ofSeqModel` needs `[Monad m]` and `[LawfulMonad m]` only — it
  never mentions a type former, let alone an iteration operator.
* `LambdaCase.Alg.ofModel` adds the four type-former equivalences and
  `[InjectiveFormers S.Ty]`.  It still needs **no** `Iterate` and **no** Elgot
  law: neither the soundness proof (lambda-case has no iteration axiom) nor
  the coherence proof (whose coupling argument only has to traverse the
  first-order formers) consults one.
* `LambdaIter.Alg.ofModel` adds `[Iterate m]` and `[LawfulElgotMonad m]`.

`FinSet` (and Mathlib's `Finset`) is a lawful monad, so it clears the first two
bars.  It cannot clear the third, and not merely because no `LawfulElgotMonad`
instance happens to have been supplied: `Isotope.Elgot.Nondet` proves that
**none exists**, since the reflexive-transitive closure of a finitely branching
relation need not be finitely branching.  `CSet` clears all three, because a
countable union of countable sets is countable.

The negative half is therefore not "the bridge does not apply".  It is
`Isotope.LambdaIter.Monadic.finSet_not_alg_lambdaIter`: **no** iteration
operator on `FinSet`, lawful or not, makes the standard finite-nondeterministic
operations into an algebra of the lambda-iter presentation.  Soundness for the
one axiom `IterationAxiom.fixpoint`, at the one term `iter x (step x)`, already
forces the Elgot fixpoint law at the ray body, and
`Isotope.Elgot.Nondet.FinSet.no_fixpoint` refutes that.
`Isotope.LambdaIter.Monadic.csetLoop_infinite` exhibits the obstruction
concretely: in the countable model that loop denotes the whole upper set of its
start state.

## Honest boundary

* The negative statement is at the level of the *laws* and of the *intended
  interpretation*, and it has to be: `¬ Nonempty (LambdaIter.Alg raySig)` is
  false (a terminal algebra always exists), and `¬ Nonempty (Iterate FinSet)`
  is false too (`FinSet.nonempty_iterate`).  See that theorem's docstring for
  exactly what is quantified over.
* The positive results are algebras of the *presentations*, i.e. objects of
  `Alg`; nothing here builds a Freyd or Elgot category.
* The `Finset` analogue is recorded in `Isotope.Elgot.Nondet` at the level of
  the monad only; this file's algebras are stated for the decidability-free
  `FinSet`.
-/

namespace Isotope.LambdaSeq.Monadic

open Isotope.Elgot
open Isotope.Elgot.Nondet
open Isotope.LambdaIter (Sig TypeFormers)
open Isotope.LambdaIter.Monadic (raySig rayInterp finRayModel csetRayModel)

/-! ### Finite nondeterminism models the iteration-free calculi -/

/-- **Finite nondeterminism is a model of lambda-seq.**  Only `[Monad FinSet]`
and `[LawfulMonad FinSet]` are used. -/
def finSeqAlg : LambdaSeq.Alg.{0, 0} raySig :=
  LambdaSeq.Alg.ofSeqModel finRayModel.toSeqModel

/-- **Finite nondeterminism is a model of lambda-case.**  No iteration operator
and no Elgot law is used; the extra hypotheses over lambda-seq are the four
type-former equivalences and injectivity of the formers. -/
def finCaseAlg : LambdaCase.Alg.{0, 0} raySig :=
  LambdaCase.Alg.ofModel finRayModel

/-! ### Countable nondeterminism models all three -/

/-- Countable nondeterminism is a model of lambda-seq. -/
def csetSeqAlg : LambdaSeq.Alg.{0, 0} raySig :=
  LambdaSeq.Alg.ofSeqModel csetRayModel.toSeqModel

/-- Countable nondeterminism is a model of lambda-case. -/
def csetCaseAlg : LambdaCase.Alg.{0, 0} raySig :=
  LambdaCase.Alg.ofModel csetRayModel

/-- **Countable nondeterminism is a model of lambda-iter** — the case finite
nondeterminism provably cannot supply. -/
abbrev csetIterAlg : LambdaIter.Alg.{0, 0} raySig :=
  Isotope.LambdaIter.Monadic.csetIterAlg

/-! ### The negative half, restated here for the record -/

/-- **Finite nondeterminism is not a model of lambda-iter.**  See
`Isotope.LambdaIter.Monadic.finSet_not_alg_lambdaIter` for the precise
quantification and for why a bare `¬ Nonempty` statement would be false. -/
theorem finSet_not_alg_lambdaIter :
    ¬ ∃ (I : Iterate FinSet.{0}) (X : LambdaIter.Alg.{0, 0} raySig),
        X.toOps = @Isotope.LambdaIter.Monadic.ops raySig FinSet.{0} _ I
          finRayModel :=
  Isotope.LambdaIter.Monadic.finSet_not_alg_lambdaIter

/-! ### The finite algebras are not terminal -/

/-- Singletons determine their element, so `pure` is injective on `FinSet`. -/
theorem finSet_pure_inj {A : Type} {x y : A}
    (h : (pure x : FinSet.{0} A) = pure y) : x = y :=
  FinSet.mem_pure.mp (h ▸ FinSet.mem_pure.mpr (rfl : x = x))

/-- The booleans of the ray signature's type universe. -/
abbrev boolT : raySig.Ty :=
  TypeFormers.coprod (τ := raySig.Ty) TypeFormers.unit TypeFormers.unit

/-- The typing derivation of `inl ()` at the booleans, in lambda-case. -/
abbrev inlUnit : LambdaCase.LocallyNameless.HasType raySig.Instr
    (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty raySig.Ty)
    (.nil) (.inl .unit) boolT := .inl .unit

/-- The typing derivation of `inr ()` at the booleans, in lambda-case. -/
abbrev inrUnit : LambdaCase.LocallyNameless.HasType raySig.Instr
    (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty raySig.Ty)
    (.nil) (.inr .unit) boolT := .inr .unit

/-- **The finite-nondeterminism algebra of lambda-case is not terminal**: it
separates the two booleans, so `finCaseAlg` has genuine semantic content. -/
theorem finCaseAlg_denote_inl_ne_inr :
    finCaseAlg.denote inlUnit ≠ finCaseAlg.denote inrUnit := by
  intro h
  rw [finCaseAlg, LambdaCase.Monadic.ofModel_denote,
    LambdaCase.Monadic.ofModel_denote] at h
  have h' := congrFun h PUnit.unit
  rw [LambdaCase.Monadic.denote_inl, LambdaCase.Monadic.denote_unit, pure_bind,
    LambdaCase.Monadic.denote_inr, LambdaCase.Monadic.denote_unit,
    pure_bind] at h'
  have h2 := (finRayModel.coprodEquiv TypeFormers.unit TypeFormers.unit).symm.injective
    (finSet_pure_inj h')
  cases h2

/-- **A non-derivability result from the finite model**: the lambda-case
equational theory does not identify the two booleans of the ray signature. -/
theorem not_equiv_inl_inr :
    ¬ LambdaCase.LocallyNameless.Equiv (Φ := raySig.Instr) raySig.pureEff
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty raySig.Ty)
      (.nil) (.inl .unit) (.inr .unit) boolT := fun he =>
  finCaseAlg_denote_inl_ne_inr (finCaseAlg.sound inlUnit inrUnit he)

end Isotope.LambdaSeq.Monadic
