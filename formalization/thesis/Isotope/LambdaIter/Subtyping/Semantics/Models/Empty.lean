import Isotope.LambdaIter.Signature.Empty
import Isotope.LambdaIter.Subtyping.Semantics.Models.CategoricalFree
import Isotope.LambdaIter.Subtyping.Semantics.Models.Free
import Isotope.LambdaIter.Semantics.Categorical
import Isotope.LambdaCase.Semantics
import Isotope.LambdaCase.Semantics.Categorical
import Isotope.LambdaSeq.Semantics
import Isotope.LambdaSeq.Categorical

/-!
# The empty signature has a model in every monad and in every Freyd category

`Isotope.LambdaIter.EmptyTy` and `Isotope.LambdaIter.EmptyInstr` are the type
universe with no base types and the instruction set with no instructions.  This
file supplies every semantic interface the three calculi
`lambda_{iter, seq, case}` ask for, at the empty signature, in maximal
generality:

* **set-valued** — `emptyTypeModel` (from `Models/Free.lean`), lawful, and
  `emptyInstructionModel`, which exists for **every** `m` with a `Pure`;
* **categorical** — `emptyCategoricalTypeModel` (from
  `Models/CategoricalFree.lean`), lawful in **every** cartesian monoidal value
  category with finite coproducts, and `emptyCategoricalInstructionModel`,
  which exists for **every** functor `J`.

The six corollaries below are the two requested theorems, elaborated rather
than asserted: for each of the three calculi and each of the two frames, an
actual definition producing the denotation of an arbitrary typing derivation
over the empty signature.  Each is stated at the *weakest* structure the
corresponding `denote` actually consumes:

| calculus | monadic frame | categorical frame |
|---|---|---|
| λ-seq | `[Monad m]` | `[FreydCategory J]` (plus coproducts on `V`, see below) |
| λ-case | `[Monad m]` | `[DistributiveFreydCategory J]` |
| λ-iter | `[Monad m] [Iterate m]` | `[StrongElgotFreydCategory J]` |

Note that λ-case genuinely needs **more** than a plain Freyd category: its
`case` clause goes through `caseWithContext`, which uses
`DistributiveTensor.leftIso` and the inverse of `coprodComparison J`, and its
`abort` clause uses `emptyIsInitial`.  λ-seq is the only one of the three for
which a plain Freyd category suffices, which is why λ-seq has its own leaner
`TypeModel` asking neither for type-former isomorphisms nor for coproducts on
the value category.

## Honest boundary

These are **interface** theorems, and the qualifier matters.

* What is proved is that the empty signature supplies a `TypeModel` and an
  `InstructionModel`, hence a *total* denotation function, in every monad and
  in every Freyd category of the appropriate strength.  It is **not** proved
  that every monad or every Freyd category is a *lawful* model of λ-iter in the
  sense of validating the equational theory.  That needs instances of
  `LambdaIter.LocallyNameless.Categorical.TypingCoherent` and of the various
  `LawfulModel`-style classes; those exist only for the Kleisli category of a
  lawful Elgot monad
  (`Isotope/LambdaIter/Semantics/Kleisli/Model.lean`), not for a general Freyd
  category.  No statement of the form "every Freyd category is a model of
  λ-iter *up to the equational theory*" is made or implied here.
* The instruction half of both theorems is **vacuous by construction**:
  `EmptyInstr` is `PEmpty`, so `denote` on instructions is `PEmpty.elim` and
  every law about it holds by `PEmpty.elim`.  The instruction-model
  instances below are therefore tautologies, and are stated in the fully
  general form (any type model, any monad, any functor) precisely because
  nothing about the target is used.  The genuine content of the second theorem
  is the **type** model, `Categorical.Free.typeModel`, which is a real
  construction in an arbitrary value category.
* Nothing here says the empty *calculus* is interesting.  It says that the
  frame conditions of the semantics are satisfiable with no assumptions on the
  signature at all, which is what makes the empty signature a candidate initial
  object in a category of signatures.
-/

universe u v v₁ v₂ u₁ u₂ w

namespace Isotope.LambdaIter.Subtyping.Semantics

open CategoryTheory CategoryTheory.Limits

/-! ## The set-valued model, in every monad -/

/-- The set-valued interpretation of the empty type universe: `1`, `0`, `×`
and `⊕` on Lean types, with no base types to interpret. -/
@[reducible] def emptyTypeModel : TypeModel.{u, v} EmptyTy.{u} :=
  Free.typeModel (fun (a : EmptyBase.{u}) => a.elim)

attribute [instance] emptyTypeModel

/-- The empty type model is lawful: every operation of the `Subtyping`
interface receives its expected semantics. -/
instance emptyLawfulTypeModel : LawfulTypeModel.{u, v} EmptyTy.{u} :=
  Free.lawfulTypeModel _

/-- **A model in every monad (instruction half).**  The empty instruction set
has an instruction model over *any* type universe, effect set and monad.

Tautological by construction: `EmptyInstr` is `PEmpty`, so all three fields
are `PEmpty.elim`.  It is stated in this generality because nothing about the
target is used. -/
instance emptyInstructionModel {τ : Type u} [TypeFormers τ] [Subtyping τ]
    [TypeModel.{u, v} τ] [HasTy EmptyInstr.{w} τ] {ε : Type*}
    [HasEff EmptyInstr.{w} ε] [Bot ε] (m : Type v → Type v) [Pure m] :
    InstructionModel EmptyInstr.{w} τ ε m where
  denote f := f.elim
  denotePure f := f.elim
  denote_pure f := f.elim

end Isotope.LambdaIter.Subtyping.Semantics

namespace Isotope.LambdaIter.Subtyping.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V]
  [HasFiniteCoproducts V]

/-! ## The categorical model, in every Freyd category -/

/-- **A model in every Freyd category (type half).**  In *any* cartesian
monoidal category with finite coproducts, the empty type universe is
interpreted by `𝟙_ V`, `⊥_ V`, `⊗` and `⨿`.  This is the genuinely new content
of the second theorem: unlike the instruction half it is not vacuous. -/
@[reducible] noncomputable def emptyTypeModel :
    TypeModel EmptyTy.{u} V :=
  Free.typeModel (fun (a : EmptyBase.{u}) => a.elim)

/-- The empty categorical type model is lawful, with no hypotheses on `V`
beyond those needed to state it. -/
theorem emptyLawfulTypeModel :
    LawfulTypeModel EmptyTy.{u} V (emptyTypeModel.{u} (V := V)) :=
  Free.lawfulTypeModel _

/-- **A model in every Freyd category (instruction half).**  The empty
instruction set has a categorical instruction model over *any* type model and
*any* functor `J`.

Tautological by construction: the single field is `PEmpty.elim`. -/
instance emptyInstructionModel {C : Type u₂} [Category.{v₂} C]
    (J : Functor V C) {τ : Type*} [TypeFormers τ] [Subtyping τ]
    (M : TypeModel τ V) [HasTy EmptyInstr.{w} τ] :
    InstructionModel J M EmptyInstr.{w} where
  denote f := f.elim

end Isotope.LambdaIter.Subtyping.Semantics.Categorical

namespace Isotope.LambdaSeq.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits

/-- The λ-seq type model of the empty universe.  λ-seq's `TypeModel` is a
leaner class than λ-iter's — no type-former isomorphisms, no coproducts asked
of `V` — so this is the same two definitions viewed through a weaker
interface. -/
@[reducible] noncomputable def emptyTypeModel {V : Type u₁} [Category.{v₁} V]
    [CartesianMonoidalCategory V] [Limits.HasFiniteCoproducts V] :
    TypeModel LambdaIter.EmptyTy.{u} V :=
  freeTypeModel (fun (a : LambdaIter.EmptyBase.{u}) => a.elim)

/-- The empty instruction set has a λ-seq instruction model over any type
model and any functor.  Tautological: the field is `PEmpty.elim`. -/
instance emptyInstructionModel {V : Type u₁} {C : Type u₂} [Category.{v₁} V]
    [Category.{v₂} C] (J : Functor V C) {τ : Type*}
    [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ] (M : TypeModel τ V)
    [LambdaIter.HasTy LambdaIter.EmptyInstr.{w} τ] :
    InstructionModel J M LambdaIter.EmptyInstr.{w} where
  denote f := f.elim

end Isotope.LambdaSeq.Semantics.Categorical

/-!
## The two theorems, as six checked corollaries

Each definition below is an application of the corresponding `denote` to the
empty signature's models, so the claim "the empty signature has a model in
every monad / in every Freyd category" is *elaborated* rather than asserted:
if any interface were missing, these would not typecheck.
-/

namespace Isotope.LambdaIter.Subtyping.Semantics.EmptySignature

open CategoryTheory CategoryTheory.Limits
open Isotope.LambdaIter Isotope.LambdaIter.Subtyping.Semantics

section Monadic

variable {ν : Type w} [DecidableEq ν] {m : Type v → Type v} [Monad m]

/-- **λ-seq over the empty signature denotes in every monad.**  No iteration,
no coproducts, no lawfulness: `[Monad m]` alone. -/
def denoteSeq {Γ : Ctx ν EmptyTy.{u}} {n : Nat}
    {β : LambdaSeq.LocallyNameless.BoundCtx EmptyTy.{u} n}
    {t : LambdaSeq.LocallyNameless.Tm ν EmptyInstr.{u} n} {A : EmptyTy.{u}}
    (h : LambdaSeq.LocallyNameless.HasType EmptyInstr.{u} Γ β t A) :
    CtxDen Γ → BoundDen β → m (TyDen A) :=
  LambdaSeq.Semantics.denote (ε := EmptyEff.{u}) h

/-- **λ-case over the empty signature denotes in every monad.**  Products,
coproducts and `abort` are all interpreted set-theoretically, so still only
`[Monad m]` is needed — no iteration operator. -/
def denoteCase {Γ : Ctx ν EmptyTy.{u}} {n : Nat}
    {β : LambdaCase.LocallyNameless.BoundCtx EmptyTy.{u} n}
    {t : LambdaCase.LocallyNameless.Tm ν EmptyInstr.{u} n} {A : EmptyTy.{u}}
    (h : LambdaCase.LocallyNameless.HasType EmptyInstr.{u} Γ β t A) :
    CtxDen Γ → BoundDen β → m (TyDen A) :=
  LambdaCase.Semantics.denote (ε := EmptyEff.{u}) h

/-- **λ-iter over the empty signature denotes in every monad equipped with an
iteration operator.**  `[Iterate m]` is the *only* extra assumption over
λ-case; in particular `LawfulMonad` and the Elgot laws are not needed to
*define* the denotation.  They would be needed to prove it sound for the
equational theory, which is not claimed here. -/
def denoteIter [Isotope.Elgot.Iterate m] {Γ : Ctx ν EmptyTy.{u}} {n : Nat}
    {β : LocallyNameless.BoundCtx EmptyTy.{u} n}
    {t : LocallyNameless.Tm ν EmptyInstr.{u} n} {A : EmptyTy.{u}}
    (h : Subtyping.LocallyNameless.HasType EmptyInstr.{u} Γ β t A) :
    CtxDen Γ → BoundDen β → m (TyDen A) :=
  Semantics.denote (ε := EmptyEff.{u}) h

end Monadic

section Categorical

open Isotope.LambdaIter.Subtyping.Semantics.Categorical

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  {ν : Type w} [DecidableEq ν]

/-- **λ-seq over the empty signature denotes in every Freyd category.**  Plain
`FreydCategory J`: no distributivity, no Elgot structure, no iteration on `C`.

`V` is still asked for finite coproducts, and that is a fact about the *type
universe*, not about λ-seq.  λ-seq's terms never build or eliminate a sum, but
its types are still those of `Ty α`, which contains `⊕` and `0`, and its
`Subtyping` interface still demands coercions `0 ⟶ A`; interpreting those needs
an initial object, and interpreting `⊕` needs binary coproducts.  A universe
without those two formers would drop the assumption. -/
noncomputable def denoteSeqFreyd (J : Functor V C) [FreydCategory J]
    [HasFiniteCoproducts V]
    {Γ : Ctx ν EmptyTy.{u}} {n : Nat}
    {β : LambdaSeq.LocallyNameless.BoundCtx EmptyTy.{u} n}
    {t : LambdaSeq.LocallyNameless.Tm ν EmptyInstr.{u} n} {A : EmptyTy.{u}}
    (h : LambdaSeq.LocallyNameless.HasType EmptyInstr.{u} Γ β t A) :
    J.obj (LambdaSeq.Semantics.Categorical.envObj
        (LambdaSeq.Semantics.Categorical.emptyTypeModel.{u} (V := V)) Γ β) ⟶
      J.obj (LambdaSeq.Semantics.Categorical.emptyTypeModel.{u} (V := V) |>.obj A) :=
  LambdaSeq.Semantics.Categorical.denote J _ h

variable [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]

/-- **λ-case over the empty signature denotes in every distributive Freyd
category.**  A plain Freyd category does *not* suffice: `caseWithContext`
needs `DistributiveTensor.leftIso` and the inverse of `coprodComparison J`,
and `abort` needs the interpretation of `0` to be initial. -/
noncomputable def denoteCaseFreyd (J : Functor V C) [DistributiveFreydCategory J]
    {Γ : Ctx ν EmptyTy.{u}} {n : Nat}
    {β : LambdaCase.LocallyNameless.BoundCtx EmptyTy.{u} n}
    {t : LambdaCase.LocallyNameless.Tm ν EmptyInstr.{u} n} {A : EmptyTy.{u}}
    (h : LambdaCase.LocallyNameless.HasType EmptyInstr.{u} Γ β t A) :
    J.obj (envObj (Categorical.emptyTypeModel.{u} (V := V)) Γ β) ⟶
      J.obj (Categorical.emptyTypeModel.{u} (V := V) |>.obj A) :=
  LambdaCase.Semantics.Categorical.denote J _ h

variable [Iteration C] [ElgotCategory C]

/-- **λ-iter over the empty signature denotes in every strong Elgot Freyd
category.**  This is the full strength: distributivity for `case`, plus
`Iteration`/`ElgotCategory` on the computation category and the strength law
for `iter` in a context. -/
noncomputable def denoteIterFreyd (J : Functor V C) [StrongElgotFreydCategory J]
    {Γ : Ctx ν EmptyTy.{u}} {n : Nat}
    {β : LocallyNameless.BoundCtx EmptyTy.{u} n}
    {t : LocallyNameless.Tm ν EmptyInstr.{u} n} {A : EmptyTy.{u}}
    (h : Subtyping.LocallyNameless.HasType EmptyInstr.{u} Γ β t A) :
    J.obj (envObj (Categorical.emptyTypeModel.{u} (V := V)) Γ β) ⟶
      J.obj (Categorical.emptyTypeModel.{u} (V := V) |>.obj A) :=
  Categorical.denote J _ h

/-- The coercion-free (exact) λ-iter judgment denotes in the same frame, via
the embedding `HasType.toGeneric`. -/
noncomputable def denoteIterExactFreyd (J : Functor V C) [StrongElgotFreydCategory J]
    {Γ : Ctx ν EmptyTy.{u}} {n : Nat}
    {β : LocallyNameless.BoundCtx EmptyTy.{u} n}
    {t : LocallyNameless.Tm ν EmptyInstr.{u} n} {A : EmptyTy.{u}}
    (h : Isotope.LambdaIter.LocallyNameless.HasType EmptyInstr.{u} Γ β t A) :
    J.obj (envObj (Categorical.emptyTypeModel.{u} (V := V)) Γ β) ⟶
      J.obj (Categorical.emptyTypeModel.{u} (V := V) |>.obj A) :=
  LocallyNameless.Categorical.denote J _ h

end Categorical

end Isotope.LambdaIter.Subtyping.Semantics.EmptySignature
