import Isotope.LambdaIter.Subtyping.Semantics.Models.Empty
import Isotope.LambdaIter.Subtyping.Semantics.KleisliModel
import Isotope.Elgot.Nondet.Powerset
import Isotope.Elgot.ITree
import Isotope.Elgot.Brookes
import Isotope.Elgot.RA
import Isotope.Elgot.Transformer.State
import Isotope.LambdaCase.Semantics.Identity

/-!
# The empty signature, instantiated

`Models/Empty.lean` proves the two theorems in the abstract: the empty
signature has a model in every monad and in every Freyd category.  This file
*fires* them, at the monads and effectful Freyd categories already formalized
elsewhere in the development, and at one worked closed term.

Nothing here is new mathematics; the point is that each line below is an
elaborated application, so a missing or mis-universed interface would show up
as a compile error rather than as an unchecked claim.

## Honest boundary

These are instantiations of the *interface* theorems.  None of them is a
soundness or adequacy statement: no equation of the equational theory is
claimed to hold in any of these models.
-/

universe u v

namespace Isotope.LambdaIter.Subtyping.Semantics.EmptySignature

open CategoryTheory Isotope.Elgot Isotope.LambdaIter Isotope.LambdaIter.Subtyping.Semantics

/-! ## A model in every monad, at concrete monads

Each definition is `denoteIter` (λ-iter's monadic semantics over the empty
signature) at a concrete `[Monad m] [Iterate m]` from the development. -/

section ConcreteMonads

variable {t : LocallyNameless.Tm Empty EmptyInstr.{u} 0} {A : EmptyTy.{u}}
  (h : Subtyping.LocallyNameless.HasType EmptyInstr.{u} .nil .nil t A)

/-- Partiality. -/
noncomputable def denotePart : _root_.Part.{v} (TyDen A) :=
  denoteClosed (ε := EmptyEff.{u}) (m := _root_.Part.{v}) h

/-- Nondeterminism (the powerset monad). -/
def denoteSetM : SetM.{v} (TyDen A) :=
  denoteClosed (ε := EmptyEff.{u}) (m := SetM.{v}) h

/-- Interaction trees over an arbitrary event signature. -/
noncomputable def denoteITree (E : Type v → Type v) : ITree.Tree E (TyDen A) :=
  denoteClosed (ε := EmptyEff.{u}) (m := ITree.Tree E) h

/-- Partial state. -/
noncomputable def denoteState (S : Type v) : StateT S _root_.Part.{v} (TyDen A) :=
  denoteClosed (ε := EmptyEff.{u}) (m := StateT S _root_.Part.{v}) h

/-- Brookes-style traces, for any rewriting relation. -/
def denoteBrookes {E : Type v} (c : Brookes.Rewriting E) : Brookes c (TyDen A) :=
  denoteClosed (ε := EmptyEff.{u}) (m := Brookes c) h

/-- The release-acquire concurrency monad. -/
def denoteComp (R : RA.RuleSet) (Loc Val : Type) : RA.Comp R Loc Val (TyDen A) :=
  denoteClosed (ε := EmptyEff.{u}) (m := RA.Comp R Loc Val) h

end ConcreteMonads

/-! ## A model in every Freyd category, at concrete Freyd categories

Each Kleisli category below is a `StrongElgotFreydCategory` (established in
`Semantics/Examples.lean`), so the categorical λ-iter semantics applies. -/

section ConcreteFreyd

variable {ν : Type} [DecidableEq ν] {Γ : Ctx ν EmptyTy.{u}} {n : Nat}
  {β : LocallyNameless.BoundCtx EmptyTy.{u} n}
  {t : LocallyNameless.Tm ν EmptyInstr.{u} n} {A : EmptyTy.{u}}
  (h : Subtyping.LocallyNameless.HasType EmptyInstr.{u} Γ β t A)

/-- λ-iter over the empty signature, in the Kleisli–Freyd category of `Part`. -/
noncomputable def denoteFreydPart :=
  denoteIterFreyd (Kleisli.Adjunction.toKleisli (Kleisli.Type.TM _root_.Part.{v})) h

/-- λ-iter over the empty signature, in the Kleisli–Freyd category of the
powerset monad. -/
noncomputable def denoteFreydSetM :=
  denoteIterFreyd (Kleisli.Adjunction.toKleisli (Kleisli.Type.TM SetM.{v})) h

/-- λ-iter over the empty signature, in the Kleisli–Freyd category of
interaction trees. -/
noncomputable def denoteFreydITree (E : Type v → Type v) :=
  denoteIterFreyd (Kleisli.Adjunction.toKleisli (Kleisli.Type.TM (ITree.Tree E))) h

/-- λ-case over the empty signature needs only a *distributive* Freyd
category; the Kleisli–Freyd category of `Part` is one. -/
noncomputable def denoteCaseFreydPart
    {βc : LambdaCase.LocallyNameless.BoundCtx EmptyTy.{u} n}
    {tc : LambdaCase.LocallyNameless.Tm ν EmptyInstr.{u} n}
    (hc : LambdaCase.LocallyNameless.HasType EmptyInstr.{u} Γ βc tc A) :=
  denoteCaseFreyd (Kleisli.Adjunction.toKleisli (Kleisli.Type.TM _root_.Part.{v})) hc

/-- λ-seq over the empty signature needs only a plain Freyd category. -/
noncomputable def denoteSeqFreydPart
    {βs : LambdaSeq.LocallyNameless.BoundCtx EmptyTy.{u} n}
    {ts : LambdaSeq.LocallyNameless.Tm ν EmptyInstr.{u} n}
    (hs : LambdaSeq.LocallyNameless.HasType EmptyInstr.{u} Γ βs ts A) :=
  denoteSeqFreyd (Kleisli.Adjunction.toKleisli (Kleisli.Type.TM _root_.Part.{v})) hs

end ConcreteFreyd

/-! ## A worked closed term

The empty signature has no instructions, but it still has terms.  `boolTm true`
is the closed λ-case term `inl ⟨⟩` at type `1 ⊕ 1`, and the identity-monad
evaluator computes it. -/

/-- The closed λ-case term `inl ⟨⟩`, of type `bool = 1 ⊕ 1`. -/
def trueTm : LambdaCase.LocallyNameless.Tm Empty EmptyInstr.{0} 0 := .inl .unit

/-- ...and its typing derivation over the empty signature. -/
def trueTy : LambdaCase.LocallyNameless.HasType EmptyInstr.{0}
    (.nil : Ctx Empty EmptyTy.{0}) .nil trueTm EmptyTy.boolTy.{0} :=
  .inl .unit

/-- **The empty signature computes.**  Evaluating `inl ⟨⟩` in the identity
monad gives the left injection, so the denotation is not a formal symbol. -/
example :
    LambdaCase.Semantics.Identity.eval (ε := EmptyEff.{0}) trueTy PUnit.unit PUnit.unit =
      Sum.inl PUnit.unit := rfl

/-- The same term denotes `pure (inl ())` in *every* lawful monad, so the
identity-monad computation above is not an artifact of `Id`. -/
example (m : Type → Type) [Monad m] [LawfulMonad m] :
    LambdaCase.Semantics.denote (ε := EmptyEff.{0}) (m := m) trueTy
        PUnit.unit PUnit.unit =
      pure (Sum.inl PUnit.unit) := by
  have h : LambdaCase.Semantics.denote (ε := EmptyEff.{0}) (m := m) trueTy
      PUnit.unit PUnit.unit
      = (pure PUnit.unit : m PUnit) >>= fun a => pure (Sum.inl a) := rfl
  rw [h, pure_bind]

end Isotope.LambdaIter.Subtyping.Semantics.EmptySignature
