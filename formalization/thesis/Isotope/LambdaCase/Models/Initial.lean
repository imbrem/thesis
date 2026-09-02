import Isotope.LambdaCase.Models.Syntax
import Isotope.LambdaCase.Models.Limits
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Initiality of the quotiented lambda-case syntax, and equational completeness

For a fixed signature `S`, the quotiented lambda-case syntax `Syn S` is the
initial object of `Alg S`: there is exactly one morphism from it to every
model.  Both halves are proved here, and are named so that neither can be
mistaken for the other:

* **existence** is `Syn.toHom`, the interpretation of the syntactic model in an
  arbitrary model, as a morphism of models.  It is `Quotient.lift` of the
  denotation; well-definedness with respect to `Equiv` is exactly the `sound`
  field of a model, and independence of the *chosen* typing derivation is
  exactly the `coh` field.
* **uniqueness** is `Syn.hom_eq_toHom`: any morphism of models out of `Syn S`
  equals `Syn.toHom`.  It needs no induction over derivations, because
  `Alg.Hom.map_denote` already performs it: every class is the denotation of a
  derivation in `Syn S`, and a model morphism commutes with denotation.

`Syn.uniqueHom` and `Syn.isInitial` package the two together.

The corollary is **equational completeness with respect to algebras**: two
typable terms with the same denotation in every algebra are `Equiv`-related
(`Syn.equiv_of_denote_eq`).  This is the converse of soundness, which is the
`sound` field of a model and therefore given rather than proved.

## Honest boundary

Read the qualifier: a "model" is an object of `Alg S`, that is, an *algebra of
the equational presentation* of lambda-case.  It is **not** a Freyd category,
and nothing here proves that a monad or a Freyd category yields one.  Doing
that means discharging `Alg.coh` and `Alg.sound` in such a category, which is
precisely the content of the two coherence classes
(`LambdaIter.Subtyping.Semantics.Categorical.TypingCoherent` and the
corresponding lawfulness class) that have no instance anywhere in this
repository; and no theorem in this repository states that any denotation of
lambda-case respects `Equiv`.  So:

* `Syn.isInitial` is initiality in the category of algebras;
* `Syn.equiv_of_denote_eq` is completeness with respect to algebras;
* neither statement may be weakened to "all models" in the informal sense, nor
  strengthened to Freyd or monadic semantics.

The non-vacuity of these statements comes from two directions.  `Alg S` is
inhabited by objects other than `Syn S` (`Alg.terminal`, `Alg.const`, and
products and powers of those, in `Models/Limits.lean` and
`Models/Examples.lean`), and has parallel morphisms that differ
(`Alg.constHom_ne_id`, `Alg.powReindex_ne_id`), so `Unique (Syn S ⟶ X)` is not
a statement about a degenerate class; and `Syn S` itself distinguishes
`Equiv`-inequivalent terms, which is what makes the completeness corollary
informative rather than trivial.

Universes: `Syn S : Alg.{u, u} S`, so the statements below quantify over
algebras whose carrier lands in `Type u`.  Nothing forces that restriction
mathematically, but stating it honestly is cheaper than carrying a lift.
-/

namespace Isotope.LambdaCase

open LocallyNameless

open Isotope.LambdaIter (Sig)

universe u

namespace Syn

variable {S : Sig.{u}}

/-- The interpretation of the syntactic model in an arbitrary model: send the
class of a term to the denotation of any of its typing derivations.

`Quotient.lift` is well defined by the model's `sound` field, and the choice of
derivation is immaterial by its `coh` field. -/
noncomputable def interp (X : Alg.{u, u} S) {n : Nat} {β : BoundCtx S.Ty n}
    {A : S.Ty} : El S β A → X.El β A :=
  Quotient.lift (fun a => X.denote (Classical.choice a.2))
    (fun _ _ e => X.sound _ _ e)

/-- The interpretation of the class of a derivation is the denotation of that
derivation.  Note this is *not* definitional: the class remembers only the
term, so a different derivation may be chosen, and `Alg.coh` is what repairs
the difference. -/
@[simp] theorem interp_mk (X : Alg.{u, u} S) {n : Nat} {β : BoundCtx S.Ty n}
    {A : S.Ty} {t : Tm Empty S.Instr n}
    (h : HasType S.Instr LambdaIter.Ctx.nil β t A) :
    interp X (mk h) = X.denote h := X.coh _ _

/-- **Existence half of initiality (the interpretation theorem).**  The
interpretation of the syntactic model in an arbitrary model, as a morphism of
models.

On its own this says only that `Syn S` has *at least* one morphism to every
algebra; the uniqueness half is `hom_eq_toHom` below. -/
noncomputable def toHom (X : Alg.{u, u} S) : Syn S ⟶ X where
  map := interp X
  map_var i := by simp
  map_op f a := by
    induction a using Syn.ind with
    | H _ ha => simp
  map_let₁ a b := by
    induction a using Syn.ind with
    | H _ ha => induction b using Syn.ind with
      | H _ hb => simp
  map_unit := by simp
  map_pair a b := by
    induction a using Syn.ind with
    | H _ ha => induction b using Syn.ind with
      | H _ hb => simp
  map_let₂ a c := by
    induction a using Syn.ind with
    | H _ ha => induction c using Syn.ind with
      | H _ hc => simp
  map_inl a := by
    induction a using Syn.ind with
    | H _ ha => simp
  map_inr b := by
    induction b using Syn.ind with
    | H _ hb => simp
  map_case e l r := by
    induction e using Syn.ind with
    | H _ he => induction l using Syn.ind with
      | H _ hl => induction r using Syn.ind with
        | H _ hr => simp
  map_abort a := by
    induction a using Syn.ind with
    | H _ ha => simp

@[simp] theorem toHom_map (X : Alg.{u, u} S) {n : Nat} {β : BoundCtx S.Ty n}
    {A : S.Ty} (x : El S β A) : (toHom X).map x = interp X x := rfl

/-- **Uniqueness half of initiality.**  Any morphism of models out of the
syntactic model is the interpretation. -/
theorem hom_eq_toHom (X : Alg.{u, u} S) (F : Syn S ⟶ X) : F = toHom X := by
  apply Alg.Hom.ext
  intro n β A x
  induction x using Syn.ind with
  | H t h =>
    rw [toHom_map, interp_mk, ← denote_mk h]
    exact F.map_denote h

/-- **For a fixed signature, the quotiented lambda-case syntax is the initial
model:** there is exactly one morphism from `Syn S` to any algebra of the
equational presentation of lambda-case over `S`.

`default` is the existence half (`toHom`) and `uniq` the uniqueness half
(`hom_eq_toHom`); both are genuinely proved. -/
noncomputable instance uniqueHom (X : Alg.{u, u} S) : Unique (Syn S ⟶ X) where
  default := toHom X
  uniq := hom_eq_toHom X

/-- **The quotiented lambda-case syntax is an initial object of the category of
models.**  This is initiality among *algebras of the equational presentation*;
see the module docstring for what it does not say. -/
noncomputable def isInitial (S : Sig.{u}) :
    CategoryTheory.Limits.IsInitial (Syn.{u} S) :=
  CategoryTheory.Limits.IsInitial.ofUnique _

noncomputable instance hasInitial (S : Sig.{u}) :
    CategoryTheory.Limits.HasInitial (Alg.{u, u} S) :=
  (isInitial S).hasInitial

/-- **Equational completeness with respect to algebras.**  If two typable
lambda-case terms have the same denotation in every algebra of the
presentation, they are provably equal in the equational theory `Equiv`.

The proof is one line: instantiate the hypothesis at the syntactic model and
apply exactness of the quotient.  This is the converse of soundness, which is
the `sound` field of a model. -/
theorem equiv_of_denote_eq {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty}
    {t t' : Tm Empty S.Instr n}
    (h : HasType S.Instr LambdaIter.Ctx.nil β t A)
    (h' : HasType S.Instr LambdaIter.Ctx.nil β t' A)
    (H : ∀ X : Alg.{u, u} S, X.denote h = X.denote h') :
    Equiv (Φ := S.Instr) S.pureEff LambdaIter.Ctx.nil β t t' A := by
  have e := H (Syn S)
  rw [denote_mk, denote_mk] at e
  exact equiv_of_mk_eq e

/-- **Soundness and completeness together.**  Two typable lambda-case terms are
provably equal exactly when they denote equally in every algebra.  Soundness
(the right-to-left direction) is the `sound` field of a model, so the content
is entirely in the left-to-right direction, which is `equiv_of_denote_eq`. -/
theorem denote_eq_iff_equiv {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty}
    {t t' : Tm Empty S.Instr n}
    (h : HasType S.Instr LambdaIter.Ctx.nil β t A)
    (h' : HasType S.Instr LambdaIter.Ctx.nil β t' A) :
    (∀ X : Alg.{u, u} S, X.denote h = X.denote h') ↔
      Equiv (Φ := S.Instr) S.pureEff LambdaIter.Ctx.nil β t t' A :=
  ⟨equiv_of_denote_eq h h', fun e X => X.sound h h' e⟩

end Syn

end Isotope.LambdaCase
