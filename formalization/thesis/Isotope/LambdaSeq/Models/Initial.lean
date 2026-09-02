import Isotope.LambdaSeq.Models.Syntax
import Isotope.LambdaSeq.Models.Limits
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Initiality of the quotiented lambda-seq syntax, and equational completeness

For a fixed signature `S`, the quotiented lambda-seq syntax `Syn S` is the
initial object of `Alg S`.  Both halves are proved here and are named so that
neither can be mistaken for the other:

* **existence** is `Syn.toHom`, the interpretation of the syntactic model in an
  arbitrary model, as a morphism of models;
* **uniqueness** is `Syn.hom_eq_toHom`: any morphism of models out of `Syn S`
  equals `Syn.toHom`.

`Syn.uniqueHom` and `Syn.isInitial` package the two together, and
`Syn.equiv_of_denote_eq` is the completeness corollary.

## Honest boundary

A "model" is an object of `Alg S`, that is, an *algebra of the equational
presentation* of lambda-seq.  It is **not** a Freyd category, and nothing here
proves that a monad or a Freyd category yields one: that means discharging
`Alg.coh` and `Alg.sound`, and this repository contains no soundness theorem
for any lambda-seq denotation with respect to `Equiv`.  So `Syn.isInitial` is
initiality in the category of algebras and `Syn.equiv_of_denote_eq` is
completeness with respect to algebras; neither may be weakened to "all models"
in the informal sense, nor strengthened to Freyd semantics.

Non-vacuity comes from `Models/Limits.lean` and `Models/Examples.lean`, which
supply algebras other than `Syn S` and parallel morphisms that differ.
-/

namespace Isotope.LambdaSeq

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
derivation.  This is *not* definitional: the class remembers only the term, and
`Alg.coh` repairs the difference between derivations. -/
@[simp] theorem interp_mk (X : Alg.{u, u} S) {n : Nat} {β : BoundCtx S.Ty n}
    {A : S.Ty} {t : Tm Empty S.Instr n}
    (h : HasType S.Instr LambdaIter.Ctx.nil β t A) :
    interp X (mk h) = X.denote h := X.coh _ _

/-- **Existence half of initiality (the interpretation theorem).**  The
interpretation of the syntactic model in an arbitrary model, as a morphism of
models.  On its own this says only that `Syn S` has *at least* one morphism to
every algebra; uniqueness is `hom_eq_toHom`. -/
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

/-- **For a fixed signature, the quotiented lambda-seq syntax is the initial
model:** there is exactly one morphism from `Syn S` to any algebra of the
equational presentation of lambda-seq over `S`. -/
noncomputable instance uniqueHom (X : Alg.{u, u} S) : Unique (Syn S ⟶ X) where
  default := toHom X
  uniq := hom_eq_toHom X

/-- **The quotiented lambda-seq syntax is an initial object of the category of
models.**  Initiality among *algebras of the equational presentation*. -/
noncomputable def isInitial (S : Sig.{u}) :
    CategoryTheory.Limits.IsInitial (Syn.{u} S) :=
  CategoryTheory.Limits.IsInitial.ofUnique _

noncomputable instance hasInitial (S : Sig.{u}) :
    CategoryTheory.Limits.HasInitial (Alg.{u, u} S) :=
  (isInitial S).hasInitial

/-- **Equational completeness with respect to algebras.**  If two typable
lambda-seq terms have the same denotation in every algebra of the presentation,
they are provably equal in the equational theory `Equiv`. -/
theorem equiv_of_denote_eq {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty}
    {t t' : Tm Empty S.Instr n}
    (h : HasType S.Instr LambdaIter.Ctx.nil β t A)
    (h' : HasType S.Instr LambdaIter.Ctx.nil β t' A)
    (H : ∀ X : Alg.{u, u} S, X.denote h = X.denote h') :
    Equiv (Φ := S.Instr) S.pureEff LambdaIter.Ctx.nil β t t' A := by
  have e := H (Syn S)
  rw [denote_mk, denote_mk] at e
  exact equiv_of_mk_eq e

/-- **Soundness and completeness together.**  Two typable lambda-seq terms are
provably equal exactly when they denote equally in every algebra.  Soundness is
the `sound` field of a model, so the content is entirely in the left-to-right
direction, which is `equiv_of_denote_eq`. -/
theorem denote_eq_iff_equiv {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty}
    {t t' : Tm Empty S.Instr n}
    (h : HasType S.Instr LambdaIter.Ctx.nil β t A)
    (h' : HasType S.Instr LambdaIter.Ctx.nil β t' A) :
    (∀ X : Alg.{u, u} S, X.denote h = X.denote h') ↔
      Equiv (Φ := S.Instr) S.pureEff LambdaIter.Ctx.nil β t t' A :=
  ⟨equiv_of_denote_eq h h', fun e X => X.sound h h' e⟩

end Syn

end Isotope.LambdaSeq
