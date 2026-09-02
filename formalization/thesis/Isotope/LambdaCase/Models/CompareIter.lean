import Isotope.LambdaCase.Models.Initial
import Isotope.LambdaCase.Metatheory.EmbedIter
import Isotope.LambdaIter.Models.Alg

/-!
# Comparison of the lambda-case and lambda-iter model theories

Lambda-case is the iteration-free fragment of lambda-iter: its eleven term
formers are eleven of lambda-iter's twelve, and its fifteen axioms are
lambda-iter's `StructuralAxiom` and `SequencingAxiom` schemes.  This file turns
that inclusion of presentations into a functor of model categories and
identifies the map it forces out of the initial lambda-case model.

* `Alg.ofIter` restricts a lambda-iter algebra to a lambda-case algebra by
  forgetting `iter`.  Coherence transports along `HasType.embed` and soundness
  along `Equiv.embedIter` (proved in
  `Isotope/LambdaCase/Metatheory/EmbedIter.lean`); the latter is the whole
  content of the restriction, and is why this file could not be written before
  that lemma existed.
* `Alg.ofIterFunctor` makes this a functor `LambdaIter.Alg S ⥤ LambdaCase.Alg S`
  over a *shared* signature `S : LambdaIter.Sig`.
* `Syn.toIter_mk` computes the unique morphism out of the initial lambda-case
  model into such a restriction: **it sends the class of a lambda-case typing
  derivation to the lambda-iter denotation of its embedding.**  This is the
  model-level form of "the equational theories agree along the embedding".

## What this does not say

The statement is against an *arbitrary* lambda-iter algebra, not against a
lambda-iter syntactic model: no quotient of lambda-iter syntax is constructed
in this repository at the time of writing, so nothing here asserts that the
comparison map into such a quotient is injective, i.e. that lambda-iter is
conservative over lambda-case.  `Equiv.embedIter` goes in one direction only.
-/

namespace Isotope.LambdaCase

open LocallyNameless

open Isotope.LambdaIter (Sig instrSrc instrTrg)

universe u w

namespace Alg

variable {S : Sig.{u}}

/-- The operations of a lambda-iter algebra, restricted to the iteration-free
fragment. -/
def opsOfIter (X : LambdaIter.Alg.Ops.{u, w} S) : Ops.{u, w} S where
  El β A := X.El β A
  var i := X.var i
  op f a := X.op f a
  let₁ a b := X.let₁ a b
  unit := X.unit
  pair a b := X.pair a b
  let₂ a c := X.let₂ a c
  inl a := X.inl a
  inr b := X.inr b
  case e l r := X.case e l r
  abort a := X.abort a

/-- Denoting a lambda-case derivation in a restricted lambda-iter algebra is
denoting its image under the term embedding. -/
theorem denote_opsOfIter (X : LambdaIter.Alg.Ops.{u, w} S) :
    ∀ {n : Nat} {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
      (h : HasType S.Instr LambdaIter.Ctx.nil β t A),
      (opsOfIter X).denote h = X.denote h.embed
  | _, _, _, _, .fv h => absurd h (by simp [LambdaIter.Ctx.lookup])
  | _, _, _, _, .bv => rfl
  | _, _, _, _, .op ha => by
      rw [Ops.denote_op, denote_opsOfIter X ha]; rfl
  | _, _, _, _, .let₁ ha hb => by
      rw [Ops.denote_let₁, denote_opsOfIter X ha, denote_opsOfIter X hb]; rfl
  | _, _, _, _, .unit => rfl
  | _, _, _, _, .pair ha hb => by
      rw [Ops.denote_pair, denote_opsOfIter X ha, denote_opsOfIter X hb]; rfl
  | _, _, _, _, .let₂ ha hc => by
      rw [Ops.denote_let₂, denote_opsOfIter X ha, denote_opsOfIter X hc]; rfl
  | _, _, _, _, .inl ha => by
      rw [Ops.denote_inl, denote_opsOfIter X ha]; rfl
  | _, _, _, _, .inr hb => by
      rw [Ops.denote_inr, denote_opsOfIter X hb]; rfl
  | _, _, _, _, .case he hl hr => by
      rw [Ops.denote_case, denote_opsOfIter X he, denote_opsOfIter X hl,
        denote_opsOfIter X hr]; rfl
  | _, _, _, _, .abort ha => by
      rw [Ops.denote_abort, denote_opsOfIter X ha]; rfl

/-- **Restriction of a lambda-iter model to a lambda-case model.**  Coherence
and soundness transport along the embedding of lambda-case into lambda-iter:
`HasType.embed` for the former, `Equiv.embedIter` for the latter. -/
def ofIter (X : LambdaIter.Alg.{u, w} S) : Alg.{u, w} S where
  toOps := opsOfIter X.toOps
  coh h k := by
    rw [denote_opsOfIter, denote_opsOfIter]; exact X.coh _ _
  sound h k e := by
    rw [denote_opsOfIter, denote_opsOfIter]; exact X.sound _ _ e.embedIter

@[simp] theorem ofIter_El (X : LambdaIter.Alg.{u, w} S) {n : Nat}
    {β : BoundCtx S.Ty n} {A : S.Ty} : (ofIter X).El β A = X.El β A := rfl

/-- Denoting a lambda-case derivation in a restricted model is denoting its
embedding in the original one. -/
@[simp] theorem denote_ofIter (X : LambdaIter.Alg.{u, w} S) {n : Nat}
    {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr LambdaIter.Ctx.nil β t A) :
    (ofIter X).denote h = X.denote h.embed := denote_opsOfIter X.toOps h

/-- Restriction of a lambda-iter model morphism. -/
def homOfIter {X Y : LambdaIter.Alg.{u, w} S} (F : X ⟶ Y) :
    ofIter X ⟶ ofIter Y where
  map := F.map
  map_var i := F.map_var i
  map_op f a := F.map_op f a
  map_let₁ a b := F.map_let₁ a b
  map_unit := F.map_unit
  map_pair a b := F.map_pair a b
  map_let₂ a c := F.map_let₂ a c
  map_inl a := F.map_inl a
  map_inr b := F.map_inr b
  map_case e l r := F.map_case e l r
  map_abort a := F.map_abort a

/-- **Restriction is a functor** from lambda-iter models to lambda-case models
over the same signature. -/
def ofIterFunctor (S : Sig.{u}) :
    CategoryTheory.Functor (LambdaIter.Alg.{u, w} S) (Alg.{u, w} S) where
  obj := ofIter
  map := homOfIter
  map_id _ := rfl
  map_comp _ _ := rfl

end Alg

namespace Syn

variable {S : Sig.{u}}

/-- The unique lambda-case model morphism from the initial lambda-case model
into the restriction of a lambda-iter model. -/
noncomputable def toIter (X : LambdaIter.Alg.{u, u} S) :
    Syn.{u} S ⟶ Alg.ofIter X := toHom (Alg.ofIter X)

/-- **Agreement with the embedding into lambda-iter.**  For every lambda-iter
algebra `X`, the unique lambda-case model morphism out of the syntactic model
sends the class of a lambda-case typing derivation to the lambda-iter
denotation of its embedding.

Equivalently: interpreting a lambda-case term in a lambda-iter model, either by
first embedding it and then denoting, or by restricting the model and then
using initiality, gives the same answer. -/
@[simp] theorem toIter_mk (X : LambdaIter.Alg.{u, u} S) {n : Nat}
    {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr LambdaIter.Ctx.nil β t A) :
    (toIter X).map (mk h) = X.denote h.embed := by
  rw [toIter, toHom_map, interp_mk, Alg.denote_ofIter]

/-- Any lambda-case model morphism out of `Syn S` into a restricted lambda-iter
model is `toIter`, by initiality. -/
theorem hom_eq_toIter (X : LambdaIter.Alg.{u, u} S)
    (F : Syn.{u} S ⟶ Alg.ofIter X) : F = toIter X := hom_eq_toHom _ F

end Syn

end Isotope.LambdaCase
