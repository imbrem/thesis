import Isotope.LambdaSeq.Models.Initial
import Isotope.LambdaCase.Models.Initial

/-!
# Comparison of the lambda-seq and lambda-case model theories

Lambda-seq is the sequential fragment of lambda-case: its three term formers
are three of lambda-case's eleven, and each of its four axioms is one of
lambda-case's fifteen.  This file turns that inclusion of presentations into a
functor of model categories and identifies the induced map out of the initial
object.

* `Alg.ofCase` restricts a lambda-case algebra to a lambda-seq algebra by
  forgetting the eight non-sequential operations.  Its two propositional
  fields are discharged by transporting along the term embedding: coherence
  along `HasType.embedCase`, soundness along `Equiv.embedCase` (which is
  already proved in `Isotope/LambdaSeq/Equiv.lean`).
* `Alg.ofCaseFunctor` makes this a functor `LambdaCase.Alg S ⥤ LambdaSeq.Alg S`
  over a *shared* signature `S : LambdaIter.Sig`.
* `Syn.toCase` is the unique lambda-seq model morphism from the initial
  lambda-seq model into the restriction of the initial lambda-case model, and
  `Syn.toCase_mk` computes it: **it is the term embedding on equivalence
  classes.**  That is the precise sense in which the two syntactic models
  agree.

## What this does not say

Nothing here compares lambda-case with lambda-iter; that comparison is
`Isotope/LambdaCase/Models/CompareIter.lean`.
-/

namespace Isotope.LambdaSeq

open LocallyNameless

open Isotope.LambdaIter (Sig instrSrc instrTrg)

universe u w

namespace Alg

variable {S : Sig.{u}}

/-- The operations of a lambda-case algebra, restricted to the sequential
fragment. -/
def opsOfCase (X : LambdaCase.Alg.Ops.{u, w} S) : Ops.{u, w} S where
  El β A := X.El β A
  var i := X.var i
  op f a := X.op f a
  let₁ a b := X.let₁ a b

/-- Denoting a lambda-seq derivation in a restricted lambda-case algebra is
denoting its image under the term embedding. -/
theorem denote_opsOfCase (X : LambdaCase.Alg.Ops.{u, w} S) :
    ∀ {n : Nat} {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
      (h : HasType S.Instr LambdaIter.Ctx.nil β t A),
      (opsOfCase X).denote h = X.denote h.embedCase
  | _, _, _, _, .fv h => absurd h (by simp [LambdaIter.Ctx.lookup])
  | _, _, _, _, .bv => rfl
  | _, _, _, _, .op ha => by
      rw [Ops.denote_op, denote_opsOfCase X ha]; rfl
  | _, _, _, _, .let₁ ha hb => by
      rw [Ops.denote_let₁, denote_opsOfCase X ha, denote_opsOfCase X hb]; rfl

/-- **Restriction of a lambda-case model to a lambda-seq model.**  Coherence
and soundness transport along the embedding of lambda-seq into lambda-case:
`HasType.embedCase` for the former, `Equiv.embedCase` for the latter. -/
def ofCase (X : LambdaCase.Alg.{u, w} S) : Alg.{u, w} S where
  toOps := opsOfCase X.toOps
  coh h k := by
    rw [denote_opsOfCase, denote_opsOfCase]; exact X.coh _ _
  sound h k e := by
    rw [denote_opsOfCase, denote_opsOfCase]; exact X.sound _ _ e.embedCase

@[simp] theorem ofCase_El (X : LambdaCase.Alg.{u, w} S) {n : Nat}
    {β : BoundCtx S.Ty n} {A : S.Ty} : (ofCase X).El β A = X.El β A := rfl

/-- Denoting a lambda-seq derivation in a restricted model is denoting its
embedding in the original one. -/
@[simp] theorem denote_ofCase (X : LambdaCase.Alg.{u, w} S) {n : Nat}
    {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr LambdaIter.Ctx.nil β t A) :
    (ofCase X).denote h = X.denote h.embedCase := denote_opsOfCase X.toOps h

/-- Restriction of a lambda-case model morphism. -/
def homOfCase {X Y : LambdaCase.Alg.{u, w} S} (F : X ⟶ Y) :
    ofCase X ⟶ ofCase Y where
  map := F.map
  map_var i := F.map_var i
  map_op f a := F.map_op f a
  map_let₁ a b := F.map_let₁ a b

/-- **Restriction is a functor** from lambda-case models to lambda-seq models
over the same signature. -/
def ofCaseFunctor (S : Sig.{u}) :
    CategoryTheory.Functor (LambdaCase.Alg.{u, w} S) (Alg.{u, w} S) where
  obj := ofCase
  map := homOfCase
  map_id _ := rfl
  map_comp _ _ := rfl

end Alg

namespace Syn

variable {S : Sig.{u}}

/-- The unique lambda-seq model morphism from the initial lambda-seq model into
the restriction of the initial lambda-case model.  It exists and is unique by
initiality of `Syn S`; the point of the next theorem is that it *computes*. -/
noncomputable def toCase (S : Sig.{u}) :
    Syn.{u} S ⟶ Alg.ofCase (LambdaCase.Syn.{u} S) :=
  toHom (Alg.ofCase (LambdaCase.Syn S))

/-- **The comparison map is the term embedding.**  On the class of a lambda-seq
typing derivation, the unique morphism `Syn S ⟶ ofCase (LambdaCase.Syn S)`
returns the class of the embedded derivation.

This is the precise sense in which the quotiented lambda-seq syntax sits inside
the quotiented lambda-case syntax: it is not merely that the terms embed, but
that the embedding is the map forced by initiality. -/
@[simp] theorem toCase_mk {n : Nat} {β : BoundCtx S.Ty n}
    {t : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr LambdaIter.Ctx.nil β t A) :
    (toCase S).map (mk h) = LambdaCase.Syn.mk h.embedCase := by
  rw [toCase, toHom_map, interp_mk, Alg.denote_ofCase, LambdaCase.Syn.denote_mk]

/-- Any lambda-seq model morphism out of `Syn S` into the restriction of the
lambda-case syntactic model is `toCase`, by initiality. -/
theorem hom_eq_toCase (F : Syn.{u} S ⟶ Alg.ofCase (LambdaCase.Syn.{u} S)) :
    F = toCase S := hom_eq_toHom _ F

end Syn

end Isotope.LambdaSeq
