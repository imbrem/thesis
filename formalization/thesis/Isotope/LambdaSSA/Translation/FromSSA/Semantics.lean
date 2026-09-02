import Isotope.LambdaSSA.Translation.FromSSA
import Isotope.LambdaSSA.Semantics.Monadic.Model
import Isotope.LambdaSSA.Semantics.Label
import Isotope.LambdaIter.Subtyping.Semantics.Agreement

/-! # Semantic comparison for the reverse SSA translation

The SSA semantics uses an unbiased finite coproduct for label contexts, while
the reverse compiler necessarily chooses the right-associated binary encoding
`FromSSA.labelType`.  This file supplies the canonical comparison map.  It is
kept explicit in preservation statements, so no definitional identification of
these two representations is assumed.
-/

namespace Isotope.LambdaSSA.Translation.FromSSA.Semantics

open CategoryTheory CategoryTheory.Limits
open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics

universe u v

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]

/-- Injection into the right-associated semantic label sum chosen by the
reverse compiler. -/
def nestedInject : {L : LambdaSSA.LCtx τ} → (i : Nat) → {A : τ} →
    LambdaSSA.At L i A → TyDen A → TyDen (labelType L)
  | _ :: _, 0, _, h, a => by
      have e := Option.some.inj h
      subst e
      exact (TypeModel.coprodEquiv _ _).symm (.inl a)
  | _ :: L, i + 1, _, h, a =>
      (TypeModel.coprodEquiv _ _).symm (.inr (nestedInject i h a))

private noncomputable abbrev categoricalTypeModel :=
  Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofTypeModel (τ := τ)

/-- Fold the unbiased finite label coproduct used by SSA into the nested
binary coproduct used by the generated lambda-iter term. -/
noncomputable def encodeLabelsHom (L : LambdaSSA.LCtx τ) :
    LambdaSSA.Semantics.Categorical.labelObj categoricalTypeModel L ⟶
      TyDen (labelType L) :=
  Limits.Sigma.desc fun (i : Fin L.length) => nestedInject i.val (by
    simp [LambdaSSA.At, i.isLt])

noncomputable def encodeLabels (L : LambdaSSA.LCtx τ) :
    LambdaSSA.Semantics.Categorical.labelObj categoricalTypeModel L →
      TyDen (labelType L) := encodeLabelsHom L

end Isotope.LambdaSSA.Translation.FromSSA.Semantics
