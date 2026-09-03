import Isotope.LambdaIter.Subtyping.LocallyNameless.Refinement
import Mathlib.Order.Antisymmetrization

/-! # The ordered syntactic presentation of lambda-iter refinement -/

namespace Isotope.LambdaIter.Subtyping.LocallyNameless.Refinement

open Isotope.LambdaIter.LocallyNameless
open Isotope.LambdaIter.Subtyping.LocallyNameless

universe u w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε]

set_option relaxedAutoImplicit true

variable {pureEff : ε} {Γ : LambdaIter.Ctx ν τ}
variable {R : Theory (Φ := Φ) Γ} {n : Nat} {β : BoundCtx τ n} {A : τ}

/-- A raw term together with its exact typing derivation.  Including the
derivation makes transitivity unconditional even when subtype witnesses are
semantically proof-relevant. -/
structure Presentation (pureEff : ε) (Γ : LambdaIter.Ctx ν τ)
    (R : Theory (Φ := Φ) Γ) (β : BoundCtx τ n) (A : τ) where
  term : Tm ν Φ n
  typing : HasType Φ Γ β term A

instance : LE (Presentation pureEff Γ R β A) where
  le a b := Related pureEff Γ R a.typing b.typing

instance : Preorder (Presentation pureEff Γ R β A) where
  le_refl a := Related.refl a.typing
  le_trans _ _ _ := Related.trans

/-- Quotienting the typed presentation by mutual refinement yields the
partially ordered syntactic model. -/
abbrev OrderedSyntax (pureEff : ε) (Γ : LambdaIter.Ctx ν τ)
    (R : Theory (Φ := Φ) Γ) (β : BoundCtx τ n) (A : τ) :=
  Antisymmetrization (Presentation pureEff Γ R β A) (· ≤ ·)

def Presentation.toOrderedSyntax (a : Presentation pureEff Γ R β A) :
    OrderedSyntax pureEff Γ R β A := toAntisymmetrization (· ≤ ·) a

theorem Presentation.toOrderedSyntax_le_iff
    (a b : Presentation pureEff Γ R β A) :
    a.toOrderedSyntax ≤ b.toOrderedSyntax ↔ Related pureEff Γ R a.typing b.typing :=
  toAntisymmetrization_le_toAntisymmetrization_iff

theorem Presentation.toOrderedSyntax_eq_iff
    (a b : Presentation pureEff Γ R β A) :
    a.toOrderedSyntax = b.toOrderedSyntax ↔
      Equivalent pureEff Γ R a.typing b.typing := by
  rw [le_antisymm_iff, Presentation.toOrderedSyntax_le_iff,
    Presentation.toOrderedSyntax_le_iff]
  rfl

end Isotope.LambdaIter.Subtyping.LocallyNameless.Refinement
