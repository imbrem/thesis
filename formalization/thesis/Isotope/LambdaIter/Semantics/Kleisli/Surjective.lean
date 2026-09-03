import Isotope.LambdaIter.Subtyping.Semantics.Agreement

/-!
# The environment embedding is surjective

`envToCategorical` embeds the nested-pair environments of the direct semantics
into the categorical environment object of the Kleisli model.  The agreement
theorem of `Agreement/Full.lean` is pointwise at points in the image of that
embedding, so turning it into an equation between Kleisli morphisms needs the
embedding to be onto.  It is: the only non-identity step is the map from the
syntactic-universe `PUnit` to the semantic-universe unit object, and both are
singletons.
-/

namespace Isotope.LambdaIter.Subtyping.Semantics

open CategoryTheory CategoryTheory.Limits
open Isotope.LambdaIter.LocallyNameless

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]

omit [DecidableEq ν] in
/-- Every categorical free environment comes from a nested-pair one. -/
theorem ctxToCategorical_surjective : {Γ : Ctx ν τ} →
    (c : Categorical.ctxObj (Categorical.ofTypeModel (τ := τ)) Γ) →
      ∃ γ : CtxDen Γ, ctxToCategorical γ = c
  | .nil, c => ⟨PUnit.unit, by cases c; rfl⟩
  | .snoc Γ _ A, c => by
      obtain ⟨γ, hγ⟩ := ctxToCategorical_surjective (Γ := Γ) c.1
      refine ⟨(γ, c.2), ?_⟩
      show (ctxToCategorical γ, c.2) = c
      rw [hγ]
      rfl

/-- Every categorical bound environment comes from a nested-pair one. -/
theorem boundToCategorical_surjective : {n : Nat} → {β : BoundCtx τ n} →
    (c : Categorical.boundObj (Categorical.ofTypeModel (τ := τ)) β) →
      ∃ ρ : BoundDen β, boundToCategorical ρ = c
  | 0, .nil, c => ⟨PUnit.unit, by cases c; rfl⟩
  | _ + 1, .snoc β A, c => by
      obtain ⟨ρ, hρ⟩ := boundToCategorical_surjective (β := β) c.1
      refine ⟨(ρ, c.2), ?_⟩
      show (boundToCategorical ρ, c.2) = c
      rw [hρ]
      rfl

/-- **The environment embedding is onto.** -/
theorem envToCategorical_surjective {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    (e : Categorical.envObj (Categorical.ofTypeModel (τ := τ)) Γ β) :
    ∃ (γ : CtxDen Γ) (ρ : BoundDen β), envToCategorical γ ρ = e := by
  obtain ⟨γ, hγ⟩ := ctxToCategorical_surjective (Γ := Γ) e.1
  obtain ⟨ρ, hρ⟩ := boundToCategorical_surjective (β := β) e.2
  refine ⟨γ, ρ, ?_⟩
  show (ctxToCategorical γ, boundToCategorical ρ) = e
  rw [hγ, hρ]
  rfl

end Isotope.LambdaIter.Subtyping.Semantics
