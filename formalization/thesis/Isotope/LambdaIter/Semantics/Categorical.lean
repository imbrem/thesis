import Isotope.LambdaIter.Semantics.Denotation
import Isotope.LambdaIter.Subtyping.Semantics.Categorical

/-!
# Abstract categorical semantics for coercion-free lambda-iter

This module presently reuses the categorical `TypeModel` object interface.
Consequently it carries an unused ambient `Subtyping τ` instance; no coercion
derivation is introduced by the embedding below. Removing that vestigial
parameter is an API refactor, not a semantic requirement.
-/

namespace Isotope.LambdaIter.LocallyNameless

universe v₁ v₂ u₁ u₂ u₃ u₄ u₅

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u₃} [TypeFormers τ] [Subtyping τ]
variable {ν : Type u₄} [DecidableEq ν]
variable {Φ : Type u₅} [HasTy Φ τ]

namespace Categorical

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  (M : Subtyping.Semantics.Categorical.TypeModel τ V)
  [Subtyping.Semantics.Categorical.InstructionModel J M Φ]

/-- A pure primitive instruction is represented in the value category and
the computation interpretation is exactly its image under the Freyd
embedding. -/
class PureInstructionModel {ε : Type*} [HasEff Φ ε] (pureEff : ε) where
  denotePure (f : Φ) (hf : IsPure pureEff f) : M.obj (instrSrc f) ⟶ M.obj (instrTrg f)
  map_denotePure (f : Φ) (hf : IsPure pureEff f) :
    J.map (denotePure f hf) =
      Subtyping.Semantics.Categorical.InstructionModel.denote f

/-- Abstract categorical denotation of an exact typing derivation. -/
noncomputable def denote {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A) :
    J.obj (Subtyping.Semantics.Categorical.envObj M Γ β) ⟶ J.obj (M.obj A) :=
  Subtyping.Semantics.Categorical.denote J M h.toGeneric

/-- Optional coherence of the semantics with respect to exact typing
derivations. This is not automatic for an arbitrary `TypeFormers τ`: if, for
example, tensor is non-injective, the same pair term can admit genuinely
different decompositions and hence use different model isomorphisms. -/
class TypingCoherent : Prop where
  denote_eq {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
      {t : Tm ν Φ n} {A : τ} (h k : HasType Φ Γ β t A) :
    denote J M h = denote J M k

end Categorical

end Isotope.LambdaIter.LocallyNameless
