import Isotope.LambdaIter.NoSubtyping.Metatheory
import Isotope.LambdaIter.Semantics.Categorical

/-!
# Abstract categorical semantics for coercion-free lambda-iter

This module presently reuses the categorical `TypeModel` object interface.
Consequently it carries an unused ambient `Subtyping τ` instance; no coercion
derivation is introduced by the embedding below. Removing that vestigial
parameter is an API refactor, not a semantic requirement.
-/

namespace Isotope.LambdaIter.NoSubtyping.LocallyNameless

universe v₁ v₂ u₁ u₂ u₃ u₄ u₅

open CategoryTheory CategoryTheory.Limits
open Isotope.LambdaIter.Semantics

variable {τ : Type u₃} [TypeFormers τ] [Subtyping τ]
variable {ν : Type u₄} [DecidableEq ν]
variable {Φ : Type u₅} [HasTy Φ τ]

/-- Embed an exact typing derivation into the older generic judgment. Every
constructor is preserved and, crucially, no `sub` node is inserted. -/
def HasType.toGeneric : {Γ : Ctx ν τ} → {n : Nat} →
    {β : BoundCtx τ n} → {t : Tm ν Φ n} → {A : τ} →
    HasType Φ Γ β t A →
      Isotope.LambdaIter.LocallyNameless.HasType Φ Γ β t A
  | _, _, _, _, _, .fv h => .fv h
  | _, _, _, _, _, .bv => .bv
  | _, _, _, _, _, .op h => .op h.toGeneric
  | _, _, _, _, _, .let₁ ha hb => .let₁ ha.toGeneric hb.toGeneric
  | _, _, _, _, _, .unit => .unit
  | _, _, _, _, _, .pair ha hb => .pair ha.toGeneric hb.toGeneric
  | _, _, _, _, _, .let₂ ha hc => .let₂ ha.toGeneric hc.toGeneric
  | _, _, _, _, _, .inl h => .inl h.toGeneric
  | _, _, _, _, _, .inr h => .inr h.toGeneric
  | _, _, _, _, _, .case he hl hr => .case he.toGeneric hl.toGeneric hr.toGeneric
  | _, _, _, _, _, .abort h => .abort h.toGeneric
  | _, _, _, _, _, .iter ha hb => .iter ha.toGeneric hb.toGeneric

namespace Categorical

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  (M : Semantics.Categorical.TypeModel τ V)
  [Semantics.Categorical.InstructionModel J M Φ]

/-- A pure primitive instruction is represented in the value category and
the computation interpretation is exactly its image under the Freyd
embedding. -/
class PureInstructionModel {ε : Type*} [HasEff Φ ε] (pureEff : ε) where
  denotePure (f : Φ) (hf : IsPure pureEff f) : M.obj (instrSrc f) ⟶ M.obj (instrTrg f)
  map_denotePure (f : Φ) (hf : IsPure pureEff f) :
    J.map (denotePure f hf) =
      Semantics.Categorical.InstructionModel.denote f

/-- Abstract categorical denotation of an exact typing derivation. -/
noncomputable def denote {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A) :
    J.obj (Semantics.Categorical.envObj M Γ β) ⟶ J.obj (M.obj A) :=
  Semantics.Categorical.denote J M h.toGeneric

/-- Optional coherence of the semantics with respect to exact typing
derivations. This is not automatic for an arbitrary `TypeFormers τ`: if, for
example, tensor is non-injective, the same pair term can admit genuinely
different decompositions and hence use different model isomorphisms. -/
class TypingCoherent : Prop where
  denote_eq {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
      {t : Tm ν Φ n} {A : τ} (h k : HasType Φ Γ β t A) :
    denote J M h = denote J M k

end Categorical

end Isotope.LambdaIter.NoSubtyping.LocallyNameless
