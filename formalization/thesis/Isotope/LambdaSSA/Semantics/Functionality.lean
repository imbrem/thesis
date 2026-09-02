import Isotope.LambdaSSA.Semantics.Inversion
import Isotope.LambdaSSA.Semantics.TypingAgreement

/-! # Bottom-aware functionality of SSA denotations -/

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open Isotope.LambdaIter.Subtyping.Semantics.Categorical

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : Functor V C) [DistributiveFreydCategory J]
  {τ : Type u₃} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
  (M : TypeModel τ V)
  {Φ : Type u₄} [LambdaIter.HasTy Φ τ] [InstructionModel J M Φ]

/-- Two denotations agree either directly or because they have the same
empty-producing prefix.  Keeping the prefix is essential: maps into an
initial object need not themselves be unique. -/
inductive DenotesAgreement
    {Γ : VCtx τ} {t : Tm Φ} {A : τ} {h : Tm.HasType Γ t A}
    {f g : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)} : Prop where
  | equal (hfg : f = g) : DenotesAgreement
  | bottom (hf : FactorsThroughEmpty J M f)
      (hg : FactorsThroughEmpty J M g)
      (hp : hf.prefix = hg.prefix) : DenotesAgreement

theorem DenotesAgreement.eq
    {Γ : VCtx τ} {t : Tm Φ} {A : τ} {h : Tm.HasType Γ t A}
    {f g : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
    (a : DenotesAgreement J M (h := h) (f := f) (g := g)) : f = g := by
  cases a with
  | equal hfg => exact hfg
  | bottom hf hg hp => exact hf.eq_of_prefix hg hp

end Isotope.LambdaSSA.Semantics.Categorical
