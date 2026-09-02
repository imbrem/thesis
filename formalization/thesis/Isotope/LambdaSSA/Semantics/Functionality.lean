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

/-- Heterogeneous agreement allows a term to receive different result types.
This can only be observed through a common empty-producing prefix; otherwise
the result types and arrows coincide. -/
inductive HeterogeneousAgreement {Γ : VCtx τ} {t : Tm Φ} :
    {A : τ} → Tm.HasType Γ t A →
    {B : τ} → Tm.HasType Γ t B →
    (f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)) →
    (g : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj B)) → Prop where
  | equal {A : τ} {hA hB : Tm.HasType Γ t A}
      {f g : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
      (hfg : f = g) : HeterogeneousAgreement hA hB f g
  | bottom {A B : τ} {hA : Tm.HasType Γ t A} {hB : Tm.HasType Γ t B}
      {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
      {g : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj B)}
      (hf : FactorsThroughEmpty J M f)
      (hg : FactorsThroughEmpty J M g)
      (hp : hf.emptyPrefix = hg.emptyPrefix) : HeterogeneousAgreement hA hB f g

theorem HeterogeneousAgreement.eq_of_same_type
    {Γ : VCtx τ} {t : Tm Φ} {A : τ}
    {hA hB : Tm.HasType Γ t A}
    {f g : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
    (a : HeterogeneousAgreement J M hA hB f g) : f = g := by
  cases a with
  | equal hfg => exact hfg
  | bottom hf hg hp => exact hf.eq_of_prefix hg hp

theorem HeterogeneousAgreement.abort
    {Γ : VCtx τ} {a : Tm Φ} {A B : τ}
    {ha : Tm.HasType Γ a LambdaIter.empty}
    {hA : Tm.HasType Γ (.abort a) A} {hB : Tm.HasType Γ (.abort a) B}
    {z z' : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj (LambdaIter.empty : τ))}
    (hz : z = z') :
    HeterogeneousAgreement J M hA hB (abort J M (A := A) z)
      (abort J M (A := B) z') := by
  subst z'
  exact .bottom (abort_factors J M z) (abort_factors J M z) rfl

/-- Two denotations agree either directly or because they have the same
empty-producing prefix.  Keeping the prefix is essential: maps into an
initial object need not themselves be unique. -/
inductive DenotesAgreement
    {Γ : VCtx τ} {t : Tm Φ} {A : τ} {h : Tm.HasType Γ t A}
    {f g : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)} : Prop where
  | equal (hfg : f = g) : DenotesAgreement
  | bottom (hf : FactorsThroughEmpty J M f)
      (hg : FactorsThroughEmpty J M g)
      (hp : hf.emptyPrefix = hg.emptyPrefix) : DenotesAgreement

theorem DenotesAgreement.eq
    {Γ : VCtx τ} {t : Tm Φ} {A : τ} {h : Tm.HasType Γ t A}
    {f g : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
    (a : DenotesAgreement J M (h := h) (f := f) (g := g)) : f = g := by
  cases a with
  | equal hfg => exact hfg
  | bottom hf hg hp => exact hf.eq_of_prefix hg hp

theorem HeterogeneousAgreement.toDenotesAgreement
    {Γ : VCtx τ} {t : Tm Φ} {A : τ} {h : Tm.HasType Γ t A}
    {f g : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
    (a : HeterogeneousAgreement J M h h f g) :
    DenotesAgreement J M (h := h) (f := f) (g := g) := by
  cases a with
  | equal hfg => exact .equal hfg
  | bottom hf hg hp => exact .bottom hf hg hp

/-- Once constructor-wise agreement has been established, functionality is a
direct consequence; no independent semantic coherence assumption is needed. -/
theorem Denotes.functional_of_agreement
    {Γ : VCtx τ} {t : Tm Φ} {A : τ} {h : Tm.HasType Γ t A}
    {f g : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
    (_df : Denotes J M h f) (_dg : Denotes J M h g)
    (a : DenotesAgreement J M (h := h) (f := f) (g := g)) : f = g :=
  a.eq

end Isotope.LambdaSSA.Semantics.Categorical
