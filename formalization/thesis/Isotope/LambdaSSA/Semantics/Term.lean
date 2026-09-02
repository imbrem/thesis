import Isotope.LambdaSSA.Semantics.Model
import Isotope.LambdaSSA.Semantics.Assumptions

/-! # Distributive Freyd semantics of lambda-SSA terms -/

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Isotope.LambdaSSA.Semantics.Categorical

set_option autoImplicit true
set_option relaxedAutoImplicit true

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.PremonoidalCategory
open Isotope.LambdaIter.Subtyping.Semantics.Categorical
open scoped MonoidalCategory

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

/-- The graph of denotation.  Typing is a `Prop`, so Lean cannot eliminate a
typing derivation directly into a hom-set.  Defining its single-valued graph
in `Prop` preserves the intended structural definition without strengthening
the typing judgment to `Type`. -/
inductive Denotes : {Γ : VCtx τ} → {t : Tm Φ} → {A : τ} →
    Tm.HasType Γ t A → (J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)) → Prop where
  | var (h : At Γ i A) : Denotes (.var h) (J.map (lookup M i h))
  | op (dha : Denotes ha fa) :
      Denotes (.op ha) (fa ≫ InstructionModel.denote _)
  | let₁ (dha : Denotes ha fa) (dhb : Denotes hb fb) :
      Denotes (.let₁ ha hb) (bind J fa fb)
  | pair (dha : Denotes ha fa) (dhb : Denotes hb fb) :
      Denotes (.pair ha hb)
        (pair J fa fb ≫ J.map (M.tensorIso _ _).inv)
  | unit : Denotes (.unit (Γ := Γ))
      (J.map (CartesianMonoidalCategory.toUnit _ ≫ M.unitIso.inv))
  | let₂ (dha : Denotes ha fa) (dhb : Denotes hb fb) :
      Denotes (.let₂ ha hb) (bind J fa (
        J.map ((𝟙 _) ⊗ₘ (M.tensorIso _ _).hom) ≫
          J.map (ctxPairIso M _ _ _).hom ≫ fb))
  | inl (dha : Denotes ha fa) : Denotes (.inl (B := B) ha)
      (fa ≫ J.map (coprod.inl ≫ (M.coprodIso _ _).inv))
  | inr (dhb : Denotes hb fb) : Denotes (.inr (A := A) hb)
      (fb ≫ J.map (coprod.inr ≫ (M.coprodIso _ _).inv))
  | case (dhe : Denotes he fe) (dhl : Denotes hl fl)
      (dhr : Denotes hr fr) : Denotes (.case he hl hr)
        (caseWithContext J (fe ≫ J.map (M.coprodIso _ _).hom) fl fr)
  | abort (dha : Denotes ha fa) : Denotes (.abort (A := A) ha) (abort J M fa)

private theorem denotes_exists {Γ : VCtx τ} {t : Tm Φ} {A : τ}
    (h : Tm.HasType Γ t A) : ∃ f, Denotes J M h f := by
  induction h with
  | var h => exact ⟨_, .var h⟩
  | op ha ih => rcases ih with ⟨fa, hfa⟩; exact ⟨_, .op hfa⟩
  | let₁ ha hb iha ihb =>
      rcases iha with ⟨fa, hfa⟩; rcases ihb with ⟨fb, hfb⟩
      exact ⟨_, .let₁ hfa hfb⟩
  | pair ha hb iha ihb =>
      rcases iha with ⟨fa, hfa⟩; rcases ihb with ⟨fb, hfb⟩
      exact ⟨_, .pair hfa hfb⟩
  | unit => exact ⟨_, .unit⟩
  | let₂ ha hb iha ihb =>
      rcases iha with ⟨fa, hfa⟩; rcases ihb with ⟨fb, hfb⟩
      exact ⟨_, .let₂ hfa hfb⟩
  | inl ha ih => rcases ih with ⟨fa, hfa⟩; exact ⟨_, .inl hfa⟩
  | inr hb ih => rcases ih with ⟨fb, hfb⟩; exact ⟨_, .inr hfb⟩
  | case he hl hr ihe ihl ihr =>
      rcases ihe with ⟨fe, hfe⟩; rcases ihl with ⟨fl, hfl⟩
      rcases ihr with ⟨fr, hfr⟩
      exact ⟨_, .case hfe hfl hfr⟩
  | abort ha ih => rcases ih with ⟨fa, hfa⟩; exact ⟨_, .abort hfa⟩

/-- Denotation of an exactly typed SSA expression.  The construction is
independent of region control flow and requires no iteration structure. -/
noncomputable def denote {Γ : VCtx τ} {t : Tm Φ} {A : τ}
    (h : Tm.HasType Γ t A) : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A) :=
  (denotes_exists J M h).choose

theorem denote_spec {Γ : VCtx τ} {t : Tm Φ} {A : τ}
    (h : Tm.HasType Γ t A) : Denotes J M h (denote J M h) :=
  (denotes_exists J M h).choose_spec

end Isotope.LambdaSSA.Semantics.Categorical
