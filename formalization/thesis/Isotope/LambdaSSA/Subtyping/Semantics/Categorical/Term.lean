import Isotope.LambdaSSA.Subtyping.Typing
import Isotope.LambdaSSA.Semantics.Term

/-! # Direct proof-relevant categorical semantics of subtyped SSA terms -/

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Isotope.LambdaSSA.Subtyping.Semantics.Categorical

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

open LambdaSSA.Semantics.Categorical

/-- Direct categorical interpretation.  In particular, `.sub h d` is
interpreted by the specific morphism `M.subty d`. -/
noncomputable def denote : {Γ : VCtx τ} → {t : LambdaSSA.Tm Φ} → {A : τ} →
    Tm.HasType Γ t A → (J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A))
  | _, _, _, .var h => J.map (lookup M _ h)
  | _, _, _, .op h => denote h ≫ InstructionModel.denote _
  | _, _, _, .let₁ ha hb => bind J (denote ha) (denote hb)
  | _, _, _, .pair ha hb =>
      pair J (denote ha) (denote hb) ≫ J.map (M.tensorIso _ _).inv
  | _, _, _, .unit =>
      J.map (CartesianMonoidalCategory.toUnit _ ≫ M.unitIso.inv)
  | _, _, _, .let₂ ha hb =>
      bind J (denote ha) <|
        J.map ((𝟙 _) ⊗ₘ (M.tensorIso _ _).hom) ≫
          J.map (ctxPairIso M _ _ _).hom ≫ denote hb
  | _, _, _, .inl ha =>
      denote ha ≫ J.map (coprod.inl ≫ (M.coprodIso _ _).inv)
  | _, _, _, .inr hb =>
      denote hb ≫ J.map (coprod.inr ≫ (M.coprodIso _ _).inv)
  | _, _, _, .case he hl hr =>
      caseWithContext J (denote he ≫ J.map (M.coprodIso _ _).hom)
        (denote hl) (denote hr)
  | _, _, _, .abort ha => abort J M (denote ha)
  | _, _, _, .sub ha d => denote ha ≫ J.map (M.subty d)

/-- Structural graph of the proof-relevant categorical term semantics. -/
inductive Denotes : {Γ : VCtx τ} → {t : LambdaSSA.Tm Φ} → {A : τ} →
    Tm.HasType Γ t A → (J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)) → Prop where
  | var (h : At Γ i A) : Denotes (.var h) (J.map (lookup M i h))
  | op (dha : Denotes ha fa) : Denotes (.op ha) (fa ≫ InstructionModel.denote _)
  | let₁ (dha : Denotes ha fa) (dhb : Denotes hb fb) :
      Denotes (.let₁ ha hb) (bind J fa fb)
  | pair (dha : Denotes ha fa) (dhb : Denotes hb fb) :
      Denotes (.pair ha hb) (pair J fa fb ≫ J.map (M.tensorIso _ _).inv)
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
  | case (dhe : Denotes he fe) (dhl : Denotes hl fl) (dhr : Denotes hr fr) :
      Denotes (.case he hl hr)
        (caseWithContext J (fe ≫ J.map (M.coprodIso _ _).hom) fl fr)
  | abort (dha : Denotes ha fa) :
      Denotes (.abort (A := A) ha) (abort J M fa)
  | sub {A B : τ} {ha : Tm.HasType Γ a A}
      {fa : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
      (dha : Denotes ha fa) (d : LambdaIter.Subty A B) :
      Denotes (.sub ha d) (fa ≫ J.map (M.subty d))

theorem denote_spec {Γ : VCtx τ} {t : LambdaSSA.Tm Φ} {A : τ}
    (h : Tm.HasType Γ t A) : Denotes J M h (denote J M h) := by
  induction h with
  | var h => exact .var h
  | op _ ih => exact .op ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | pair _ _ iha ihb => exact .pair iha ihb
  | unit => exact .unit
  | let₂ _ _ iha ihb => exact .let₂ iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ihe ihl ihr => exact .case ihe ihl ihr
  | abort _ ih => exact .abort ih
  | sub _ d ih => exact .sub ih d

theorem Denotes.eq_denote {Γ : VCtx τ} {t : LambdaSSA.Tm Φ} {A : τ}
    {h : Tm.HasType Γ t A} {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
    (d : Denotes J M h f) : f = denote J M h := by
  induction d <;> simp only [denote, *] <;> rfl

@[simp] theorem denote_sub {Γ : VCtx τ} {t : LambdaSSA.Tm Φ} {A B : τ}
    (h : Tm.HasType Γ t A) (d : LambdaIter.Subty A B) :
    denote J M (.sub h d) = denote J M h ≫ J.map (M.subty d) := rfl

end Isotope.LambdaSSA.Subtyping.Semantics.Categorical
