import Isotope.LambdaSSA.Subtyping.Semantics.Categorical.Term
import Isotope.LambdaSSA.Semantics.Region

/-! # Proof-relevant categorical semantics of subtyped SSA regions -/

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Isotope.LambdaSSA.Subtyping.Semantics.Categorical

set_option autoImplicit true
set_option relaxedAutoImplicit true

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.PremonoidalCategory
open Isotope.LambdaIter.Subtyping.Semantics.Categorical
open scoped MonoidalCategory
open LambdaSSA.Semantics.Categorical

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
  (M : TypeModel τ V)
  {Φ : Type u₄} [LambdaIter.HasTy Φ τ] [InstructionModel J M Φ]

/-- Structural denotation graph.  Unlike exact SSA, its term premises use the
proof-relevant denotation and therefore retain every coercion witness. -/
inductive RegionDenotes : {Γ : VCtx τ} → {r : LambdaSSA.Region Φ} → {L : LCtx τ} →
    Region.HasType Γ r L → (J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)) → Prop where
  | br : RegionDenotes (.br h ha)
      (denote J M ha ≫ J.map (labelInject M _ h))
  | case (dl : RegionDenotes hl fl) (dr : RegionDenotes hr fr) :
      RegionDenotes (.case he hl hr)
        (caseWithContext J
          (denote J M he ≫ J.map (M.coprodIso _ _).hom) fl fr)
  | let₁ (db : RegionDenotes hb fb) :
      RegionDenotes (.let₁ ha hb) (bind J (denote J M ha) fb)
  | let₂ (db : RegionDenotes hb fb) :
      RegionDenotes (.let₂ ha hb) (bind J (denote J M ha) (
        J.map ((𝟙 _) ⊗ₘ (M.tensorIso _ _).hom) ≫
          J.map (ctxPairIso M _ _ _).hom ≫ fb))
  | cfgZero {R : Fin 0 → τ} {entry : LambdaSSA.Region Φ}
      {blocks : Fin 0 → LambdaSSA.Region Φ}
      {he : Region.HasType Γ entry (List.ofFn R ++ L)}
      {hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)}
      {fe : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
      (de : RegionDenotes he fe) :
      RegionDenotes (.cfg R he hb) fe
  | cfg {n : Nat} {R : Fin n → τ} {Γ : VCtx τ} {L : LCtx τ}
      {entry : LambdaSSA.Region Φ} {blocks : Fin n → LambdaSSA.Region Φ}
      {he : Region.HasType Γ entry (List.ofFn R ++ L)}
      {hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)}
      {fe : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (List.ofFn R ++ L))}
      {fb : ∀ i, J.obj (ctxObj M (R i :: Γ)) ⟶
        J.obj (labelObj M (List.ofFn R ++ L))}
      {collective : J.obj (ctxObj M Γ ⊗ finiteLabelObj M R) ⟶
        J.obj (labelObj M (List.ofFn R ++ L))}
      (de : RegionDenotes he fe)
      (db : ∀ i, RegionDenotes (hb i) (fb i))
      (dc : LambdaSSA.Semantics.Categorical.CollectiveDenotes J M Γ R L fb collective) :
      RegionDenotes (.cfg R he hb) (caseWithContext J
        (fe ≫ J.map (labelAppendSplit M (List.ofFn R) L))
        (J.map (CartesianMonoidalCategory.snd _ _))
        (contextualLoop J
          (J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ labelObjToFinite M R) ≫
            collective ≫ J.map (labelAppendSplit M (List.ofFn R) L))))

private theorem exists_denotation { Γ : VCtx τ} {r : LambdaSSA.Region Φ} {L : LCtx τ}
    (h : Region.HasType Γ r L) : ∃ f, RegionDenotes J M h f := by
  induction h with
  | br h ha => exact ⟨_, .br (h := h)⟩
  | case he hl hr ihl ihr =>
      rcases ihl with ⟨fl, dl⟩
      rcases ihr with ⟨fr, dr⟩
      exact ⟨_, .case dl dr⟩
  | let₁ ha hb ih =>
      rcases ih with ⟨fb, db⟩
      exact ⟨_, .let₁ db⟩
  | let₂ ha hb ih =>
      rcases ih with ⟨fb, db⟩
      exact ⟨_, .let₂ db⟩
  | @cfg _ _ _ n _ R he hb ihe ihb =>
      cases n with
      | zero =>
          rcases ihe with ⟨fe, de⟩
          exact ⟨fe, .cfgZero de⟩
      | succ n =>
          rcases ihe with ⟨fe, de⟩
          choose fb db using ihb
          rcases collectiveDenotes_exists_succ J M n _ R _ fb with ⟨fc, dc⟩
          exact ⟨_, .cfg de db dc⟩

/-- Chosen categorical denotation of a proof-relevant SSA region. -/
noncomputable def denoteRegion {Γ : VCtx τ} {r : LambdaSSA.Region Φ} {L : LCtx τ}
    (h : Region.HasType Γ r L) : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L) :=
  (exists_denotation J M h).choose

theorem denoteRegion_spec {Γ : VCtx τ} {r : LambdaSSA.Region Φ} {L : LCtx τ}
    (h : Region.HasType Γ r L) : RegionDenotes J M h (denoteRegion J M h) :=
  (exists_denotation J M h).choose_spec

end Isotope.LambdaSSA.Subtyping.Semantics.Categorical
