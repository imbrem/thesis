import Isotope.CategoryTheory.Monad.Elgot
import Isotope.LambdaIter.Subtyping.Semantics.Categorical
import Isotope.LambdaIter.Subtyping.Semantics.Denotation

/-!
# Agreement of categorical and monadic lambda-iter semantics

This file specializes the categorical interfaces to the set-valued model and its Kleisli
category.  The final agreement theorem is intentionally stated pointwise on the underlying
Kleisli arrow.
-/

universe u v w q r

namespace Isotope.LambdaIter.Subtyping.Semantics

open Isotope.LambdaIter.LocallyNameless
open Isotope.LambdaIter.Subtyping.LocallyNameless

open CategoryTheory CategoryTheory.Limits
open Isotope.Elgot
open Isotope.LambdaIter.LocallyNameless

namespace Categorical

variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable [Semantics.TypeModel.{u, v} τ]

private theorem types_coprodMap_comparison {X Y X' Y' : Type v}
    (f : X → X') (g : Y → Y') :
    coprod.map f g ≫ (Types.binaryCoproductIso X' Y').hom =
      (Types.binaryCoproductIso X Y).hom ≫ Sum.map f g := by
  apply coprod.hom_ext
  · simp only [coprod.inl_map_assoc, Category.assoc,
      Types.binaryCoproductIso_inl_comp_hom]
    rw [← Category.assoc, Types.binaryCoproductIso_inl_comp_hom]
    rfl
  · simp only [coprod.inr_map_assoc, Category.assoc,
      Types.binaryCoproductIso_inr_comp_hom]
    rw [← Category.assoc, Types.binaryCoproductIso_inr_comp_hom]
    rfl

/-- A set-valued type model is a categorical type model in `Type`. -/
@[reducible] noncomputable def ofTypeModel : Categorical.TypeModel τ (Type v) where
  obj := Semantics.TypeModel.interp
  tensorIso A B := Equiv.toIso (Semantics.TypeModel.tensorEquiv A B)
  unitIso :=
    { hom := fun _ => PUnit.unit
      inv := fun _ => Semantics.TypeModel.unitEquiv.symm ()
      hom_inv_id := by
        funext x
        exact Semantics.TypeModel.unitEquiv.injective
          (Semantics.TypeModel.unitEquiv.apply_symm_apply ())
      inv_hom_id := by funext x; cases x; rfl }
  coprodIso A B := (Equiv.toIso (Semantics.TypeModel.coprodEquiv A B)).trans
    (Types.binaryCoproductIso _ _).symm
  emptyIsInitial := IsInitial.ofUniqueHom
    (fun X z => Empty.elim (Semantics.TypeModel.emptyEquiv z))
    (fun X f => by funext z; exact Empty.elim (Semantics.TypeModel.emptyEquiv z))
  subty d := Semantics.TypeModel.coe d

private theorem ofTypeModel_coprodIso_hom_comparison (A B : τ) :
    ((ofTypeModel (τ := τ)).coprodIso A B).hom ≫
        (Types.binaryCoproductIso
          ((ofTypeModel (τ := τ)).obj A)
          ((ofTypeModel (τ := τ)).obj B)).hom =
      (Equiv.toIso (Semantics.TypeModel.coprodEquiv A B)).hom := by
  change (((Equiv.toIso (Semantics.TypeModel.coprodEquiv A B)).trans
      (Types.binaryCoproductIso _ _).symm).hom ≫
        (Types.binaryCoproductIso _ _).hom) = _
  simp [Category.assoc]

/-- The structural laws of a set-valued type model transport to the
categorical model in `Type`. -/
noncomputable instance ofTypeModelLawful [Semantics.LawfulTypeModel.{u, v} τ] :
    Categorical.LawfulTypeModel τ (Type v) (ofTypeModel (τ := τ)) where
  subty_refl A := by
    simpa [ofTypeModel] using Semantics.LawfulTypeModel.coe_refl A
  subty_trans f g := by
    simpa [ofTypeModel, Function.comp_def] using
      Semantics.LawfulTypeModel.coe_trans f g
  subty_tensor f g := by
    funext p
    simpa [ofTypeModel] using
      Semantics.LawfulTypeModel.coe_tensor f g p
  subty_coprod f g := by
    funext s
    apply_fun (Types.binaryCoproductIso _ _).hom
    · change (Semantics.TypeModel.coe (Subty.coprod f g) ≫
          ((ofTypeModel (τ := τ)).coprodIso _ _).hom ≫
          (Types.binaryCoproductIso _ _).hom) s =
        (((ofTypeModel (τ := τ)).coprodIso _ _).hom ≫
          coprod.map (Semantics.TypeModel.coe f) (Semantics.TypeModel.coe g) ≫
          (Types.binaryCoproductIso _ _).hom) s
      rw [ofTypeModel_coprodIso_hom_comparison]
      rw [types_coprodMap_comparison]
      rw [← Category.assoc, ofTypeModel_coprodIso_hom_comparison]
      change Semantics.TypeModel.coprodEquiv _ _
          (Semantics.TypeModel.coe (Subty.coprod f g) s) =
        Sum.map (Semantics.TypeModel.coe f) (Semantics.TypeModel.coe g)
          (Semantics.TypeModel.coprodEquiv _ _ s)
      exact Semantics.LawfulTypeModel.coe_coprod f g s
    · intro x y h
      simpa using congrArg (Types.binaryCoproductIso _ _).inv h
  subty_empty A := by
    funext z
    simpa [ofTypeModel] using
      Semantics.LawfulTypeModel.coe_empty A z
  subty_unit A := by
    rfl

/-- Optional proof irrelevance transports independently of the structural
laws. -/
noncomputable instance ofTypeModelSubtyProofIrrelevant
    [Semantics.SubtyProofIrrelevant.{u, v} τ] :
    Categorical.SubtyProofIrrelevant τ (Type v) (ofTypeModel (τ := τ)) where
  subty_eq f g := Semantics.SubtyProofIrrelevant.coe_eq f g

variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Semantics.InstructionModel Φ τ ε m]

/-- A monadic instruction interpretation is precisely a Kleisli instruction interpretation. -/
@[reducible] def ofInstructionModel : Categorical.InstructionModel
    (CategoryTheory.Kleisli.Adjunction.toKleisli (CategoryTheory.ofTypeMonad m))
    (ofTypeModel (τ := τ)) Φ where
  denote f := CategoryTheory.Kleisli.Hom.mk
    (by
      simpa [ofTypeModel, CategoryTheory.Kleisli.Adjunction.toKleisli] using
        (Semantics.InstructionModel.denote
          (Φ := Φ) (τ := τ) (ε := ε) (m := m) f))

variable {ν : Type w} [DecidableEq ν]
variable [Isotope.Elgot.Iterate m] [Isotope.Elgot.LawfulElgotMonad m]

@[simp] private theorem types_snd_apply {X Y : Type v} (p : X × Y) :
    CategoryTheory.CartesianMonoidalCategory.snd X Y p = p.2 := by rfl

@[simp] private theorem types_fst_apply {X Y : Type v} (p : X × Y) :
    CategoryTheory.CartesianMonoidalCategory.fst X Y p = p.1 := by rfl

/-- The categorical denotation specialized to a set-valued monadic model. -/
noncomputable def denoteOfType {Γ : Ctx ν τ} {n : Nat}
    {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A) :=
  letI := ofInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  Categorical.denote
    (CategoryTheory.Kleisli.Adjunction.toKleisli (CategoryTheory.ofTypeMonad m))
    (ofTypeModel (τ := τ)) h

end Categorical

variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable [Semantics.TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Semantics.InstructionModel Φ τ ε m]
variable {ν : Type w} [DecidableEq ν]
variable [Isotope.Elgot.Iterate m] [Isotope.Elgot.LawfulElgotMonad m]

/-- Canonical embedding of the existing nested-pair free environment into its categorical
interpretation.  This avoids requiring the syntactic and semantic universes to coincide. -/
def ctxToCategorical : {Γ : Ctx ν τ} → CtxDen Γ →
    Categorical.ctxObj (Categorical.ofTypeModel (τ := τ)) Γ
  | .nil, _ => PUnit.unit
  | .snoc Γ _ A, γ => (ctxToCategorical γ.1, γ.2)

/-- Canonical embedding of a bound environment into its categorical interpretation. -/
def boundToCategorical : {n : Nat} → {β : BoundCtx τ n} → BoundDen β →
    Categorical.boundObj (Categorical.ofTypeModel (τ := τ)) β
  | 0, .nil, _ => PUnit.unit
  | _ + 1, .snoc β A, ρ => (boundToCategorical ρ.1, ρ.2)

/-- Canonical complete categorical environment associated to the monadic environments. -/
def envToCategorical {n : Nat} {Γ : Ctx ν τ} {β : BoundCtx τ n}
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    Categorical.envObj (Categorical.ofTypeModel (τ := τ)) Γ β :=
  (ctxToCategorical γ, boundToCategorical ρ)

theorem ctxLookup_toCategorical {Γ : Ctx ν τ} (γ : CtxDen Γ)
    (x : ν) {A : τ} (h : Γ.lookup x = some A) :
    Categorical.ctxLookup (Categorical.ofTypeModel (τ := τ)) x h
        (ctxToCategorical γ) = CtxDen.lookup γ x h := by
  induction Γ generalizing A with
  | nil => simp [Ctx.lookup] at h
  | snoc Γ name B ih =>
      cases name with
      | none =>
          exact ih γ.1 h
      | some y =>
          by_cases hxy : x = y
          · subst y
            have hBA : B = A := by simpa [Ctx.lookup] using h
            subst A
            simp only [Categorical.ctxLookup, CtxDen.lookup, ctxToCategorical]
            simp
          · simp only [Categorical.ctxLookup, CtxDen.lookup, ctxToCategorical]
            simp only [dif_neg hxy]
            change Categorical.ctxLookup (Categorical.ofTypeModel (τ := τ)) x _
                (ctxToCategorical γ.1) = CtxDen.lookup γ.1 x _
            exact ih γ.1 (by simpa [Ctx.lookup, hxy] using h)

theorem freeLookup_toCategorical {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    (γ : CtxDen Γ) (ρ : BoundDen β) (x : ν) {A : τ}
    (h : Γ.lookup x = some A) :
    Categorical.freeLookup (Categorical.ofTypeModel (τ := τ)) x h
        (envToCategorical γ ρ) = CtxDen.lookup γ x h := by
  exact ctxLookup_toCategorical γ x h

theorem boundLookup_toCategorical {n : Nat} {β : BoundCtx τ n}
    (ρ : BoundDen β) (i : Fin n) :
    Categorical.boundLookup (Categorical.ofTypeModel (τ := τ)) i
        (boundToCategorical ρ) = BoundDen.get ρ i := by
  induction β with
  | nil => exact Fin.elim0 i
  | snoc β A ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact ih ρ.1 j

theorem boundVar_toCategorical {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    (γ : CtxDen Γ) (ρ : BoundDen β) (i : Fin n) :
    Categorical.boundVar (Categorical.ofTypeModel (τ := τ)) i
        (envToCategorical γ ρ) = BoundDen.get ρ i := by
  exact boundLookup_toCategorical ρ i

theorem envSnocIso_toCategorical {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    (γ : CtxDen Γ) (ρ : BoundDen β) {A : τ} (a : TyDen A) :
    (Categorical.envSnocIso (Categorical.ofTypeModel (τ := τ)) Γ β A).hom
        (envToCategorical γ ρ, a) = envToCategorical γ (ρ, a) := by rfl

theorem envPairHom_toCategorical {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    (γ : CtxDen Γ) (ρ : BoundDen β) {A B : τ} (a : TyDen A) (b : TyDen B) :
    Categorical.envPairHom (Categorical.ofTypeModel (τ := τ)) Γ β A B
        (envToCategorical γ ρ, (a, b)) = envToCategorical γ ((ρ, a), b) := by rfl

end Isotope.LambdaIter.Subtyping.Semantics
