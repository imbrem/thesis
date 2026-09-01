import Isotope.CategoryTheory.Monad.Elgot
import Isotope.LambdaIter.Semantics.Categorical
import Isotope.LambdaIter.Semantics.Denotation

/-!
# Agreement of categorical and monadic lambda-iter semantics

This file specializes the categorical interfaces to the set-valued model and its Kleisli
category.  The final agreement theorem is intentionally stated pointwise on the underlying
Kleisli arrow.
-/

universe u v w q r

namespace Isotope.LambdaIter.Semantics

open CategoryTheory CategoryTheory.Limits
open Isotope.Elgot
open Isotope.LambdaIter.LocallyNameless

namespace Categorical

variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable [Semantics.TypeModel.{u, v} τ]

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

/-- The structural laws of a set-valued type model transport to the
categorical model in `Type`. -/
noncomputable instance ofTypeModelLawful [Semantics.LawfulTypeModel.{u, v} τ] :
    Categorical.LawfulTypeModel τ (Type v) (ofTypeModel (τ := τ)) where
  subty_refl A := by
    simpa [ofTypeModel] using Semantics.LawfulTypeModel.coe_refl (v := v) A
  subty_trans f g := by
    simpa [ofTypeModel, Function.comp_def] using
      Semantics.LawfulTypeModel.coe_trans (v := v) f g
  subty_tensor f g := by
    funext p
    simpa [ofTypeModel] using
      Semantics.LawfulTypeModel.coe_tensor (v := v) f g p
  subty_coprod f g := by
    funext s
    simpa [ofTypeModel] using
      Semantics.LawfulTypeModel.coe_coprod (v := v) f g s
  subty_empty A := by
    funext z
    simpa [ofTypeModel] using
      Semantics.LawfulTypeModel.coe_empty (v := v) A z
  subty_unit A := by
    funext a
    simpa [ofTypeModel] using
      Semantics.LawfulTypeModel.coe_unit (v := v) A a

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

end Isotope.LambdaIter.Semantics
