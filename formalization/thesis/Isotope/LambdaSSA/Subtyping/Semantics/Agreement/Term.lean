import Isotope.LambdaSSA.Subtyping.Semantics.Monadic.Term
import Isotope.LambdaSSA.Subtyping.Semantics.Categorical.Term
import Isotope.LambdaIter.Subtyping.Semantics.Agreement.Combinators

namespace Isotope.LambdaSSA.Subtyping.Semantics

open CategoryTheory CategoryTheory.Limits Isotope.Elgot
open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics

universe u v q r

namespace Agreement

variable {τ : Type u} [TypeFormers τ] [LambdaIter.Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [InstructionModel Φ τ ε m]

private abbrev J := Kleisli.Adjunction.toKleisli (CategoryTheory.ofTypeMonad m)
private noncomputable abbrev M :=
  Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofTypeModel (τ := τ)

private theorem coprod_inv_inl_agrees (A B : τ) (a : TyDen A) :
    ((M (τ := τ)).coprodIso A B).inv
      ((Types.binaryCoproductIso (TyDen A) (TyDen B)).inv (.inl a)) =
      (TypeModel.coprodEquiv A B).symm (.inl a) := by
  change (((Equiv.toIso (TypeModel.coprodEquiv A B)).trans
    (Types.binaryCoproductIso _ _).symm).inv
      ((Types.binaryCoproductIso _ _).inv (.inl a))) = _
  simp

private theorem coprod_inv_inr_agrees (A B : τ) (b : TyDen B) :
    ((M (τ := τ)).coprodIso A B).inv
      ((Types.binaryCoproductIso (TyDen A) (TyDen B)).inv (.inr b)) =
      (TypeModel.coprodEquiv A B).symm (.inr b) := by
  change (((Equiv.toIso (TypeModel.coprodEquiv A B)).trans
    (Types.binaryCoproductIso _ _).symm).inv
      ((Types.binaryCoproductIso _ _).inv (.inr b))) = _
  simp

private theorem coprod_hom_agrees (A B : τ) (e : TyDen (coprod A B)) :
    (Types.binaryCoproductIso ((M (τ := τ)).obj A) ((M (τ := τ)).obj B)).hom
      (((M (τ := τ)).coprodIso A B).hom e) = TypeModel.coprodEquiv A B e := by
  change (Types.binaryCoproductIso _ _).hom
    (((Equiv.toIso (TypeModel.coprodEquiv A B)).trans
      (Types.binaryCoproductIso _ _).symm).hom e) = _
  simp

def envToCategorical : {Γ : VCtx τ} →
    Monadic.Env Γ → LambdaSSA.Semantics.Categorical.ctxObj (M (τ := τ)) Γ
  | [], ρ => ρ
  | _ :: _, ρ => (envToCategorical ρ.1, ρ.2)

private theorem envPair_agrees {Γ : VCtx τ} {A B : τ} (ρ : Monadic.Env Γ)
    (ab : TyDen (tensor A B)) :
    (LambdaSSA.Semantics.Categorical.ctxPairIso (M (τ := τ)) Γ A B).hom
      (envToCategorical ρ, ((M (τ := τ)).tensorIso A B).hom ab) =
    let p := TypeModel.tensorEquiv A B ab
    envToCategorical ((ρ, p.1), p.2) := by rfl

private theorem lookup_agrees {Γ : VCtx τ} {A : τ} (i : Nat) (h : At Γ i A)
    (ρ : Monadic.Env Γ) :
    ((J (m := m)).map (LambdaSSA.Semantics.Categorical.lookup (M (τ := τ)) i h)).of
        (envToCategorical ρ) = (pure (LambdaSSA.Semantics.Monadic.Env.get ρ i h) : m _) := by
  induction Γ generalizing i with
  | nil => simp [At] at h
  | cons B Γ ih =>
      cases i with
      | zero => simp [At] at h; subst A; rfl
      | succ i => exact ih i h ρ.1

/-- The direct proof-relevant monadic and categorical term interpretations
agree in the Kleisli model, without proof irrelevance for subtype witnesses. -/
theorem denotes_toCategorical {Γ : VCtx τ} {t : LambdaSSA.Tm Φ} {A : τ}
    {h : Tm.HasType Γ t A} {f : Monadic.Env Γ → m (TyDen A)}
    (d : Monadic.Denotes ε h f) :
    letI := Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofInstructionModel
      (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    ∃ F, Isotope.LambdaSSA.Subtyping.Semantics.Categorical.Denotes
      (J (m := m)) (M (τ := τ)) h F ∧
      (fun ρ => F.of (envToCategorical ρ)) = f := by
  dsimp
  letI := Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  induction d with
  | var h => exact ⟨_, .var h, funext (lookup_agrees _ h)⟩
  | op d ih =>
      rcases ih with ⟨F, dF, eF⟩
      refine ⟨_, .op dF, ?_⟩
      funext ρ
      have hF := congrFun eF ρ
      simp [Kleisli.Type.comp_of_eq_kcomp,
        Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofInstructionModel,
        Isotope.Elgot.kcomp, joinM, bind_map_left, hF]
      rfl
  | let₁ da db iha ihb =>
      rcases iha with ⟨F, dF, eF⟩
      rcases ihb with ⟨G, dG, eG⟩
      refine ⟨_, .let₁ dF dG, ?_⟩
      funext ρ
      simp [Isotope.LambdaIter.Subtyping.Semantics.Categorical.bind_of,
        Isotope.Elgot.kcomp, congrFun eF ρ]
      apply bind_congr
      exact fun a => congrFun eG (ρ, a)
  | pair da db iha ihb =>
      rcases iha with ⟨F, dF, eF⟩
      rcases ihb with ⟨G, dG, eG⟩
      refine ⟨_, .pair dF dG, ?_⟩
      funext ρ
      simp [Isotope.LambdaIter.Subtyping.Semantics.Categorical.pair_of,
        Isotope.LambdaIter.Subtyping.Semantics.Categorical.comp_map_of,
        Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofTypeModel,
        Isotope.Elgot.kcomp, Isotope.Elgot.liftPure, joinM, bind_map_left,
        congrFun eF ρ, congrFun eG ρ]
      apply bind_congr
      intro a
      unfold M Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofTypeModel
      rfl
  | unit => exact ⟨_, .unit, rfl⟩
  | let₂ da db iha ihb =>
      rcases iha with ⟨F, dF, eF⟩
      rcases ihb with ⟨G, dG, eG⟩
      refine ⟨_, .let₂ dF dG, ?_⟩
      funext ρ
      simp [Isotope.LambdaIter.Subtyping.Semantics.Categorical.bind_of,
        Isotope.LambdaIter.Subtyping.Semantics.Categorical.comp_map_of,
        Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofTypeModel,
        Isotope.Elgot.kcomp, joinM, bind_map_left, congrFun eF ρ]
      apply bind_congr
      intro ab
      rw [envPair_agrees]
      exact congrFun eG _
  | inl d ih =>
      rcases ih with ⟨F, dF, eF⟩
      refine ⟨_, .inl dF, ?_⟩
      funext ρ
      simp [Isotope.LambdaIter.Subtyping.Semantics.Categorical.comp_map_of,
        Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofTypeModel,
        Isotope.Elgot.kcomp, joinM, bind_map_left, congrFun eF ρ]
      apply congrArg (fun k => k <$> _)
      funext a
      exact coprod_inv_inl_agrees _ _ a
  | inr d ih =>
      rcases ih with ⟨F, dF, eF⟩
      refine ⟨_, .inr dF, ?_⟩
      funext ρ
      simp [Isotope.LambdaIter.Subtyping.Semantics.Categorical.comp_map_of,
        Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofTypeModel,
        Isotope.Elgot.kcomp, joinM, bind_map_left, congrFun eF ρ]
      apply congrArg (fun k => k <$> _)
      funext b
      exact coprod_inv_inr_agrees _ _ b
  | case de dl dr ihe ihl ihr =>
      rcases ihe with ⟨E, dE, eE⟩
      rcases ihl with ⟨L, dL, eL⟩
      rcases ihr with ⟨R, dR, eR⟩
      refine ⟨_, .case dE dL dR, ?_⟩
      funext ρ
      simp [Isotope.LambdaIter.Subtyping.Semantics.Categorical.caseWithContext_of,
        Isotope.LambdaIter.Subtyping.Semantics.Categorical.comp_map_of,
        Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofTypeModel,
        Isotope.Elgot.kcomp, joinM, bind_map_left, congrFun eE ρ]
      apply bind_congr
      intro e
      cases hcase : TypeModel.coprodEquiv _ _ e with
      | inl a =>
          simp only [Isotope.Elgot.liftPure, Function.comp_apply, pure_bind]
          generalize hs : (Types.binaryCoproductIso _ _).hom
            (((M (τ := τ)).coprodIso _ _).hom e) = s
          cases s with
          | inl x =>
              have hx : x = a := Sum.inl.inj
                (hs.symm.trans ((coprod_hom_agrees _ _ e).trans hcase))
              subst x
              simpa [envToCategorical] using congrFun eL (ρ, a)
          | inr y =>
              have contra := hs.symm.trans ((coprod_hom_agrees _ _ e).trans hcase)
              cases contra
      | inr b =>
          simp only [Isotope.Elgot.liftPure, Function.comp_apply, pure_bind]
          generalize hs : (Types.binaryCoproductIso _ _).hom
            (((M (τ := τ)).coprodIso _ _).hom e) = s
          cases s with
          | inl x =>
              have contra := hs.symm.trans ((coprod_hom_agrees _ _ e).trans hcase)
              cases contra
          | inr y =>
              have hy : y = b := Sum.inr.inj
                (hs.symm.trans ((coprod_hom_agrees _ _ e).trans hcase))
              subst y
              simpa [envToCategorical] using congrFun eR (ρ, b)
  | abort d ih =>
      rcases ih with ⟨F, dF, eF⟩
      refine ⟨_, .abort dF, ?_⟩
      funext ρ
      unfold Isotope.LambdaIter.Subtyping.Semantics.Categorical.abort
      simp [Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofTypeModel,
        Isotope.Elgot.kcomp, joinM, bind_map_left, congrFun eF ρ]
      apply bind_congr
      intro z
      exact Empty.elim (TypeModel.emptyEquiv z)
  | sub d witness ih =>
      rcases ih with ⟨F, dF, eF⟩
      refine ⟨_, .sub dF witness, ?_⟩
      funext ρ
      rw [Kleisli.Type.comp_of_eq_kcomp]
      simp [Isotope.Elgot.kcomp,
        Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofTypeModel,
        congrFun eF ρ, coeSub]
      rw [← bind_pure_comp]
      apply bind_congr
      intro a
      rfl

/-- Compatibility for the chosen direct denotations. -/
theorem denote_agrees {Γ : VCtx τ} {t : LambdaSSA.Tm Φ} {A : τ}
    (h : Tm.HasType Γ t A) :
    letI := Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofInstructionModel
      (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    (fun ρ => (Isotope.LambdaSSA.Subtyping.Semantics.Categorical.denote
      (J (m := m)) (M (τ := τ)) h).of
      (envToCategorical ρ)) = Monadic.denote (ε := ε) (m := m) h := by
  dsimp
  letI := Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  rcases denotes_toCategorical (Monadic.denote_spec (ε := ε) (m := m) h) with
    ⟨F, dF, hF⟩
  have hchosen := Isotope.LambdaSSA.Subtyping.Semantics.Categorical.Denotes.eq_denote
    (J := J (m := m)) (M := M (τ := τ)) dF
  simpa [hchosen] using hF

end Agreement
end Isotope.LambdaSSA.Subtyping.Semantics
