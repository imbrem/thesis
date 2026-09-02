import Isotope.LambdaSSA.Semantics.Monadic.Term
import Isotope.LambdaSSA.Semantics.Term
import Isotope.LambdaIter.Subtyping.Semantics.Agreement.Combinators

namespace Isotope.LambdaSSA.Semantics

open CategoryTheory CategoryTheory.Limits Isotope.Elgot
open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics

universe u v q r

namespace Agreement

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [InstructionModel Φ τ ε m]

private abbrev J := Kleisli.Adjunction.toKleisli (CategoryTheory.ofTypeMonad m)
private noncomputable abbrev M := Categorical.ofTypeModel (τ := τ)

private theorem tensor_inv_agrees (A B : τ) (p : TyDen A × TyDen B) :
    ((M (τ := τ)).tensorIso A B).inv p =
      (TypeModel.tensorEquiv A B).symm p := rfl

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

private theorem coprod_hom_agrees (A B : τ) (e : TyDen (LambdaIter.coprod A B)) :
    (Types.binaryCoproductIso (TyDen A) (TyDen B)).hom
      (((M (τ := τ)).coprodIso A B).hom e) =
        TypeModel.coprodEquiv A B e := by
  change (Types.binaryCoproductIso _ _).hom
    (((Equiv.toIso (TypeModel.coprodEquiv A B)).trans
      (Types.binaryCoproductIso _ _).symm).hom e) = _
  simp

/-- The explicit identification between direct monadic environments and the
newest-first categorical interpretation of SSA contexts. -/
def envToCategorical : {Γ : VCtx τ} →
    Monadic.Env Γ → Categorical.ctxObj (M (τ := τ)) Γ
  | [], ρ => ρ
  | _ :: _, ρ => (envToCategorical ρ.1, ρ.2)

private theorem envPair_agrees {Γ : VCtx τ} {A B : τ} (ρ : Monadic.Env Γ)
    (ab : TyDen (LambdaIter.tensor A B)) :
    (Categorical.ctxPairIso (M (τ := τ)) Γ A B).hom
      (envToCategorical ρ, ((M (τ := τ)).tensorIso A B).hom ab) =
    let p := TypeModel.tensorEquiv A B ab
    envToCategorical ((ρ, p.1), p.2) := by rfl

private theorem lookup_agrees {Γ : VCtx τ} {A : τ} (i : Nat) (h : At Γ i A)
    (ρ : Monadic.Env Γ) :
    ((J (m := m)).map (Categorical.lookup (M (τ := τ)) i h)).of
        (envToCategorical ρ) = (pure (Monadic.Env.get ρ i h) : m _) := by
  induction Γ generalizing i with
  | nil => simp [At] at h
  | cons B Γ ih =>
      cases i with
      | zero =>
          simp [At] at h
          subst A
          rfl
      | succ i =>
          exact ih i h ρ.1

/-- Every witness of the direct monadic graph induces a witness of the
categorical graph specialized to the Kleisli/Freyd model, with pointwise equal
underlying functions.  No proof-irrelevance or typing-coherence assumption is
used. -/
theorem denotes_toCategorical {Γ : VCtx τ} {t : Tm Φ} {A : τ}
    {h : Tm.HasType Γ t A} {f : Monadic.Env Γ → m (TyDen A)}
    (d : Monadic.Denotes (m := m) ε h f) :
    letI := Categorical.ofInstructionModel
      (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    ∃ F, Categorical.Denotes (J (m := m)) (M (τ := τ)) h F ∧
      (fun ρ => F.of (envToCategorical ρ)) = f := by
  dsimp
  letI := Categorical.ofInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  induction d with
  | var h =>
      exact ⟨_, .var h, funext (lookup_agrees _ h)⟩
  | op d ih =>
      rcases ih with ⟨F, dF, eF⟩
      refine ⟨_, .op dF, ?_⟩
      funext ρ
      have hF := congrFun eF ρ
      simp [Kleisli.Type.comp_of_eq_kcomp, Categorical.ofInstructionModel,
        Isotope.Elgot.kcomp, joinM, bind_map_left, hF]
      rfl
  | let₁ da db iha ihb =>
      rcases iha with ⟨F, dF, eF⟩
      rcases ihb with ⟨G, dG, eG⟩
      refine ⟨_, .let₁ dF dG, ?_⟩
      funext ρ
      have hF := congrFun eF ρ
      have hG (a) := congrFun eG (ρ, a)
      simp [Categorical.bind_of, Isotope.Elgot.kcomp, joinM, bind_map_left, hF, hG]
      apply bind_congr
      exact hG
  | pair da db iha ihb =>
      rcases iha with ⟨F, dF, eF⟩
      rcases ihb with ⟨G, dG, eG⟩
      refine ⟨_, .pair dF dG, ?_⟩
      funext ρ
      have hF := congrFun eF ρ
      have hG := congrFun eG ρ
      simp [Categorical.pair_of, Categorical.comp_map_of, Categorical.ofTypeModel,
        Isotope.Elgot.kcomp, Isotope.Elgot.liftPure, joinM, bind_map_left, hF, hG]
      apply bind_congr
      intro a
      unfold M Categorical.ofTypeModel
      rfl
  | unit =>
      refine ⟨_, .unit, ?_⟩
      funext ρ
      rfl
  | let₂ da db iha ihb =>
      rcases iha with ⟨F, dF, eF⟩
      rcases ihb with ⟨G, dG, eG⟩
      refine ⟨_, .let₂ dF dG, ?_⟩
      funext ρ
      have hF := congrFun eF ρ
      have hG (a) (b) := congrFun eG ((ρ, a), b)
      simp [Categorical.bind_of, Categorical.comp_map_of, Categorical.ofTypeModel,
        Isotope.Elgot.kcomp, joinM, bind_map_left, hF]
      apply bind_congr
      intro ab
      rw [envPair_agrees]
      exact hG _ _
  | inl d ih =>
      rcases ih with ⟨F, dF, eF⟩
      refine ⟨_, .inl dF, ?_⟩
      funext ρ
      have hF := congrFun eF ρ
      simp [Categorical.comp_map_of, Categorical.ofTypeModel,
        Isotope.Elgot.kcomp, joinM, bind_map_left, hF]
      apply congrArg (fun k => k <$> _)
      funext a
      change ((M (τ := τ)).coprodIso _ _).inv
        ((Types.binaryCoproductIso _ _).inv (.inl a)) = _
      exact coprod_inv_inl_agrees _ _ a
  | inr d ih =>
      rcases ih with ⟨F, dF, eF⟩
      refine ⟨_, .inr dF, ?_⟩
      funext ρ
      have hF := congrFun eF ρ
      simp [Categorical.comp_map_of, Categorical.ofTypeModel,
        Isotope.Elgot.kcomp, joinM, bind_map_left, hF]
      apply congrArg (fun k => k <$> _)
      funext b
      change ((M (τ := τ)).coprodIso _ _).inv
        ((Types.binaryCoproductIso _ _).inv (.inr b)) = _
      exact coprod_inv_inr_agrees _ _ b
  | case de dl dr ihe ihl ihr =>
      rcases ihe with ⟨E, dE, eE⟩
      rcases ihl with ⟨L, dL, eL⟩
      rcases ihr with ⟨R, dR, eR⟩
      refine ⟨_, .case dE dL dR, ?_⟩
      funext ρ
      have hE := congrFun eE ρ
      have hL (a) := congrFun eL (ρ, a)
      have hR (b) := congrFun eR (ρ, b)
      simp [Categorical.caseWithContext_of, Categorical.comp_map_of,
        Categorical.ofTypeModel, Isotope.Elgot.kcomp, joinM, bind_map_left, hE]
      apply bind_congr
      intro e
      cases hcase : TypeModel.coprodEquiv _ _ e with
      | inl a =>
          simp only [Isotope.Elgot.liftPure, pure_bind]
          rw [coprod_hom_agrees, hcase]
          exact hL a
      | inr b =>
          simp only [Isotope.Elgot.liftPure, pure_bind]
          rw [coprod_hom_agrees, hcase]
          exact hR b
  | abort d ih =>
      rcases ih with ⟨F, dF, eF⟩
      refine ⟨_, .abort dF, ?_⟩
      funext ρ
      unfold Categorical.abort
      have hF := congrFun eF ρ
      simp [Categorical.ofTypeModel, Isotope.Elgot.kcomp, joinM, bind_map_left, hF]
      apply bind_congr
      intro z
      exact Empty.elim (TypeModel.emptyEquiv z)

end Agreement
end Isotope.LambdaSSA.Semantics
