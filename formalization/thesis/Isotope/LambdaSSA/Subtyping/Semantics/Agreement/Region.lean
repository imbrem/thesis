import Isotope.LambdaSSA.Subtyping.Semantics.Monadic.Region
import Isotope.LambdaSSA.Subtyping.Semantics.Categorical.Region
import Isotope.LambdaSSA.Subtyping.Semantics.Agreement.Term
import Isotope.LambdaIter.Subtyping.Semantics.Agreement.Iteration

/-! # Agreement of direct and categorical lambda-SSA region semantics -/

namespace Isotope.LambdaSSA.Subtyping.Semantics

open CategoryTheory CategoryTheory.Limits Isotope.Elgot
open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics

universe u v q r

namespace Agreement

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Iterate m] [LawfulElgotMonad m] [InstructionModel Φ τ ε m]

private abbrev J := Kleisli.Adjunction.toKleisli (CategoryTheory.ofTypeMonad m)
private noncomputable abbrev M := Categorical.ofTypeModel (τ := τ)

private def envFromCategorical : {Γ : VCtx τ} →
    Isotope.LambdaSSA.Semantics.Categorical.ctxObj (M (τ := τ)) Γ → Isotope.LambdaSSA.Semantics.Monadic.Env Γ
  | [], ρ => ρ
  | _ :: _, ρ => (envFromCategorical ρ.1, ρ.2)

@[simp] private theorem envFrom_to {Γ : VCtx τ} (ρ : Isotope.LambdaSSA.Semantics.Monadic.Env Γ) :
    envFromCategorical (envToCategorical ρ) = ρ := by
  induction Γ with
  | nil => rfl
  | cons _ _ ih => simp [envFromCategorical, envToCategorical, ih]

@[simp] private theorem envTo_from {Γ : VCtx τ}
    (ρ : Isotope.LambdaSSA.Semantics.Categorical.ctxObj (M (τ := τ)) Γ) :
    envToCategorical (envFromCategorical ρ) = ρ := by
  induction Γ with
  | nil => rfl
  | cons _ _ ih => simp [envFromCategorical, envToCategorical, ih]

private theorem coprod_hom_agrees (A B : τ)
    (e : TyDen (LambdaIter.coprod A B)) :
    (Types.binaryCoproductIso ((M (τ := τ)).obj A) ((M (τ := τ)).obj B)).hom
      (((M (τ := τ)).coprodIso A B).hom e) =
        TypeModel.coprodEquiv A B e := by
  change (Types.binaryCoproductIso _ _).hom
    (((Equiv.toIso (TypeModel.coprodEquiv A B)).trans
      (Types.binaryCoproductIso _ _).symm).hom e) = _
  simp

private theorem envPair_agrees {Γ : VCtx τ} {A B : τ} (ρ : Isotope.LambdaSSA.Semantics.Monadic.Env Γ)
    (ab : TyDen (LambdaIter.tensor A B)) :
    (Isotope.LambdaSSA.Semantics.Categorical.ctxPairIso (M (τ := τ)) Γ A B).hom
      (envToCategorical ρ, ((M (τ := τ)).tensorIso A B).hom ab) =
    let p := TypeModel.tensorEquiv A B ab
    envToCategorical ((ρ, p.1), p.2) := by rfl

private theorem collective_toCategorical {Γ : VCtx τ} {n : Nat}
    {R : Fin n → τ} {L : LCtx τ}
    {fb : ∀ i, Isotope.LambdaSSA.Semantics.Monadic.Env (R i :: Γ) →
      m (Monadic.LabelDen (List.ofFn R ++ L))}
    {collective : Isotope.LambdaSSA.Semantics.Monadic.Env Γ × Isotope.LambdaSSA.Semantics.Monadic.FiniteLabelDen R →
      m (Monadic.LabelDen (List.ofFn R ++ L))}
    (dc : Monadic.CollectiveDenotes Γ R L fb collective)
    {FB : ∀ i, (J (m := m)).obj (Isotope.LambdaSSA.Semantics.Categorical.ctxObj (M (τ := τ)) (R i :: Γ)) ⟶
      (J (m := m)).obj (Isotope.LambdaSSA.Semantics.Categorical.labelObj (M (τ := τ)) (List.ofFn R ++ L))}
    (eFB : ∀ i ρ, (FB i).of (envToCategorical ρ) =
      (fb i ρ >>= fun x =>
        (pure (Isotope.LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv (List.ofFn R ++ L) x) :
          m (Isotope.LambdaSSA.Semantics.Categorical.labelObj (M (τ := τ)) (List.ofFn R ++ L))))) :
    Isotope.LambdaSSA.Semantics.Categorical.CollectiveDenotes (J (m := m)) (M (τ := τ)) Γ R L FB
      (Kleisli.Hom.mk (fun p =>
        (show m (Isotope.LambdaSSA.Semantics.Categorical.labelObj (M (τ := τ)) (List.ofFn R ++ L)) from
        collective (envFromCategorical p.1,
            (Isotope.LambdaSSA.Semantics.Monadic.finiteCategoricalEquiv R).symm p.2) >>= fun x =>
          (pure (Isotope.LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv (List.ofFn R ++ L) x) :
            m (Isotope.LambdaSSA.Semantics.Categorical.labelObj (M (τ := τ)) (List.ofFn R ++ L)))))) := by
  constructor
  intro i
  ext p
  rcases p with ⟨ρ, a⟩
  rw [Kleisli.Type.comp_of_eq_kcomp]
  simp [Isotope.Elgot.kcomp, envFromCategorical]
  have hfinite : (Isotope.LambdaSSA.Semantics.Monadic.finiteCategoricalEquiv R).symm
      (Isotope.LambdaSSA.Semantics.Categorical.finiteLabelInject (M (τ := τ)) R i a) =
      Isotope.LambdaSSA.Semantics.Monadic.finiteLabelInject R i a := by
    unfold Isotope.LambdaSSA.Semantics.Monadic.finiteCategoricalEquiv Isotope.LambdaSSA.Semantics.Categorical.finiteLabelInject
    apply CofanTypes.equivOfIsColimit_symm_apply
  rw [hfinite]
  rw [dc.restrict]
  simpa [envToCategorical] using (eFB i (envFromCategorical ρ, a)).symm

/-- A direct monadic region witness induces a categorical witness in the
Kleisli/Freyd model with the same result on corresponding environments. -/
theorem regionDenotes_toCategorical {Γ : VCtx τ} {region : Region Φ} {L : LCtx τ}
    {h : Region.HasType Γ region L}
    {f : Isotope.LambdaSSA.Semantics.Monadic.Env Γ → m (Monadic.LabelDen L)}
    (d : Monadic.RegionDenotes (m := m) ε h f) :
    letI := Categorical.ofInstructionModel
      (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    ∃ F, Categorical.RegionDenotes (J (m := m)) (M (τ := τ)) h F ∧
      (fun ρ => F.of (envToCategorical ρ)) =
        (fun ρ => f ρ >>= fun x => pure (Isotope.LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv L x)) := by
  dsimp
  letI := Categorical.ofInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  induction d with
  | br dt =>
      rcases denotes_toCategorical dt with ⟨F, dF, eF⟩
      refine ⟨_, Categorical.RegionDenotes.br (h := by assumption) dF, ?_⟩
      funext ρ
      rw [Kleisli.Type.comp_of_eq_kcomp]
      simp [Isotope.Elgot.kcomp, Isotope.LambdaSSA.Semantics.Monadic.labelInject,
        congrFun eF ρ]
      exact bind_pure_comp _ _
  | case de dl dr ihl ihr =>
      rcases denotes_toCategorical de with ⟨E, dE, eE⟩
      rcases ihl with ⟨FL, dFL, eFL⟩
      rcases ihr with ⟨FR, dFR, eFR⟩
      refine ⟨_, .case dE dFL dFR, ?_⟩
      funext ρ
      rw [Isotope.LambdaIter.Subtyping.Semantics.Categorical.caseWithContext_of]
      simp [Isotope.LambdaIter.Subtyping.Semantics.Categorical.comp_map_of, Categorical.ofTypeModel,
        Isotope.Elgot.kcomp, joinM, bind_map_left, congrFun eE ρ]
      apply bind_congr
      intro e
      cases he : TypeModel.coprodEquiv _ _ e with
      | inl a =>
          simp only [Isotope.Elgot.liftPure, Function.comp_apply, pure_bind]
          rw [coprod_hom_agrees, he]
          simpa [envToCategorical, bind_pure_comp] using congrFun eFL (ρ, a)
      | inr b =>
          simp only [Isotope.Elgot.liftPure, Function.comp_apply, pure_bind]
          rw [coprod_hom_agrees, he]
          simpa [envToCategorical, bind_pure_comp] using congrFun eFR (ρ, b)
  | let₁ da db ihb =>
      rcases denotes_toCategorical da with ⟨F, dF, eF⟩
      rcases ihb with ⟨G, dG, eG⟩
      refine ⟨_, .let₁ dF dG, ?_⟩
      funext ρ
      rw [Isotope.LambdaIter.Subtyping.Semantics.Categorical.bind_of]
      simp [Isotope.Elgot.kcomp, congrFun eF ρ]
      apply bind_congr
      intro a
      simpa [envToCategorical, bind_pure_comp] using congrFun eG (ρ, a)
  | let₂ da db ihb =>
      rcases denotes_toCategorical da with ⟨F, dF, eF⟩
      rcases ihb with ⟨G, dG, eG⟩
      refine ⟨_, .let₂ dF dG, ?_⟩
      funext ρ
      simp [Isotope.LambdaIter.Subtyping.Semantics.Categorical.bind_of,
        Isotope.LambdaIter.Subtyping.Semantics.Categorical.comp_map_of, Categorical.ofTypeModel,
        Isotope.Elgot.kcomp, joinM, bind_map_left, congrFun eF ρ]
      apply bind_congr
      intro ab
      rw [envPair_agrees]
      simpa [bind_pure_comp] using congrFun eG _
  | cfgZero he hb de ih =>
      rcases ih with ⟨F, dF, eF⟩
      exact ⟨F, .cfgZero dF, eF⟩
  | cfg he hb de db dc ihe ihb =>
      rcases ihe with ⟨FE, dFE, eFE⟩
      choose FB dFB eFB using ihb
      rename_i n R Γ L entry blocks fe fb collective
      let FC : (J (m := m)).obj (Isotope.LambdaSSA.Semantics.Categorical.ctxObj (M (τ := τ)) Γ ×
          Isotope.LambdaSSA.Semantics.Categorical.finiteLabelObj (M (τ := τ)) R) ⟶
          (J (m := m)).obj (Isotope.LambdaSSA.Semantics.Categorical.labelObj (M (τ := τ))
            (List.ofFn R ++ L)) := Kleisli.Hom.mk (fun
        (p : Isotope.LambdaSSA.Semantics.Categorical.ctxObj (M (τ := τ)) Γ ×
          Isotope.LambdaSSA.Semantics.Categorical.finiteLabelObj (M (τ := τ)) R) =>
        (show m (Isotope.LambdaSSA.Semantics.Categorical.labelObj (M (τ := τ)) (List.ofFn R ++ L)) from
        collective (envFromCategorical p.1,
            (Isotope.LambdaSSA.Semantics.Monadic.finiteCategoricalEquiv R).symm p.2) >>= fun x =>
          (pure (Isotope.LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv (List.ofFn R ++ L) x) :
            m (Isotope.LambdaSSA.Semantics.Categorical.labelObj (M (τ := τ)) (List.ofFn R ++ L)))))
      have dFC : Isotope.LambdaSSA.Semantics.Categorical.CollectiveDenotes (J (m := m)) (M (τ := τ))
          Γ R L FB FC := collective_toCategorical dc (fun i ρ => congrFun (eFB i) ρ)
      refine ⟨_, .cfg dFE dFB dFC, ?_⟩
      funext ρ
      rw [Isotope.LambdaIter.Subtyping.Semantics.Categorical.caseWithContext_of]
      simp [Isotope.LambdaIter.Subtyping.Semantics.Categorical.comp_map_of,
        Isotope.LambdaSSA.Semantics.Monadic.labelAppendSplit,
        Isotope.Elgot.kcomp, Isotope.Elgot.liftPure, joinM, bind_map_left,
        bind_pure_comp, congrFun eFE ρ]
      apply bind_congr
      intro target
      rw [Isotope.LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv_appendSplit]
      generalize hsM : Isotope.LambdaSSA.Semantics.Monadic.LabelValue.appendSplit (List.ofFn R) L target = destination
      cases destination with
      | inl external =>
          simp [hsM]
      | inr loopTarget =>
          have hinr := congrFun (Types.binaryCoproductIso_inr_comp_hom
            (Isotope.LambdaSSA.Semantics.Categorical.labelObj (M (τ := τ)) L)
            (Isotope.LambdaSSA.Semantics.Categorical.labelObj (M (τ := τ)) (List.ofFn R)))
            (Isotope.LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv (List.ofFn R) loopTarget)
          change
            (Types.binaryCoproductIso
              (Isotope.LambdaSSA.Semantics.Categorical.labelObj (M (τ := τ)) L)
              (Isotope.LambdaSSA.Semantics.Categorical.labelObj (M (τ := τ)) (List.ofFn R))).hom
                ((coprod.inr :
                    Isotope.LambdaSSA.Semantics.Categorical.labelObj (M (τ := τ)) (List.ofFn R) ⟶
                      Isotope.LambdaSSA.Semantics.Categorical.labelObj (M (τ := τ)) L ⨿
                        Isotope.LambdaSSA.Semantics.Categorical.labelObj (M (τ := τ)) (List.ofFn R))
                  (Isotope.LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv
                    (List.ofFn R) loopTarget)) =
              Sum.inr (Isotope.LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv
                (List.ofFn R) loopTarget) at hinr
          simp only
          rw [hinr]
          simp only
          rw [Isotope.LambdaIter.Subtyping.Semantics.Categorical.contextualLoop_of]
          let f := fun current =>
            Isotope.LambdaSSA.Semantics.Monadic.LabelValue.appendSplit (List.ofFn R) L <$>
              collective (ρ, Isotope.LambdaSSA.Semantics.Monadic.labelDenToFinite R current)
          let g := fun current =>
            Isotope.Elgot.kcomp (m := m)
              (J.map (MonoidalCategoryStruct.whiskerLeft
                    (Isotope.LambdaSSA.Semantics.Categorical.ctxObj (M (τ := τ)) Γ)
                    (Isotope.LambdaSSA.Semantics.Categorical.labelObjToFinite (M (τ := τ)) R)) ≫ FC ≫
                J.map (Isotope.LambdaSSA.Semantics.Categorical.labelAppendSplit
                  (M (τ := τ)) (List.ofFn R) L)).of
              (fun s => pure ((Types.binaryCoproductIso
                (Isotope.LambdaSSA.Semantics.Categorical.labelObj (M (τ := τ)) L)
                (Isotope.LambdaSSA.Semantics.Categorical.labelObj (M (τ := τ)) (List.ofFn R))).hom s))
              (envToCategorical ρ, current)
          let k : Isotope.LambdaSSA.Semantics.Monadic.LabelValue L →
              m (Isotope.LambdaSSA.Semantics.Categorical.labelObj (M (τ := τ)) L) :=
            fun x => pure (Isotope.LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv L x)
          change Isotope.Elgot.iter (m := m) g
              (Isotope.LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv (List.ofFn R) loopTarget) =
            (Isotope.LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv L) <$>
              Isotope.Elgot.iter (m := m) f loopTarget
          rw [show (Isotope.LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv L) <$>
                Isotope.Elgot.iter (m := m) f loopTarget =
              Isotope.Elgot.kcomp (Isotope.Elgot.iter (m := m) f) k loopTarget by
            simp [Isotope.Elgot.kcomp, k]]
          rw [LawfulElgotMonad.naturality]
          symm
          have hcomm :
              Isotope.Elgot.kcomp (Isotope.Elgot.mapReturn f k)
                  (Isotope.Elgot.liftPure (Sum.map id
                    (Isotope.LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv (List.ofFn R)))) =
                Isotope.Elgot.kcomp
                  (Isotope.Elgot.liftPure
                    (Isotope.LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv (List.ofFn R))) g := by
            funext current
            set_option maxRecDepth 4096 in
              set_option maxHeartbeats 1000000 in
                simp [f, g, k, Isotope.Elgot.mapReturn, Isotope.Elgot.kcomp,
                Isotope.Elgot.liftPure, Isotope.LambdaIter.Subtyping.Semantics.Categorical.comp_map_of,
                Isotope.LambdaSSA.Semantics.Monadic.labelDenToFinite, Isotope.LambdaSSA.Semantics.Monadic.labelAppendSplit, FC,
                joinM, bind_map_left, bind_assoc, Function.comp_def,
                Isotope.LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv_appendSplit]
            simp only [← bind_pure_comp]
            let input := (Isotope.LambdaSSA.Semantics.Monadic.finiteCategoricalEquiv R).symm
              (Isotope.LambdaSSA.Semantics.Categorical.labelObjToFinite (M (τ := τ)) R
                (Isotope.LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv (List.ofFn R) current))
            have ha := LawfulMonad.bind_assoc
              (collective (ρ, input))
              (fun a => pure (Isotope.LambdaSSA.Semantics.Monadic.LabelValue.appendSplit (List.ofFn R) L a))
              (fun a =>
                Sum.elim
                  (fun b => pure (Sum.inl
                    (Isotope.LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv L b)))
                  (fun x => pure (Sum.inr x)) a >>=
                    pure ∘ Sum.map id
                      (Isotope.LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv (List.ofFn R)))
            change ((collective (ρ, input) >>= fun a =>
                pure (Isotope.LambdaSSA.Semantics.Monadic.LabelValue.appendSplit (List.ofFn R) L a)) >>=
                  fun a => Sum.elim
                    (fun b => pure (Sum.inl
                      (Isotope.LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv L b)))
                    (fun x => pure (Sum.inr x)) a >>=
                      pure ∘ Sum.map id
                        (Isotope.LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv (List.ofFn R))) = _
            rw [ha]
            simp only [LawfulMonad.pure_bind]
            apply bind_congr
            intro a
            cases Isotope.LambdaSSA.Semantics.Monadic.LabelValue.appendSplit (List.ofFn R) L a <;>
              simp [Category.comp_apply]
          have hu := congrFun (LawfulElgotMonad.uniformity
            (Isotope.Elgot.mapReturn f k) g
            (Isotope.LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv (List.ofFn R)) hcomm) loopTarget
          simpa [Isotope.Elgot.liftPure, Isotope.Elgot.kcomp] using hu

noncomputable def RegionCoherent : Prop :=
  letI := Categorical.ofInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  Categorical.RegionTypingCoherent (Φ := Φ) (J (m := m)) (M (τ := τ))

/-- Agreement of the independently chosen proof-relevant monadic and
categorical region denotations, under explicit typing coherence. -/
theorem denoteRegion_agrees
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {Γ : VCtx τ} {region : Region Φ} {L : LCtx τ}
    (h : Region.HasType Γ region L) (ρ : Isotope.LambdaSSA.Semantics.Monadic.Env Γ) :
    letI := Categorical.ofInstructionModel
      (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    (Categorical.denoteRegion (J (m := m)) (M (τ := τ)) h).of
        (envToCategorical ρ) =
      (Monadic.denoteRegion (ε := ε) (m := m) h ρ >>= fun x =>
        pure (Isotope.LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv L x)) := by
  dsimp
  letI := Categorical.ofInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  letI : Categorical.RegionTypingCoherent (Φ := Φ)
      (J (m := m)) (M (τ := τ)) := by
    simpa [RegionCoherent] using coherent
  rcases regionDenotes_toCategorical
      (Monadic.denoteRegion_spec (ε := ε) (m := m) h) with ⟨F, dF, hF⟩
  rw [← Categorical.RegionDenotes.eq_denote (J (m := m)) (M (τ := τ)) dF]
  exact congrFun hF ρ

end Agreement
end Isotope.LambdaSSA.Subtyping.Semantics
