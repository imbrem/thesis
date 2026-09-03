import Isotope.LambdaSSA.Semantics.Monadic.Region
import Isotope.LambdaSSA.Semantics.Agreement.Term
import Isotope.LambdaIter.Subtyping.Semantics.Agreement.Iteration

/-! # Agreement of direct and categorical lambda-SSA region semantics -/

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
variable [Iterate m] [LawfulElgotMonad m] [InstructionModel Φ τ ε m]

private abbrev J := Kleisli.Adjunction.toKleisli (CategoryTheory.ofTypeMonad m)
private noncomputable abbrev M := Categorical.ofTypeModel (τ := τ)

private def envFromCategorical : {Γ : VCtx τ} →
    Categorical.ctxObj (M (τ := τ)) Γ → Monadic.Env Γ
  | [], ρ => ρ
  | _ :: _, ρ => (envFromCategorical ρ.1, ρ.2)

@[simp] private theorem envFrom_to {Γ : VCtx τ} (ρ : Monadic.Env Γ) :
    envFromCategorical (envToCategorical ρ) = ρ := by
  induction Γ with
  | nil => rfl
  | cons _ _ ih => simp [envFromCategorical, envToCategorical, ih]

@[simp] private theorem envTo_from {Γ : VCtx τ}
    (ρ : Categorical.ctxObj (M (τ := τ)) Γ) :
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

private theorem envPair_agrees {Γ : VCtx τ} {A B : τ} (ρ : Monadic.Env Γ)
    (ab : TyDen (LambdaIter.tensor A B)) :
    (Categorical.ctxPairIso (M (τ := τ)) Γ A B).hom
      (envToCategorical ρ, ((M (τ := τ)).tensorIso A B).hom ab) =
    let p := TypeModel.tensorEquiv A B ab
    envToCategorical ((ρ, p.1), p.2) := by rfl

private theorem collective_toCategorical {Γ : VCtx τ} {n : Nat}
    {R : Fin n → τ} {L : LCtx τ}
    {fb : ∀ i, Monadic.Env (R i :: Γ) →
      m (Monadic.LabelDen (List.ofFn R ++ L))}
    {collective : Monadic.Env Γ × Monadic.FiniteLabelDen R →
      m (Monadic.LabelDen (List.ofFn R ++ L))}
    (dc : Monadic.CollectiveDenotes Γ R L fb collective)
    {FB : ∀ i, (J (m := m)).obj (Categorical.ctxObj (M (τ := τ)) (R i :: Γ)) ⟶
      (J (m := m)).obj (Categorical.labelObj (M (τ := τ)) (List.ofFn R ++ L))}
    (eFB : ∀ i ρ, (FB i).of (envToCategorical ρ) =
      (fb i ρ >>= fun x =>
        (pure (Monadic.LabelValue.categoricalEquiv (List.ofFn R ++ L) x) :
          m (Categorical.labelObj (M (τ := τ)) (List.ofFn R ++ L))))) :
    Categorical.CollectiveDenotes (J (m := m)) (M (τ := τ)) Γ R L FB
      (Kleisli.Hom.mk (fun p =>
        (show m (Categorical.labelObj (M (τ := τ)) (List.ofFn R ++ L)) from
        collective (envFromCategorical p.1,
            (Monadic.finiteCategoricalEquiv R).symm p.2) >>= fun x =>
          (pure (Monadic.LabelValue.categoricalEquiv (List.ofFn R ++ L) x) :
            m (Categorical.labelObj (M (τ := τ)) (List.ofFn R ++ L)))))) := by
  constructor
  intro i
  ext p
  rcases p with ⟨ρ, a⟩
  rw [Kleisli.Type.comp_of_eq_kcomp]
  simp [Isotope.Elgot.kcomp, envFromCategorical]
  have hfinite : (Monadic.finiteCategoricalEquiv R).symm
      (Categorical.finiteLabelInject (M (τ := τ)) R i a) =
      Monadic.finiteLabelInject R i a := by
    unfold Monadic.finiteCategoricalEquiv Categorical.finiteLabelInject
    apply CofanTypes.equivOfIsColimit_symm_apply
  rw [hfinite]
  rw [dc.restrict]
  simpa [envToCategorical] using (eFB i (envFromCategorical ρ, a)).symm

/-- A direct monadic region witness induces a categorical witness in the
Kleisli/Freyd model with the same result on corresponding environments. -/
theorem regionDenotes_toCategorical {Γ : VCtx τ} {region : Region Φ} {L : LCtx τ}
    {h : Region.HasType Γ region L}
    {f : Monadic.Env Γ → m (Monadic.LabelDen L)}
    (d : Monadic.RegionDenotes (m := m) ε h f) :
    letI := Categorical.ofInstructionModel
      (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    ∃ F, Categorical.RegionDenotes (J (m := m)) (M (τ := τ)) h F ∧
      (fun ρ => F.of (envToCategorical ρ)) =
        (fun ρ => f ρ >>= fun x => pure (Monadic.LabelValue.categoricalEquiv L x)) := by
  dsimp
  letI := Categorical.ofInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  induction d with
  | br dt =>
      rcases denotes_toCategorical dt with ⟨F, dF, eF⟩
      refine ⟨_, Categorical.RegionDenotes.br (h := by assumption) dF, ?_⟩
      funext ρ
      rw [Kleisli.Type.comp_of_eq_kcomp]
      simp [Isotope.Elgot.kcomp, Monadic.labelInject, congrFun eF ρ]
      exact bind_pure_comp _ _
  | case de dl dr ihl ihr =>
      rcases denotes_toCategorical de with ⟨E, dE, eE⟩
      rcases ihl with ⟨FL, dFL, eFL⟩
      rcases ihr with ⟨FR, dFR, eFR⟩
      refine ⟨_, .case dE dFL dFR, ?_⟩
      funext ρ
      rw [Categorical.caseWithContext_of]
      simp [Categorical.comp_map_of, Categorical.ofTypeModel,
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
      rw [Categorical.bind_of]
      simp [Isotope.Elgot.kcomp, congrFun eF ρ]
      apply bind_congr
      intro a
      simpa [envToCategorical, bind_pure_comp] using congrFun eG (ρ, a)
  | let₂ da db ihb =>
      rcases denotes_toCategorical da with ⟨F, dF, eF⟩
      rcases ihb with ⟨G, dG, eG⟩
      refine ⟨_, .let₂ dF dG, ?_⟩
      funext ρ
      simp [Categorical.bind_of, Categorical.comp_map_of, Categorical.ofTypeModel,
        Isotope.Elgot.kcomp, joinM, bind_map_left, congrFun eF ρ]
      apply bind_congr
      intro ab
      rw [envPair_agrees]
      simpa [bind_pure_comp] using congrFun eG _
  | cfgZero he hb de ih =>
      rcases ih with ⟨F, dF, eF⟩
      exact ⟨F, .cfgZero he hb dF, eF⟩
  | cfg he hb de db dc ihe ihb =>
      rcases ihe with ⟨FE, dFE, eFE⟩
      choose FB dFB eFB using ihb
      rename_i n R Γ L entry blocks fe fb collective
      let FC : (J (m := m)).obj (Categorical.ctxObj (M (τ := τ)) Γ ×
          Categorical.finiteLabelObj (M (τ := τ)) R) ⟶
          (J (m := m)).obj (Categorical.labelObj (M (τ := τ))
            (List.ofFn R ++ L)) := Kleisli.Hom.mk (fun
        (p : Categorical.ctxObj (M (τ := τ)) Γ ×
          Categorical.finiteLabelObj (M (τ := τ)) R) =>
        (show m (Categorical.labelObj (M (τ := τ)) (List.ofFn R ++ L)) from
        collective (envFromCategorical p.1,
            (Monadic.finiteCategoricalEquiv R).symm p.2) >>= fun x =>
          (pure (Monadic.LabelValue.categoricalEquiv (List.ofFn R ++ L) x) :
            m (Categorical.labelObj (M (τ := τ)) (List.ofFn R ++ L)))))
      have dFC : Categorical.CollectiveDenotes (J (m := m)) (M (τ := τ))
          Γ R L FB FC := collective_toCategorical dc (fun i ρ => congrFun (eFB i) ρ)
      refine ⟨_, .cfg he hb dFE dFB dFC, ?_⟩
      funext ρ
      rw [Categorical.caseWithContext_of]
      simp [Categorical.comp_map_of, Monadic.labelAppendSplit,
        Isotope.Elgot.kcomp, Isotope.Elgot.liftPure, joinM, bind_map_left,
        bind_pure_comp, congrFun eFE ρ]
      apply bind_congr
      intro target
      rw [Monadic.LabelValue.categoricalEquiv_appendSplit]
      generalize hsM : Monadic.LabelValue.appendSplit (List.ofFn R) L target = destination
      cases destination with
      | inl external =>
          simp [hsM]
      | inr loopTarget =>
          have hinr := congrFun (Types.binaryCoproductIso_inr_comp_hom
            (Categorical.labelObj (M (τ := τ)) L)
            (Categorical.labelObj (M (τ := τ)) (List.ofFn R)))
            (Monadic.LabelValue.categoricalEquiv (List.ofFn R) loopTarget)
          change
            (Types.binaryCoproductIso
              (Categorical.labelObj (M (τ := τ)) L)
              (Categorical.labelObj (M (τ := τ)) (List.ofFn R))).hom
                ((coprod.inr :
                    Categorical.labelObj (M (τ := τ)) (List.ofFn R) ⟶
                      Categorical.labelObj (M (τ := τ)) L ⨿
                        Categorical.labelObj (M (τ := τ)) (List.ofFn R))
                  (Monadic.LabelValue.categoricalEquiv
                    (List.ofFn R) loopTarget)) =
              Sum.inr (Monadic.LabelValue.categoricalEquiv
                (List.ofFn R) loopTarget) at hinr
          simp only
          rw [hinr]
          simp only
          rw [Categorical.contextualLoop_of]
          let f := fun current =>
            Monadic.LabelValue.appendSplit (List.ofFn R) L <$>
              collective (ρ, Monadic.labelDenToFinite R current)
          let g := fun current =>
            Isotope.Elgot.kcomp (m := m)
              (J.map (MonoidalCategoryStruct.whiskerLeft
                    (Categorical.ctxObj (M (τ := τ)) Γ)
                    (Categorical.labelObjToFinite (M (τ := τ)) R)) ≫ FC ≫
                J.map (Categorical.labelAppendSplit
                  (M (τ := τ)) (List.ofFn R) L)).of
              (fun s => pure ((Types.binaryCoproductIso
                (Categorical.labelObj (M (τ := τ)) L)
                (Categorical.labelObj (M (τ := τ)) (List.ofFn R))).hom s))
              (envToCategorical ρ, current)
          let k : Monadic.LabelValue L →
              m (Categorical.labelObj (M (τ := τ)) L) :=
            fun x => pure (Monadic.LabelValue.categoricalEquiv L x)
          change Isotope.Elgot.iter (m := m) g
              (Monadic.LabelValue.categoricalEquiv (List.ofFn R) loopTarget) =
            (Monadic.LabelValue.categoricalEquiv L) <$>
              Isotope.Elgot.iter (m := m) f loopTarget
          rw [show (Monadic.LabelValue.categoricalEquiv L) <$>
                Isotope.Elgot.iter (m := m) f loopTarget =
              Isotope.Elgot.kcomp (Isotope.Elgot.iter (m := m) f) k loopTarget by
            simp [Isotope.Elgot.kcomp, k]]
          rw [LawfulElgotMonad.naturality]
          symm
          have hcomm :
              Isotope.Elgot.kcomp (Isotope.Elgot.mapReturn f k)
                  (Isotope.Elgot.liftPure (Sum.map id
                    (Monadic.LabelValue.categoricalEquiv (List.ofFn R)))) =
                Isotope.Elgot.kcomp
                  (Isotope.Elgot.liftPure
                    (Monadic.LabelValue.categoricalEquiv (List.ofFn R))) g := by
            funext current
            set_option maxRecDepth 4096 in
              set_option maxHeartbeats 1000000 in
                simp [f, g, k, Isotope.Elgot.mapReturn, Isotope.Elgot.kcomp,
                Isotope.Elgot.liftPure, Categorical.comp_map_of,
                Monadic.labelDenToFinite, Monadic.labelAppendSplit, FC,
                joinM, bind_map_left, bind_assoc, Function.comp_def,
                Monadic.LabelValue.categoricalEquiv_appendSplit]
            simp only [← bind_pure_comp]
            let input := (Monadic.finiteCategoricalEquiv R).symm
              (Categorical.labelObjToFinite (M (τ := τ)) R
                (Monadic.LabelValue.categoricalEquiv (List.ofFn R) current))
            have ha := LawfulMonad.bind_assoc
              (collective (ρ, input))
              (fun a => pure (Monadic.LabelValue.appendSplit (List.ofFn R) L a))
              (fun a =>
                Sum.elim
                  (fun b => pure (Sum.inl
                    (Monadic.LabelValue.categoricalEquiv L b)))
                  (fun x => pure (Sum.inr x)) a >>=
                    pure ∘ Sum.map id
                      (Monadic.LabelValue.categoricalEquiv (List.ofFn R)))
            change ((collective (ρ, input) >>= fun a =>
                pure (Monadic.LabelValue.appendSplit (List.ofFn R) L a)) >>=
                  fun a => Sum.elim
                    (fun b => pure (Sum.inl
                      (Monadic.LabelValue.categoricalEquiv L b)))
                    (fun x => pure (Sum.inr x)) a >>=
                      pure ∘ Sum.map id
                        (Monadic.LabelValue.categoricalEquiv (List.ofFn R))) = _
            rw [ha]
            simp only [LawfulMonad.pure_bind]
            apply bind_congr
            intro a
            cases Monadic.LabelValue.appendSplit (List.ofFn R) L a <;>
              simp [Category.comp_apply]
          have hu := congrFun (LawfulElgotMonad.uniformity
            (Isotope.Elgot.mapReturn f k) g
            (Monadic.LabelValue.categoricalEquiv (List.ofFn R)) hcomm) loopTarget
          simpa [Isotope.Elgot.liftPure, Isotope.Elgot.kcomp] using hu

end Agreement
end Isotope.LambdaSSA.Semantics
