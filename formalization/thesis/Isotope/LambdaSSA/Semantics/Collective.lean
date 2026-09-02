import Isotope.LambdaSSA.Semantics.Finite
import Isotope.LambdaIter.Subtyping.Semantics.Categorical

universe v₁ v₂ u₁ u₂ u₃

namespace Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
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

/-- The internal labels indexed by their arity, before converting through the
list representation used by the surface typing judgment. -/
noncomputable def finiteLabelObj (R : Fin n → τ) : V :=
  ∐ fun i : Fin n => M.obj (R i)

noncomputable def finiteLabelInject (R : Fin n → τ) (i : Fin n) :
    M.obj (R i) ⟶ finiteLabelObj M R :=
  Limits.Sigma.ι (fun j : Fin n => M.obj (R j)) i

/-- Forget that a finite label family was materialized as `List.ofFn`. -/
noncomputable def labelObjToFinite (R : Fin n → τ) :
    labelObj M (List.ofFn R) ⟶ finiteLabelObj M R :=
  Limits.Sigma.desc fun j => by
    let i : Fin n := ⟨j, by simpa using j.isLt⟩
    have h : (List.ofFn R).get j = R i := by simp [i]
    exact eqToHom (congrArg M.obj h) ≫ finiteLabelInject M R i

/-- The coproduct injection indexed directly by the function used to build
the finite label context. -/
noncomputable def finiteInject (R : Fin n → τ) (i : Fin n) :
    M.obj (R i) ⟶ labelObj M (List.ofFn R) := by
  let j : Fin (List.ofFn R).length := ⟨i, by simp⟩
  have h : (List.ofFn R).get j = R i := by simp [j]
  exact eqToHom (congrArg M.obj h.symm) ≫
    Limits.Sigma.ι (fun k : Fin (List.ofFn R).length => M.obj ((List.ofFn R).get k)) j

/-- Materialize a finite-indexed label coproduct in the list representation. -/
noncomputable def finiteLabelToObj (R : Fin n → τ) :
    finiteLabelObj M R ⟶ labelObj M (List.ofFn R) :=
  Limits.Sigma.desc fun i => finiteInject M R i

@[reassoc (attr := simp)] theorem finiteLabelInject_finiteLabelToObj
    (R : Fin n → τ) (i : Fin n) :
    finiteLabelInject M R i ≫ finiteLabelToObj M R = finiteInject M R i := by
  exact Limits.Sigma.ι_desc _ _

structure FiniteCollective (Γ : VCtx τ) {n : Nat} (R : Fin n → τ) (X : V)
    (block : ∀ i, J.obj (ctxObj M (R i :: Γ)) ⟶ J.obj X)
    (f : J.obj (ctxObj M Γ ⊗ finiteLabelObj M R) ⟶ J.obj X) : Prop where
  restrict (i : Fin n) :
    J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteLabelInject M R i) ≫ f = block i

noncomputable def labelOneTo (R : Fin 1 → τ) :
    finiteLabelObj M R ⟶ M.obj (R 0) :=
  Limits.Sigma.desc fun i => eqToHom (congrArg (fun j => M.obj (R j)) (Fin.eq_zero i))

@[reassoc (attr := simp)] theorem labelOneTo_ι (R : Fin 1 → τ) :
    finiteLabelInject M R 0 ≫ labelOneTo M R = 𝟙 _ := by
  unfold finiteLabelInject labelOneTo
  calc
    _ = eqToHom (congrArg (fun j => M.obj (R j)) (Fin.eq_zero (0 : Fin 1))) :=
      Limits.Sigma.ι_desc _ _
    _ = 𝟙 _ := by simp

noncomputable def finiteConsTo (R : Fin (n + 1) → τ) :
    finiteLabelObj M R ⟶ M.obj (R 0) ⨿ finiteLabelObj M (fun i => R i.succ) :=
  Limits.Sigma.desc fun i => Fin.cases coprod.inl
    (fun j => finiteLabelInject M (fun i => R i.succ) j ≫ coprod.inr) i

@[reassoc (attr := simp)] theorem finiteConsTo_head (R : Fin (n + 1) → τ) :
    finiteLabelInject M R 0 ≫ finiteConsTo M R = coprod.inl := by
  exact Limits.Sigma.ι_desc _ _

@[reassoc (attr := simp)] theorem finiteConsTo_tail (R : Fin (n + 1) → τ)
    (i : Fin n) : finiteLabelInject M R i.succ ≫ finiteConsTo M R =
      finiteLabelInject M (fun j => R j.succ) i ≫ coprod.inr := by
  exact Limits.Sigma.ι_desc _ _

theorem finiteHead_distribute (R : Fin (n + 1) → τ) (Γ : VCtx τ) :
    ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteLabelInject M R 0) ≫
        ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteConsTo M R) ≫
        (DistributiveTensor.leftIso (ctxObj M Γ) (M.obj (R 0))
          (finiteLabelObj M (fun i => R i.succ))).inv = coprod.inl := by
  rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
    Category.comp_id, finiteConsTo_head]
  apply (cancel_mono (DistributiveTensor.leftIso (ctxObj M Γ) (M.obj (R 0))
    (finiteLabelObj M (fun i => R i.succ))).hom).1
  simp [DistributiveTensor.leftIso]

theorem finiteTail_distribute (R : Fin (n + 1) → τ) (Γ : VCtx τ) (i : Fin n) :
    ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteLabelInject M R i.succ) ≫
        ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteConsTo M R) ≫
        (DistributiveTensor.leftIso (ctxObj M Γ) (M.obj (R 0))
          (finiteLabelObj M (fun i => R i.succ))).inv =
      ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteLabelInject M (fun j => R j.succ) i) ≫
        coprod.inr := by
  rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
    Category.comp_id, finiteConsTo_tail]
  apply (cancel_mono (DistributiveTensor.leftIso (ctxObj M Γ) (M.obj (R 0))
    (finiteLabelObj M (fun i => R i.succ))).hom).1
  simp [DistributiveTensor.leftIso]

@[reassoc] theorem map_finiteHead_distribute (R : Fin (n + 1) → τ) (Γ : VCtx τ) :
    J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteLabelInject M R 0) ≫
        J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteConsTo M R) ≫
        J.map (DistributiveTensor.leftIso (ctxObj M Γ) (M.obj (R 0))
          (finiteLabelObj M (fun i => R i.succ))).inv = J.map coprod.inl := by
  simpa only [Functor.map_comp] using
    congrArg J.map (finiteHead_distribute M R Γ)

@[reassoc] theorem map_finiteTail_distribute (R : Fin (n + 1) → τ) (Γ : VCtx τ)
    (i : Fin n) :
    J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteLabelInject M R i.succ) ≫
        J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteConsTo M R) ≫
        J.map (DistributiveTensor.leftIso (ctxObj M Γ) (M.obj (R 0))
          (finiteLabelObj M (fun i => R i.succ))).inv =
      J.map (((𝟙 (ctxObj M Γ)) ⊗ₘ
        finiteLabelInject M (fun j => R j.succ) i) ≫ coprod.inr) := by
  simpa only [Functor.map_comp] using
    congrArg J.map (finiteTail_distribute M R Γ i)

theorem finiteCollective_one (Γ : VCtx τ) (R : Fin 1 → τ) (X : V)
    (block : ∀ i, J.obj (ctxObj M (R i :: Γ)) ⟶ J.obj X) :
    FiniteCollective J M Γ R X block
      (J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ labelOneTo M R) ≫ block 0) := by
  constructor
  intro i
  fin_cases i
  rw [← Category.assoc, ← J.map_comp,
    MonoidalCategory.tensorHom_comp_tensorHom]
  simp

theorem finiteCollective_exists_succ (n : Nat) (Γ : VCtx τ)
    (R : Fin (n + 1) → τ) (X : V)
    (block : ∀ i, J.obj (ctxObj M (R i :: Γ)) ⟶ J.obj X) :
    ∃ f, FiniteCollective J M Γ R X block f := by
  induction n with
  | zero => exact ⟨_, finiteCollective_one J M Γ R X block⟩
  | succ n ih =>
      let Rt : Fin (n + 1) → τ := fun i => R i.succ
      rcases ih Rt (fun i => block i.succ) with ⟨ft, dft⟩
      let f := J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteConsTo M R) ≫
        J.map (DistributiveTensor.leftIso (ctxObj M Γ)
          (M.obj (R 0)) (finiteLabelObj M Rt)).inv ≫
        splitMapCoprod J _ _ ≫ coprod.desc (block 0) ft
      refine ⟨f, ?_⟩
      constructor
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [f, Rt]
        rw [map_finiteHead_distribute_assoc]
        simp only [splitMapCoprod]
        rw [map_inl_inv_coprodComparison_assoc]
        rw [coprod.inl_desc]
      · simp only [f, Rt]
        rw [map_finiteTail_distribute_assoc]
        simp only [splitMapCoprod]
        rw [Functor.map_comp, Category.assoc,
          map_inr_inv_coprodComparison_assoc, coprod.inr_desc]
        simpa [Rt] using dft.restrict j

end Isotope.LambdaSSA.Semantics.Categorical
