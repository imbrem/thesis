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

/-- The coproduct injection indexed directly by the function used to build
the finite label context. -/
noncomputable def finiteInject (R : Fin n → τ) (i : Fin n) :
    M.obj (R i) ⟶ labelObj M (List.ofFn R) := by
  let j : Fin (List.ofFn R).length := ⟨i, by simp⟩
  have h : (List.ofFn R).get j = R i := by simp [j]
  exact eqToHom (congrArg M.obj h.symm) ≫
    Limits.Sigma.ι (fun k : Fin (List.ofFn R).length => M.obj ((List.ofFn R).get k)) j

structure FiniteCollective (Γ : VCtx τ) {n : Nat} (R : Fin n → τ) (X : V)
    (block : ∀ i, J.obj (ctxObj M (R i :: Γ)) ⟶ J.obj X)
    (f : J.obj (ctxObj M Γ ⊗ labelObj M (List.ofFn R)) ⟶ J.obj X) : Prop where
  restrict (i : Fin n) :
    J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteInject M R i) ≫ f = block i

noncomputable def labelOneTo (R : Fin 1 → τ) :
    labelObj M (List.ofFn R) ⟶ M.obj (R 0) :=
  Limits.Sigma.desc fun i => eqToHom (by fin_cases i; rfl)

@[reassoc (attr := simp)] theorem labelOneTo_ι (R : Fin 1 → τ) :
    finiteInject M R 0 ≫ labelOneTo M R = 𝟙 _ := by
  let j : Fin (List.ofFn R).length := ⟨0, by simp⟩
  let p := fun i : Fin (List.ofFn R).length =>
    (eqToHom (by fin_cases i; rfl) : M.obj ((List.ofFn R).get i) ⟶ M.obj (R 0))
  have hs : Limits.Sigma.ι
      (fun k : Fin (List.ofFn R).length => M.obj ((List.ofFn R).get k)) j ≫
      Limits.Sigma.desc p = p j := Limits.Sigma.ι_desc p j
  unfold finiteInject labelOneTo
  change (eqToHom _ ≫ Limits.Sigma.ι _ j) ≫ Limits.Sigma.desc p = 𝟙 _
  calc
    _ = eqToHom _ ≫ (Limits.Sigma.ι _ j ≫ Limits.Sigma.desc p) :=
      Category.assoc _ _ _
    _ = eqToHom _ ≫ p j := congrArg _ hs
    _ = 𝟙 _ := by simp [p, j]

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

end Isotope.LambdaSSA.Semantics.Categorical
