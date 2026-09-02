import Isotope.LambdaSSA.Semantics.Label
universe v u₁ u₃
namespace Isotope.LambdaSSA.Semantics.Categorical
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open Isotope.LambdaIter.Subtyping.Semantics.Categorical
variable {V : Type u₁} [Category.{v} V] [CartesianMonoidalCategory V]
  [HasFiniteCoproducts V] {τ : Type u₃} [LambdaIter.TypeFormers τ]
  [LambdaIter.Subtyping τ] (M : TypeModel τ V)

noncomputable def labelConsTo (A : τ) (L : LCtx τ) :
    labelObj M (A :: L) ⟶ M.obj A ⨿ labelObj M L :=
  Limits.Sigma.desc fun i => Fin.cases coprod.inl
    (fun j => Limits.Sigma.ι (fun k : Fin L.length => M.obj (L.get k)) j ≫ coprod.inr) i

noncomputable def labelConsFrom (A : τ) (L : LCtx τ) :
    M.obj A ⨿ labelObj M L ⟶ labelObj M (A :: L) :=
  coprod.desc (Limits.Sigma.ι (fun k : Fin (A::L).length => M.obj ((A::L).get k)) 0)
    (Limits.Sigma.desc fun j => Limits.Sigma.ι
      (fun k : Fin (A::L).length => M.obj ((A::L).get k)) j.succ)

@[reassoc (attr := simp)] theorem labelConsTo_head (A : τ) (L : LCtx τ) :
    Limits.Sigma.ι (fun k : Fin (A::L).length => M.obj ((A::L).get k)) 0 ≫
      labelConsTo M A L = coprod.inl := by
  rw [labelConsTo, Limits.Sigma.ι_desc]
  rfl

@[reassoc (attr := simp)] theorem labelConsTo_tail (A : τ) (L : LCtx τ)
    (i : Fin L.length) :
    Limits.Sigma.ι (fun k : Fin (A::L).length => M.obj ((A::L).get k)) i.succ ≫
      labelConsTo M A L = Limits.Sigma.ι
        (fun k : Fin L.length => M.obj (L.get k)) i ≫ coprod.inr := by
  rw [labelConsTo, Limits.Sigma.ι_desc]
  rfl

@[reassoc (attr := simp)] theorem labelConsFrom_head (A : τ) (L : LCtx τ) :
    coprod.inl ≫ labelConsFrom M A L =
      Limits.Sigma.ι (fun k : Fin (A::L).length => M.obj ((A::L).get k)) 0 := by
  simp only [labelConsFrom, coprod.inl_desc]

@[reassoc (attr := simp)] theorem labelConsFrom_tail (A : τ) (L : LCtx τ) (i : Fin L.length) :
    Limits.Sigma.ι (fun k : Fin L.length => M.obj (L.get k)) i ≫ coprod.inr ≫
      labelConsFrom M A L = Limits.Sigma.ι
        (fun k : Fin (A::L).length => M.obj ((A::L).get k)) i.succ := by
  simp only [labelConsFrom, Category.assoc, coprod.inr_desc, Limits.Sigma.ι_desc]

noncomputable def labelConsIso (A : τ) (L : LCtx τ) :
    labelObj M (A :: L) ≅ M.obj A ⨿ labelObj M L where
  hom := labelConsTo M A L
  inv := labelConsFrom M A L
  hom_inv_id := by
    apply Limits.Sigma.hom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Category.assoc, labelConsTo_head_assoc, labelConsFrom_head, comp_id]
    · simp only [Category.assoc, labelConsTo_tail_assoc, labelConsFrom_tail, comp_id]
  inv_hom_id := by
    apply coprod.hom_ext
    · simp only [Category.assoc, labelConsFrom_head_assoc, labelConsTo_head, comp_id]
    · apply Limits.Sigma.hom_ext
      intro i
      simp only [Category.assoc, labelConsFrom_tail_assoc, labelConsTo_tail, comp_id]

end Isotope.LambdaSSA.Semantics.Categorical
