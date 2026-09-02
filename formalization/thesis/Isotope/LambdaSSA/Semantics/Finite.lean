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
  unfold labelConsFrom
  calc
    _ = Limits.Sigma.ι (fun k : Fin L.length => M.obj (L.get k)) i ≫
        Limits.Sigma.desc (fun j => Limits.Sigma.ι
          (fun k : Fin (A::L).length => M.obj ((A::L).get k)) j.succ) := by
      exact congrArg _ (coprod.inr_desc _ _)
    _ = _ := Limits.Sigma.ι_desc _ _

/-- Eliminate the unique summand of a singleton label context. -/
noncomputable def labelSingletonTo (A : τ) : labelObj M [A] ⟶ M.obj A :=
  Limits.Sigma.desc fun i => eqToHom (by fin_cases i; rfl)

@[reassoc (attr := simp)] theorem labelSingletonTo_ι (A : τ) :
    Limits.Sigma.ι (fun i : Fin [A].length => M.obj ([A].get i)) 0 ≫
      labelSingletonTo M A = 𝟙 _ := by
  rw [labelSingletonTo, Limits.Sigma.ι_desc]
  rfl

end Isotope.LambdaSSA.Semantics.Categorical
