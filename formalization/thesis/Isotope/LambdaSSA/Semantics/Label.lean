import Isotope.LambdaSSA.Semantics.Model

/-! # Categorical interpretation of lambda-SSA label contexts -/

universe v u₁ u₃

namespace Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Isotope.LambdaIter.Subtyping.Semantics.Categorical

variable {V : Type u₁} [Category.{v} V]
  [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {τ : Type u₃} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]

/-- A label context is interpreted as the finite coproduct of its parameter
types, as in the paper semantics. -/
noncomputable def labelObj (M : TypeModel τ V) (L : LCtx τ) : V :=
  ∐ fun i : Fin L.length => M.obj (L.get i)

/-- The coproduct injection selected by typed label lookup evidence. -/
noncomputable def labelInject (M : TypeModel τ V) {L : LCtx τ}
    (i : Nat) {A : τ} (h : At L i A) : M.obj A ⟶ labelObj M L := by
  have hi : i < L.length := by
    have hh := h
    change L[i]? = some A at hh
    rw [List.getElem?_eq_some_iff] at hh
    exact hh.1
  let j : Fin L.length := ⟨i, hi⟩
  have hj : L.get j = A := by
    have : L[i]? = some (L.get j) := by simp [j]
    rw [h] at this
    exact Option.some.inj this.symm
  subst A
  exact Sigma.ι (fun k : Fin L.length => M.obj (L.get k)) j

end Isotope.LambdaSSA.Semantics.Categorical
