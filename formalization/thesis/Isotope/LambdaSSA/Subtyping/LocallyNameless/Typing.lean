import Isotope.LambdaSSA.LocallyNameless.Context
import Isotope.LambdaIter.Subtyping

namespace Isotope.LambdaSSA.Subtyping.LocallyNameless

open Isotope.LambdaSSA.LocallyNameless

universe u v w q

variable {τ : Type u} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
variable {ν : Type v} [DecidableEq ν]
variable {κ : Type w} [DecidableEq κ]

inductive Tm.HasType (Φ : Type q) [LambdaIter.HasTy Φ τ]
    (Γ : FreeCtx ν τ) : {n : Nat} → BoundCtx τ n → Tm ν Φ n → τ → Type (max q u v) where
  | fv : LambdaIter.Ctx.lookup Γ x = some A → HasType Φ Γ β (.fv x) A
  | bv : HasType Φ Γ β (.bv i) (β.get i)
  | op : HasType Φ Γ β a (LambdaIter.instrSrc f) →
      HasType Φ Γ β (.op f a) (LambdaIter.instrTrg f)
  | let₁ : HasType Φ Γ β a A → HasType Φ Γ (.snoc β A) b B →
      HasType Φ Γ β (.let₁ a b) B
  | pair : HasType Φ Γ β a A → HasType Φ Γ β b B →
      HasType Φ Γ β (.pair a b) (LambdaIter.tensor A B)
  | unit : HasType Φ Γ β .unit LambdaIter.unit
  | let₂ : HasType Φ Γ β a (LambdaIter.tensor A B) →
      HasType Φ Γ (.snoc (.snoc β A) B) b C → HasType Φ Γ β (.let₂ a b) C
  | inl : HasType Φ Γ β a A → HasType Φ Γ β (.inl a) (LambdaIter.coprod A B)
  | inr : HasType Φ Γ β b B → HasType Φ Γ β (.inr b) (LambdaIter.coprod A B)
  | case : HasType Φ Γ β e (LambdaIter.coprod A B) →
      HasType Φ Γ (.snoc β A) l C → HasType Φ Γ (.snoc β B) r C →
      HasType Φ Γ β (.case e l r) C
  | abort : HasType Φ Γ β a LambdaIter.empty → HasType Φ Γ β (.abort a) A
  | sub : HasType Φ Γ β a A → LambdaIter.Subty A B → HasType Φ Γ β a B

inductive Region.HasType (Φ : Type q) [LambdaIter.HasTy Φ τ]
    (Γ : FreeCtx ν τ) (K : FreeCtx κ τ) :
    {n l : Nat} → BoundCtx τ n → BoundCtx τ l → Region ν κ Φ n l →
      Type (max q u v w) where
  | br_free {label : κ} {arg : Tm ν Φ n} :
      LambdaIter.Ctx.lookup K label = some A → Tm.HasType Φ Γ β arg A →
      HasType Φ Γ K β δ (.br (.inr label) arg)
  | br_bound {label : Fin l} {arg : Tm ν Φ n} :
      Tm.HasType Φ Γ β arg (δ.get label) →
      HasType Φ Γ K β δ (.br (.inl label) arg)
  | case {discr : Tm ν Φ n}
      {left right : Region ν κ Φ (n + 1) l} :
      Tm.HasType Φ Γ β discr (LambdaIter.coprod A B) →
      HasType Φ Γ K (.snoc β A) δ left →
      HasType Φ Γ K (.snoc β B) δ right →
      HasType Φ Γ K β δ (.case discr left right)
  | let₁ {value : Tm ν Φ n} {body : Region ν κ Φ (n + 1) l} :
      Tm.HasType Φ Γ β value A →
      HasType Φ Γ K (.snoc β A) δ body →
      HasType Φ Γ K β δ (.let₁ value body)
  | let₂ {value : Tm ν Φ n} {body : Region ν κ Φ (n + 1 + 1) l} :
      Tm.HasType Φ Γ β value (LambdaIter.tensor A B) →
      HasType Φ Γ K (.snoc (.snoc β A) B) δ body →
      HasType Φ Γ K β δ (.let₂ value body)
  | cfg {arity : Nat} {entry : Region ν κ Φ n (arity + l)}
      {blocks : Fin arity → Region ν κ Φ (n + 1) (arity + l)}
      (R : Fin arity → τ) :
      HasType Φ Γ K β (extendLabelCtx δ R) entry →
      (∀ i, HasType Φ Γ K (.snoc β (R i)) (extendLabelCtx δ R) (blocks i)) →
      HasType Φ Γ K β δ (.cfg arity entry blocks)

end Isotope.LambdaSSA.Subtyping.LocallyNameless
