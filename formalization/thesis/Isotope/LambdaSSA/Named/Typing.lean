import Isotope.LambdaSSA.Named.Context

namespace Isotope.LambdaSSA.Named

variable [LambdaIter.TypeFormers τ] [LambdaIter.HasTy Φ τ]
variable [DecidableEq ν] [DecidableEq κ]

inductive Tm.HasType : VCtx ν τ → Tm ν Φ → τ → Prop where
  | var : LambdaIter.Ctx.lookup Γ x = some A → HasType Γ (.var x) A
  | op : HasType Γ a (LambdaIter.instrSrc f) →
      HasType Γ (.op f a) (LambdaIter.instrTrg f)
  | let₁ : HasType Γ a A → HasType (Γ.snoc x A) b B →
      HasType Γ (.let₁ x a b) B
  | pair : HasType Γ a A → HasType Γ b B →
      HasType Γ (.pair a b) (LambdaIter.tensor A B)
  | unit : HasType Γ .unit LambdaIter.unit
  | let₂ : HasType Γ a (LambdaIter.tensor A B) →
      HasType ((Γ.snoc x A).snoc y B) b C → HasType Γ (.let₂ x y a b) C
  | inl : HasType Γ a A → HasType Γ (.inl a) (LambdaIter.coprod A B)
  | inr : HasType Γ b B → HasType Γ (.inr b) (LambdaIter.coprod A B)
  | case : HasType Γ e (LambdaIter.coprod A B) →
      HasType (Γ.snoc x A) l C → HasType (Γ.snoc y B) r C →
      HasType Γ (.case e x l y r) C
  | abort : HasType Γ a LambdaIter.empty → HasType Γ (.abort a) A

inductive Region.HasType : VCtx ν τ → Region ν κ Φ → LCtx κ τ → Prop where
  | br {label : κ} {arg : Tm ν Φ} :
      LambdaIter.Ctx.lookup L label = some A → Tm.HasType Γ arg A →
      HasType Γ (.br label arg) L
  | case {discr : Tm ν Φ} {left right : Region ν κ Φ} :
      Tm.HasType Γ discr (LambdaIter.coprod A B) →
      HasType (Γ.snoc x A) left L → HasType (Γ.snoc y B) right L →
      HasType Γ (.case discr x left y right) L
  | let₁ {value : Tm ν Φ} {body : Region ν κ Φ} :
      Tm.HasType Γ value A → HasType (Γ.snoc x A) body L →
      HasType Γ (.let₁ x value body) L
  | let₂ {value : Tm ν Φ} {body : Region ν κ Φ} :
      Tm.HasType Γ value (LambdaIter.tensor A B) →
      HasType ((Γ.snoc x A).snoc y B) body L →
      HasType Γ (.let₂ x y value body) L
  | cfg {entry : Region ν κ Φ} {n : Nat}
      {labels : Fin n → Binder κ} {params : Fin n → Binder ν}
      {blocks : Fin n → Region ν κ Φ} (R : Fin n → τ) :
      HasType Γ entry (extendLabels L n labels R) →
      (∀ i, HasType (Γ.snoc (params i) (R i)) (blocks i)
        (extendLabels L n labels R)) →
      HasType Γ (.cfg entry n labels params blocks) L

end Isotope.LambdaSSA.Named
