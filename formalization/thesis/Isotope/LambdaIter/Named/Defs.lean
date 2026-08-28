import Isotope.LambdaIter.Ty

/-! # Named syntax for lambda-iter -/

namespace Isotope.LambdaIter.Named

universe u v w

/-- A typed instruction signature. `pure` records the side condition used by
the effect-sensitive equations, without baking an effect system into syntax. -/
structure Signature (τ : Type u) where
  Op : Type v
  src : Op → τ
  trg : Op → τ
  pure : Op → Prop := fun _ => False

/-- `none` binders deliberately retain a context position, but cannot be
referenced and shadow no name. -/
abbrev Binder (ι : Type u) := Option ι

inductive Tm (ι : Type w) {τ : Type u} (S : Signature.{u, v} τ) : Type (max w v) where
  | var (x : ι)
  | op (f : S.Op) (a : Tm ι S)
  | let₁ (x : Binder ι) (a b : Tm ι S)
  | unit
  | pair (a b : Tm ι S)
  | let₂ (x y : Binder ι) (a b : Tm ι S)
  | inl (a : Tm ι S)
  | inr (a : Tm ι S)
  | case (e : Tm ι S) (x : Binder ι) (a : Tm ι S)
      (y : Binder ι) (b : Tm ι S)
  | abort (a : Tm ι S)
  | iter (a : Tm ι S) (x : Binder ι) (b : Tm ι S)

end Isotope.LambdaIter.Named
