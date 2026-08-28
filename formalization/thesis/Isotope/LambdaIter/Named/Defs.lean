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
abbrev Binder (ν : Type u) := Option ν

inductive Tm (ν : Type w) {τ : Type u} (S : Signature.{u, v} τ) : Type (max w v) where
  | var (x : ν)
  | op (f : S.Op) (a : Tm ν S)
  | let₁ (x : Binder ν) (a b : Tm ν S)
  | unit
  | pair (a b : Tm ν S)
  | let₂ (x y : Binder ν) (a b : Tm ν S)
  | inl (a : Tm ν S)
  | inr (a : Tm ν S)
  | case (e : Tm ν S) (x : Binder ν) (a : Tm ν S)
      (y : Binder ν) (b : Tm ν S)
  | abort (a : Tm ν S)
  | iter (a : Tm ν S) (x : Binder ν) (b : Tm ν S)

end Isotope.LambdaIter.Named
