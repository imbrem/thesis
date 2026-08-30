import Isotope.LambdaIter.Signature

/-! # Named syntax for lambda-iter -/

namespace Isotope.LambdaIter.Named

universe u v

/-- `none` binders deliberately retain a context position, but cannot be
referenced and shadow no name. -/
abbrev Binder (ν : Type u) := Option ν

/-- Raw named terms depend only on names and primitive operators. Instruction
typing and effects are supplied independently to later judgments. -/
inductive Tm (ν : Type u) (Φ : Type v) : Type (max u v) where
  | var (x : ν)
  | op (f : Φ) (a : Tm ν Φ)
  | let₁ (x : Binder ν) (a b : Tm ν Φ)
  | unit
  | pair (a b : Tm ν Φ)
  | let₂ (x y : Binder ν) (a b : Tm ν Φ)
  | inl (a : Tm ν Φ)
  | inr (a : Tm ν Φ)
  | case (e : Tm ν Φ) (x : Binder ν) (a : Tm ν Φ)
      (y : Binder ν) (b : Tm ν Φ)
  | abort (a : Tm ν Φ)
  | iter (a : Tm ν Φ) (x : Binder ν) (b : Tm ν Φ)

end Isotope.LambdaIter.Named
