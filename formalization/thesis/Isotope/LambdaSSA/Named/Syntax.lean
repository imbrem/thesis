import Isotope.LambdaIter.Named.Defs

/-! # Named lambda-SSA syntax -/

namespace Isotope.LambdaSSA.Named

universe u v w

abbrev Binder (ν : Type u) := Option ν

/-- Named expressions.  Binder names are retained by the constructs which
scope them; anonymous binders occupy a context slot without introducing a
resolvable name. -/
inductive Tm (ν : Type u) (Φ : Type v) : Type (max u v) where
  | var (x : ν)
  | op (f : Φ) (a : Tm ν Φ)
  | let₁ (x : Binder ν) (a b : Tm ν Φ)
  | pair (a b : Tm ν Φ)
  | unit
  | let₂ (x y : Binder ν) (a b : Tm ν Φ)
  | inl (a : Tm ν Φ)
  | inr (a : Tm ν Φ)
  | case (e : Tm ν Φ) (x : Binder ν) (l : Tm ν Φ)
      (y : Binder ν) (r : Tm ν Φ)
  | abort (a : Tm ν Φ)
  deriving Repr, DecidableEq

/-- Named control-flow regions.  A `cfg` simultaneously binds its label
names in the entry and every block.  Each block additionally binds its value
parameter in its own body. -/
inductive Region (ν : Type u) (κ : Type v) (Φ : Type w) : Type (max u v w) where
  | br (label : κ) (arg : Tm ν Φ)
  | case (discr : Tm ν Φ)
      (x : Binder ν) (left : Region ν κ Φ)
      (y : Binder ν) (right : Region ν κ Φ)
  | let₁ (x : Binder ν) (value : Tm ν Φ) (body : Region ν κ Φ)
  | let₂ (x y : Binder ν) (value : Tm ν Φ) (body : Region ν κ Φ)
  | cfg (entry : Region ν κ Φ) (arity : Nat)
      (labels : Fin arity → Binder κ)
      (params : Fin arity → Binder ν)
      (blocks : Fin arity → Region ν κ Φ)

end Isotope.LambdaSSA.Named
