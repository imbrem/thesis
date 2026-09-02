import Isotope.LambdaIter.Signature

/-! # Locally nameless lambda-SSA syntax -/

namespace Isotope.LambdaSSA.LocallyNameless

universe u v w

/-- Expressions have named free variables and de Bruijn-indexed local
variables. -/
inductive Tm (ν : Type u) (Φ : Type v) : Nat → Type (max u v) where
  | fv (x : ν) : Tm ν Φ n
  | bv (index : Fin n) : Tm ν Φ n
  | op (f : Φ) (a : Tm ν Φ n) : Tm ν Φ n
  | let₁ (a : Tm ν Φ n) (b : Tm ν Φ (n + 1)) : Tm ν Φ n
  | pair (a b : Tm ν Φ n) : Tm ν Φ n
  | unit : Tm ν Φ n
  | let₂ (a : Tm ν Φ n) (b : Tm ν Φ (n + 1 + 1)) : Tm ν Φ n
  | inl (a : Tm ν Φ n) : Tm ν Φ n
  | inr (a : Tm ν Φ n) : Tm ν Φ n
  | case (e : Tm ν Φ n) (l r : Tm ν Φ (n + 1)) : Tm ν Φ n
  | abort (a : Tm ν Φ n) : Tm ν Φ n
  deriving Repr, DecidableEq

/-- Regions additionally have named free labels and de Bruijn-indexed local
labels.  A CFG simultaneously adds `arity` bound labels; every block adds one
bound value parameter. -/
inductive Region (ν : Type u) (κ : Type v) (Φ : Type w) :
    Nat → Nat → Type (max u v w) where
  | br (label : Fin l ⊕ κ) (arg : Tm ν Φ n) : Region ν κ Φ n l
  | case (discr : Tm ν Φ n)
      (left right : Region ν κ Φ (n + 1) l) : Region ν κ Φ n l
  | let₁ (value : Tm ν Φ n) (body : Region ν κ Φ (n + 1) l) :
      Region ν κ Φ n l
  | let₂ (value : Tm ν Φ n) (body : Region ν κ Φ (n + 1 + 1) l) :
      Region ν κ Φ n l
  | cfg (arity : Nat)
      (entry : Region ν κ Φ n (arity + l))
      (blocks : Fin arity → Region ν κ Φ (n + 1) (arity + l)) :
      Region ν κ Φ n l

end Isotope.LambdaSSA.LocallyNameless
