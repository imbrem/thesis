/-! # Three-address-code syntax used by the densem development -/

namespace Isotope.TAC.Densem

universe u v w

/-- TAC values contain variables and only nullary/binary tuples. -/
inductive Value (ν : Type u) where
  | var : ν → Value ν
  | pair : Value ν → Value ν → Value ν
  | unit : Value ν
  deriving DecidableEq

/-- Right-hand sides. Primitive operations take one (possibly tuple-valued)
argument, matching the unary instruction presentation in `freyd-ssa`. -/
inductive Operand (φ : Type v) (ν : Type u) where
  | value : Value ν → Operand φ ν
  | op : φ → Value ν → Operand φ ν
  | inl : Value ν → Operand φ ν
  | inr : Value ν → Operand φ ν
  | abort : Value ν → Operand φ ν
  deriving DecidableEq

/-- Nested TAC terminators. -/
inductive Terminator (φ : Type v) (ν : Type u) (κ : Type w) where
  | br : κ → Terminator φ ν κ
  | ret : Value ν → Terminator φ ν κ
  | ite : Operand φ ν → Terminator φ ν κ → Terminator φ ν κ →
      Terminator φ ν κ
  deriving DecidableEq

/-- A basic block is a straight-line sequence ending in a terminator. -/
inductive Block (φ : Type v) (ν : Type u) (κ : Type w) where
  | terminator : Terminator φ ν κ → Block φ ν κ
  | let₁ : ν → Operand φ ν → Block φ ν κ → Block φ ν κ
  | let₂ : ν → ν → Operand φ ν → Block φ ν κ → Block φ ν κ
  deriving DecidableEq

/-- A TAC control-flow graph has a distinguished nameless entry block and a
finite association list of labelled blocks. -/
structure CFG (φ : Type v) (ν : Type u) (κ : Type w) where
  entry : Block φ ν κ
  blocks : List (κ × Block φ ν κ)
  deriving DecidableEq

end Isotope.TAC.Densem
