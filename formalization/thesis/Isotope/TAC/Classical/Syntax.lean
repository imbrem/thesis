import Mathlib.Data.List.Defs

/-! # Classical three-address code and SSA syntax -/

namespace Isotope.TAC.Classical

universe u v w

/-- Composite operands allowed by the paper's three-address grammar. -/
inductive Value (Var : Type u) where
  | var (x : Var)
  | unit
  | pair (left right : Value Var)
deriving DecidableEq, Repr

/-- Right-hand sides: values and the primitive unary constructors. -/
inductive Operand (Var : Type u) (Op : Type v) where
  | value (v : Value Var)
  | app (f : Op) (arg : Value Var)
  | inl (arg : Value Var)
  | inr (arg : Value Var)
  | abort (arg : Value Var)
deriving DecidableEq, Repr

/-- A three-address definition binds either one result or a destructured pair. -/
inductive Instr (Var : Type u) (Op : Type v) where
  | assign (dst : Var) (rhs : Operand Var Op)
  | assignPair (fst snd : Var) (rhs : Operand Var Op)
deriving DecidableEq, Repr

/-- Nested terminators avoid introducing artificial blocks for conditionals. -/
inductive Terminator (Var : Type u) (Op : Type v) (Label : Type w) where
  | br (target : Label)
  | ret (value : Value Var)
  | cond (scrutinee : Operand Var Op)
      (thenBranch elseBranch : Terminator Var Op Label)
deriving DecidableEq, Repr

/-- One incoming value of a classical phi-node, indexed by its predecessor. -/
structure Incoming (Var : Type u) (Label : Type w) where
  predecessor : Label
  value : Value Var
deriving DecidableEq, Repr

/-- Classical phi-nodes are simultaneous definitions at block entry. -/
structure Phi (Var : Type u) (Label : Type w) where
  dst : Var
  incoming : List (Incoming Var Label)
deriving DecidableEq, Repr

/-- A flat basic block: phis, straight-line definitions, then a terminator. -/
structure Block (Var : Type u) (Op : Type v) (Label : Type w) where
  phis : List (Phi Var Label)
  body : List (Instr Var Op)
  terminator : Terminator Var Op Label
deriving DecidableEq, Repr

/-- A paper-style CFG with a distinguished nameless entry block. -/
structure CFG (Var : Type u) (Op : Type v) (Label : Type w) where
  entry : Block Var Op Label
  blocks : List (Label × Block Var Op Label)
deriving DecidableEq, Repr

inductive BlockId (Label : Type w) where
  | entry
  | named (label : Label)
deriving DecidableEq, Repr

variable {Var : Type u} {Op : Type v} {Label : Type w}

namespace Value

def uses : Value Var → List Var
  | .var x => [x]
  | .unit => []
  | .pair l r => l.uses ++ r.uses

end Value


namespace Operand

def uses : Operand Var Op → List Var
  | .value v | .app _ v | .inl v | .inr v | .abort v => v.uses

end Operand

namespace Instr

def defs : Instr Var Op → List Var
  | .assign x _ => [x]
  | .assignPair x y _ => [x, y]

def uses : Instr Var Op → List Var
  | .assign _ rhs | .assignPair _ _ rhs => rhs.uses

end Instr

namespace Terminator

def uses : Terminator Var Op Label → List Var
  | .br _ => []
  | .ret v => v.uses
  | .cond o l r => o.uses ++ l.uses ++ r.uses

def targets : Terminator Var Op Label → List Label
  | .br target => [target]
  | .ret _ => []
  | .cond _ l r => l.targets ++ r.targets

end Terminator

end Isotope.TAC.Classical
