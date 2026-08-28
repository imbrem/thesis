import Mathlib

/-!
# Types for lambda-iter

This file isolates the type-forming operations needed by the syntax and its
typing judgments. A development may either supply its own type universe or
use `Ty`, the freely generated simple types over a collection of base types.
-/

namespace Isotope.LambdaIter

/-- A type universe with the four type formers used by lambda-iter. -/
class TypeFormers (τ : Type u) where
  /-- Tensor (product) of types. -/
  tensor : τ → τ → τ
  /-- The tensor unit. -/
  unit : τ
  /-- Coproduct (sum) of types. -/
  coprod : τ → τ → τ
  /-- The empty type. -/
  empty : τ

/-- Simple types freely generated from the base types `α`. -/
inductive Ty (α : Type u) : Type u where
  | base (a : α)
  | tensor (A B : Ty α)
  | unit
  | coprod (A B : Ty α)
  | empty
  deriving Repr, DecidableEq

instance : TypeFormers (Ty α) where
  tensor := Ty.tensor
  unit := Ty.unit
  coprod := Ty.coprod
  empty := Ty.empty

section Examples

variable {α : Type u}

example (A B : Ty α) : TypeFormers.tensor A B = Ty.tensor A B := rfl
example (A B : Ty α) : TypeFormers.coprod A B = Ty.coprod A B := rfl
example : (TypeFormers.unit : Ty α) = Ty.unit := rfl
example : (TypeFormers.empty : Ty α) = Ty.empty := rfl

end Examples

end Isotope.LambdaIter
