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

/-- Tensor in a type universe. -/
def tensor [TypeFormers τ] (A B : τ) : τ := TypeFormers.tensor A B

/-- Unit in a type universe. -/
def unit [TypeFormers τ] : τ := TypeFormers.unit

/-- Coproduct in a type universe. -/
def coprod [TypeFormers τ] (A B : τ) : τ := TypeFormers.coprod A B

/-- Empty type in a type universe. -/
def empty [TypeFormers τ] : τ := TypeFormers.empty

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

@[simp] theorem tensor_ty (A B : Ty α) : tensor A B = Ty.tensor A B := rfl
@[simp] theorem unit_ty : (unit : Ty α) = Ty.unit := rfl
@[simp] theorem coprod_ty (A B : Ty α) : coprod A B = Ty.coprod A B := rfl
@[simp] theorem empty_ty : (empty : Ty α) = Ty.empty := rfl

section Examples

variable {α : Type u}

example (A B : Ty α) : tensor A B = Ty.tensor A B := rfl
example (A B : Ty α) : coprod A B = Ty.coprod A B := rfl
example : (unit : Ty α) = Ty.unit := rfl
example : (empty : Ty α) = Ty.empty := rfl

end Examples

end Isotope.LambdaIter
