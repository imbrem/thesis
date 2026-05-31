import Mathlib.Data.List.OfFn

namespace Isotope

universe ua

inductive SExp2 (A : Type ua) : Type ua where
  | cons : SExp2 A → SExp2 A → SExp2 A
  | nil : SExp2 A
  | atom : A → SExp2 A

namespace SExp2

variable {A}

@[simp]
def fromList : List (SExp2 A) → SExp2 A
  | .nil => .nil
  | .cons a as => .cons a (fromList as)

instance instCoeList : Coe (List (SExp2 A)) (SExp2 A) where
  coe := fromList

theorem coe_nil : (([] : List (SExp2 A)) : SExp2 A) = .nil := by simp

theorem coe_cons (a : SExp2 A) (as : List (SExp2 A)) :
  ((a :: as : List (SExp2 A)) : SExp2 A) = .cons a as
  := by simp

instance instEmptyCollection : EmptyCollection (SExp2 A) where
  emptyCollection := .nil

instance instInhabited : Inhabited (SExp2 A) where
  default := .nil

@[simp]
def car : SExp2 A → Option (SExp2 A)
  | .cons a _ => some a
  | .nil => .some .nil
  | .atom _ => none

@[simp]
def cdr : SExp2 A → Option (SExp2 A)
  | .cons _ d => some d
  | .nil => .some .nil
  | .atom _ => none

@[simp]
def car' (e : SExp2 A) : SExp2 A
  := e.car.getD .nil

@[simp]
def cdr' (e : SExp2 A) : SExp2 A
  := e.cdr.getD .nil

end SExp2

end Isotope
