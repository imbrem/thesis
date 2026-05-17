import Isotope.SExp.Defs
import Isotope.STm.Defs

namespace Isotope

namespace STm

def App (Arity) [instArgs : Args Arity] : Lang Arity where
  Val := Empty
  Op _ := Unit

variable {A}

@[simp]
def toExp : STm (App ℕ) A → SExp A
  | .sym a => .atom a
  | .op _ es => .par (fun i => toExp (es i))

end STm

namespace SExp

open STm

variable {A}

@[simp]
def toTerm : SExp A → STm (App ℕ) A
  | .atom a => .sym a
  | .par es => .op () (fun i => toTerm (es i))

@[simp]
theorem toTerm_toExp (e : SExp A) :
  toExp (toTerm e) = e := by induction e <;> simp [*]

end SExp

namespace STm

open SExp

@[simp]
theorem toExp_toTerm (e : STm (App ℕ) A) :
  toTerm (toExp e) = e := by induction e with
  | sym => rfl
  | const c => cases c
  | op o => cases o; simp [*]

end STm

end Isotope
