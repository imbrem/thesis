import Mathlib.Data.Nat.Basic

universe un uo

inductive SExp (O : Type uo) (N : Type un) where
  | var : N → SExp O N
  | op : O → {arity : ℕ} → (Fin arity → SExp O N) → SExp O N

namespace SExp

def mapOp {O O' N} (f : O → O') : SExp O N → SExp O' N
  | .var n => .var n
  | .op o es => .op (f o) (fun i => mapOp f (es i))

def mapVar {O N N'} (f : N → N') : SExp O N → SExp O N'
  | .var n => .var (f n)
  | .op o es => .op o (fun i => mapVar f (es i))

@[simp]
def bindOp {O O' N}
  (interpOp : O → {arity : ℕ} -> (Fin arity -> SExp O' N) -> SExp O' N)
  : SExp O N → SExp O' N
  | .var n => .var n
  | .op o es => interpOp o (fun i => bindOp interpOp (es i))

@[simp]
theorem bindOp_pure {O N} (e : SExp O N) :
  bindOp .op e = e := by induction e <;> simp [*]

@[simp]
def bindVar {O N N'}
  (interpVar : N → SExp O N')
  : SExp O N → SExp O N'
  | .var n => interpVar n
  | .op o es => .op o (fun i => bindVar interpVar (es i))

@[simp]
theorem bindVar_pure {O N} (e : SExp O N) :
  bindVar .var e = e := by induction e <;> simp [*]

end SExp

inductive SExpL.Kind where
  | sexp
  | list

inductive SExpL (O : Type uo) (N : Type un) : SExpL.Kind -> Type _ where
  | var : N -> SExpL O N .sexp
  | op : O -> SExpL O N .list -> SExpL O N .sexp
  | nil : SExpL O N .list
  | cons : SExpL O N .sexp -> SExpL O N .list -> SExpL O N .list

namespace SExpL

def Kind.toSExp (O : Type uo) (N : Type un)
  : Kind -> Type _
  | .sexp => SExp O N
  | .list => List (SExp O N)

@[simp]
def toList {O N} : SExpL O N .list -> List (SExpL O N .sexp)
  | .nil => []
  | .cons e es => e :: toList es

@[simp]
def toSExp {O N k} : SExpL O N k -> k.toSExp O N
  | .var n => .var n
  | .op o es => .op o (es.toSExp.get)
  | .nil => []
  | .cons e es => toSExp e :: toSExp es

end SExpL
