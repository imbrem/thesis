import Isotope.SExp2.Defs

namespace Isotope

universe ua up

namespace Forsp

inductive Word (P : Type up) (A : Type ua) : Type _
| prim (p : P)
| atom (a : A)
| push
| pop
| quote

inductive SWord (P : Type up) (A : Type ua) : Type _
| com (c : Word P A)
| ref (a : A)
| get (a : A)
| set (a : A)

variable {P A}

instance Prim.instCoePrim : Coe P (Word P A) where
  coe := .prim

instance Word.instCoeAtom : Coe A (Word P A) where
  coe := .atom

instance SWord.instCoeWord : Coe (Word P A) (SWord P A) where
  coe := .com

def Prog (P : Type up) (A : Type ua) : Type _ := SExp2 (SWord P A)

universe un uv us

class StackM
  (m : Type uv → Type us)
  (Val : Type uv)
  (State : Type uv)
  where
  pushM : Val → State → m State
  popM : State → m (Val × State)

structure PopEmptyStack where

instance StackM.instList {m Val}
  [Pure m] [MonadExcept PopEmptyStack m]
  : StackM m Val (List Val) where
  pushM v s := pure (v :: s)
  popM
    | [] => throw PopEmptyStack.mk
    | v :: s => pure (v, s)

class EnvM
  (m : Type uv → Type us)
  (Name : Type un) (Val : Type uv)
  (State : Type uv)
  where
  getM : Name → State → m Val
  setM : Name → Val → State → m State

structure EnvNotFound (Name : Type _)

class StoreM
  (m : Type uv → Type us)
  (Name : Type un) (Val : Type uv)
  (State : Type uv)
  extends
  StackM m Val State,
  EnvM m Name Val State

structure Store (Stack : Type uv) (Env : Type uv) where
  stack : Stack
  env : Env

-- instance StoreM.instStore
--   {Val State Env Stack : Type uv}
--   {Name : Type un}
--   [StackM m Val State] [EnvM m Name Val Env]
--   : StoreM m Name Val (Store Stack Env) where
--   pushM := sorry
--   popM := sorry
--   getM := sorry
--   setM := sorry

end Forsp

end Isotope
