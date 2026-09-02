import Isotope.TAC.Densem.Denotation
import Isotope.Elgot.Basic

/-! # Direct monadic densem semantics for TAC -/

namespace Isotope.TAC.Densem.Monadic

open Isotope.Elgot

universe u v w

/-- Monadic TAC model. Failure is polymorphic so aborts, unbound variables,
and missing labels can inhabit every result type. -/
structure Model (φ : Type v) (m : Type → Type) where
  Val : Type
  unit : Val
  pair : Val → Val → Val
  split : Val → m (Val × Val)
  inl : Val → Val
  inr : Val → Val
  op : φ → Val → m Val
  viewBool : Val → m Bool
  fail : {α : Type} → m α

abbrev Env (M : Model φ m) (ν : Type u) := ν → Option M.Val

def Env.set [DecidableEq ν] (ρ : Env M ν) (x : ν) (a : M.Val) : Env M ν :=
  fun y => if y = x then some a else ρ y

def Value.denote [Monad m] (M : Model φ m) (ρ : Env M ν) : Value ν → m M.Val
  | .var x => match ρ x with | some a => pure a | none => M.fail
  | .pair a b => do return M.pair (← Value.denote M ρ a) (← Value.denote M ρ b)
  | .unit => pure M.unit

def Operand.denote [Monad m] (M : Model φ m) (ρ : Env M ν) :
    Operand φ ν → m M.Val
  | .value a => Value.denote M ρ a
  | .op f a => Value.denote M ρ a >>= M.op f
  | .inl a => M.inl <$> Value.denote M ρ a
  | .inr a => M.inr <$> Value.denote M ρ a
  | .abort _ => M.fail

def Terminator.denote [Monad m] (M : Model φ m) (ρ : Env M ν) :
    Terminator φ ν κ → m (Exit κ M.Val)
  | .br ℓ => pure (.branch ℓ)
  | .ret a => Exit.return <$> Value.denote M ρ a
  | .ite c t e => do
      let b ← Operand.denote M ρ c >>= M.viewBool
      if b then Terminator.denote M ρ t else Terminator.denote M ρ e

def Block.denote [Monad m] [DecidableEq ν] (M : Model φ m) (ρ : Env M ν) :
    Block φ ν κ → m (Env M ν × Exit κ M.Val)
  | .terminator t => (ρ, ·) <$> Terminator.denote M ρ t
  | .let₁ x a b => do
      let v ← Operand.denote M ρ a
      Block.denote M (ρ.set x v) b
  | .let₂ x y a b => do
      let v ← Operand.denote M ρ a
      let (vx, vy) ← M.split v
      Block.denote M ((ρ.set x vx).set y vy) b

/-- Relational graph of direct monadic block semantics. -/
def Block.Denotes [Monad m] [DecidableEq ν] (M : Model φ m) (ρ : Env M ν)
    (b : Block φ ν κ) (f : m (Env M ν × Exit κ M.Val)) : Prop :=
  Block.denote M ρ b = f

def lookup [DecidableEq κ] (g : CFG φ ν κ) (ℓ : κ) :
    Option (Block φ ν κ) := (g.blocks.find? fun p => p.1 = ℓ).map Prod.snd

/-- One loop iteration: returns a value, or the environment and next label. -/
def CFG.step [Monad m] [DecidableEq ν] [DecidableEq κ]
    (M : Model φ m) (g : CFG φ ν κ) :
    Env M ν × κ → m (M.Val ⊕ (Env M ν × κ))
  | (ρ, ℓ) => match lookup g ℓ with
      | none => M.fail
      | some b => do
          let (ρ', exit) ← Block.denote M ρ b
          match exit with
          | Exit.return a => pure (.inl a)
          | .branch k => pure (.inr (ρ', k))

/-- Whole-CFG semantics. The entry block runs once; subsequent branches are
interpreted by complete-Elgot iteration. -/
def CFG.denote [Monad m] [Iterate m] [DecidableEq ν] [DecidableEq κ]
    (M : Model φ m) (g : CFG φ ν κ) (ρ : Env M ν) : m M.Val := do
  let (ρ', exit) ← Block.denote M ρ g.entry
  match exit with
  | Exit.return a => pure a
  | .branch ℓ => Elgot.iter (CFG.step M g) (ρ', ℓ)

/-- Relational graph of the iteration-based whole-CFG semantics. -/
def CFG.Denotes [Monad m] [Iterate m] [DecidableEq ν] [DecidableEq κ]
    (M : Model φ m) (g : CFG φ ν κ) (ρ : Env M ν) (f : m M.Val) : Prop :=
  CFG.denote M g ρ = f

end Isotope.TAC.Densem.Monadic
