import Isotope.TAC.Densem.Syntax

/-! # Executable and relational densem semantics for TAC -/

namespace Isotope.TAC.Densem

universe u v w q

/-- Executable interpretation of primitive values and operations. `abort`
returns no value, and a conditional is defined only when `viewBool` succeeds. -/
structure Model (φ : Type v) where
  Val : Type q
  unit : Val
  pair : Val → Val → Val
  split : Val → Option (Val × Val)
  inl : Val → Val
  inr : Val → Val
  op : φ → Val → Option Val
  viewBool : Val → Option Bool

abbrev Env (M : Model φ) (ν : Type u) := ν → Option M.Val

def Env.set [DecidableEq ν] (ρ : Env M ν) (x : ν) (a : M.Val) : Env M ν :=
  fun y => if y = x then some a else ρ y

def Value.denote (M : Model φ) (ρ : Env M ν) : Value ν → Option M.Val
  | .var x => ρ x
  | .pair a b => return M.pair (← a.denote M ρ) (← b.denote M ρ)
  | .unit => some M.unit

def Operand.denote (M : Model φ) (ρ : Env M ν) : Operand φ ν → Option M.Val
  | .value a => a.denote M ρ
  | .op f a => a.denote M ρ >>= M.op f
  | .inl a => M.inl <$> a.denote M ρ
  | .inr a => M.inr <$> a.denote M ρ
  | .abort _ => none

inductive Exit (κ : Type w) (α : Type q) where
  | branch : κ → Exit κ α
  | return : α → Exit κ α
  deriving DecidableEq

def Terminator.denote (M : Model φ) (ρ : Env M ν) :
    Terminator φ ν κ → Option (Exit κ M.Val)
  | .br ℓ => some (.branch ℓ)
  | .ret a => .return <$> a.denote M ρ
  | .ite c t e => do
      let b ← c.denote M ρ >>= M.viewBool
      if b then t.denote M ρ else e.denote M ρ

def Block.denote [DecidableEq ν] (M : Model φ) (ρ : Env M ν) :
    Block φ ν κ → Option (Env M ν × Exit κ M.Val)
  | .terminator t => (ρ, ·) <$> t.denote M ρ
  | .let₁ x a b => do
      let v ← a.denote M ρ
      b.denote M (ρ.set x v)
  | .let₂ x y a b => do
      let v ← a.denote M ρ
      let (vx, vy) ← M.split v
      b.denote M ((ρ.set x vx).set y vy)

/-- Relational graph of one basic-block execution. -/
def Block.Denotes [DecidableEq ν] (M : Model φ) (ρ : Env M ν)
    (b : Block φ ν κ) (ρ' : Env M ν) (e : Exit κ M.Val) : Prop :=
  b.denote M ρ = some (ρ', e)

/-- Look up a labelled block. Public for syntax-translation simulation lemmas. -/
def CFG.lookup [DecidableEq κ] (g : CFG φ ν κ) (ℓ : κ) :
    Option (Block φ ν κ) := (g.blocks.find? fun p => p.1 = ℓ).map Prod.snd

/-- Continue fuelled execution after a completed block. Public so translations
can state and prove simulation lemmas one transition at a time. -/
def CFG.continueFuel [DecidableEq ν] [DecidableEq κ]
    (M : Model φ) (g : CFG φ ν κ) :
    Nat → Env M ν → Exit κ M.Val → Option M.Val
  | _, _, .return a => some a
  | 0, _, .branch _ => none
  | fuel + 1, ρ, .branch ℓ => do
      let b ← g.lookup ℓ
      let (ρ', exit) ← b.denote M ρ
      continueFuel M g fuel ρ' exit

/-- Fuelled executable graph semantics. Every completed block consumes one
unit of fuel; `none` represents failure, abort, a missing label, or exhaustion. -/
def CFG.runFuel [DecidableEq ν] [DecidableEq κ] (M : Model φ) (g : CFG φ ν κ) :
    Nat → Env M ν → Option M.Val
  | 0, _ => none
  | fuel + 1, ρ => do
      let (ρ', exit) ← g.entry.denote M ρ
      continueFuel M g fuel ρ' exit

/-- Relational graph of the fuelled whole-CFG interpreter. -/
def CFG.Denotes [DecidableEq ν] [DecidableEq κ] (M : Model φ)
    (g : CFG φ ν κ) (fuel : Nat) (ρ : Env M ν) (a : M.Val) : Prop :=
  g.runFuel M fuel ρ = some a

end Isotope.TAC.Densem
