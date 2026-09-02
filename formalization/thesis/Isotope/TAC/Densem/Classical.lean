import Isotope.TAC.Classical.Syntax
import Isotope.TAC.Densem.Denotation

/-! # Bridge from phi-free classical TAC to densem TAC -/

namespace Isotope.TAC.Densem.Classical

universe u v w q

namespace C
abbrev Value := Isotope.TAC.Classical.Value
abbrev Operand := Isotope.TAC.Classical.Operand
abbrev Instr := Isotope.TAC.Classical.Instr
abbrev Terminator := Isotope.TAC.Classical.Terminator
abbrev Block := Isotope.TAC.Classical.Block
abbrev CFG := Isotope.TAC.Classical.CFG
end C

def value : C.Value ν → Densem.Value ν
  | .var x => .var x
  | .unit => .unit
  | .pair a b => .pair (value a) (value b)

def operand : C.Operand ν φ → Densem.Operand φ ν
  | .value a => .value (value a)
  | .app f a => .op f (value a)
  | .inl a => .inl (value a)
  | .inr a => .inr (value a)
  | .abort a => .abort (value a)

def terminator : C.Terminator ν φ κ → Densem.Terminator φ ν κ
  | .br ℓ => .br ℓ
  | .ret a => .ret (value a)
  | .cond c t e => .ite (operand c) (terminator t) (terminator e)

def instructions : List (C.Instr ν φ) → Densem.Terminator φ ν κ →
    Densem.Block φ ν κ
  | [], t => .terminator t
  | .assign x a :: is, t => .let₁ x (operand a) (instructions is t)
  | .assignPair x y a :: is, t => .let₂ x y (operand a) (instructions is t)

def block (b : C.Block ν φ κ) : Densem.Block φ ν κ :=
  instructions b.body (terminator b.terminator)

/-- The precise fragment on which the classical and densem CFG syntaxes
coincide: no entry or labelled block contains a phi-node. -/
structure PhiFree (g : C.CFG ν φ κ) : Prop where
  entry : g.entry.phis = []
  blocks : ∀ p ∈ g.blocks, p.2.phis = []

def cfg (g : C.CFG ν φ κ) (_ : PhiFree g) : Densem.CFG φ ν κ where
  entry := block g.entry
  blocks := g.blocks.map fun p => (p.1, block p.2)

def ofValue : Densem.Value ν → C.Value ν
  | .var x => .var x
  | .unit => .unit
  | .pair a b => .pair (ofValue a) (ofValue b)

def ofOperand : Densem.Operand φ ν → C.Operand ν φ
  | .value a => .value (ofValue a)
  | .op f a => .app f (ofValue a)
  | .inl a => .inl (ofValue a)
  | .inr a => .inr (ofValue a)
  | .abort a => .abort (ofValue a)

@[simp] theorem ofValue_value (a : C.Value ν) : ofValue (value a) = a := by
  induction a <;> simp [value, ofValue, *]

@[simp] theorem ofOperand_operand (a : C.Operand ν φ) : ofOperand (operand a) = a := by
  cases a <;> simp [operand, ofOperand]

namespace Executable

abbrev Env (M : Densem.Model φ) (ν : Type u) := Densem.Env M ν

def valueDenote (M : Densem.Model φ) (ρ : Env M ν) (a : C.Value ν) : Option M.Val :=
  match a with
  | .var x => ρ x
  | .unit => some M.unit
  | .pair l r => return M.pair (← valueDenote M ρ l) (← valueDenote M ρ r)

def operandDenote (M : Densem.Model φ) (ρ : Env M ν) (a : C.Operand ν φ) :
    Option M.Val :=
  match a with
  | .value v => valueDenote M ρ v
  | .app f v => valueDenote M ρ v >>= M.op f
  | .inl v => M.inl <$> valueDenote M ρ v
  | .inr v => M.inr <$> valueDenote M ρ v
  | .abort _ => none

def terminatorDenote (M : Densem.Model φ) (ρ : Env M ν)
    (t : C.Terminator ν φ κ) : Option (Densem.Exit κ M.Val) :=
  match t with
  | .br ℓ => some (.branch ℓ)
  | .ret v => .return <$> valueDenote M ρ v
  | .cond c t e => do
      let b ← operandDenote M ρ c >>= M.viewBool
      if b then terminatorDenote M ρ t else terminatorDenote M ρ e

def bodyDenote [DecidableEq ν] (M : Densem.Model φ) :
    List (C.Instr ν φ) → Env M ν → C.Terminator ν φ κ →
      Option (Env M ν × Densem.Exit κ M.Val)
  | [], ρ, t => (ρ, ·) <$> terminatorDenote M ρ t
  | .assign x a :: is, ρ, t => do
      let v ← operandDenote M ρ a
      bodyDenote M is (Densem.Env.set ρ x v) t
  | .assignPair x y a :: is, ρ, t => do
      let v ← operandDenote M ρ a
      let (vx, vy) ← M.split v
      bodyDenote M is ((Densem.Env.set ρ x vx).set y vy) t

def blockDenote [DecidableEq ν] (M : Densem.Model φ) (ρ : Env M ν)
    (b : C.Block ν φ κ) : Option (Env M ν × Densem.Exit κ M.Val) :=
  bodyDenote M b.body ρ b.terminator

theorem value_commute (M : Densem.Model φ) (ρ : Env M ν) (a : C.Value ν) :
    Densem.Value.denote M ρ (value a) = valueDenote M ρ a := by
  induction a <;> simp [value, Densem.Value.denote, valueDenote, *]

theorem operand_commute (M : Densem.Model φ) (ρ : Env M ν) (a : C.Operand ν φ) :
    Densem.Operand.denote M ρ (operand a) = operandDenote M ρ a := by
  cases a <;> simp [operand, Densem.Operand.denote, operandDenote, value_commute]

theorem terminator_commute (M : Densem.Model φ) (ρ : Env M ν)
    (t : C.Terminator ν φ κ) :
    Densem.Terminator.denote M ρ (terminator t) = terminatorDenote M ρ t := by
  induction t <;> simp [terminator, Densem.Terminator.denote, terminatorDenote,
    operand_commute, value_commute, *]

theorem block_commute [DecidableEq ν] (M : Densem.Model φ) (ρ : Env M ν)
    (b : C.Block ν φ κ) :
    Densem.Block.denote M ρ (block b) = blockDenote M ρ b := by
  unfold block blockDenote
  induction b.body generalizing ρ with
  | nil => simp [instructions, bodyDenote, Densem.Block.denote, terminator_commute]
  | cons i is ih =>
      cases i <;> simp [instructions, bodyDenote, Densem.Block.denote,
        operand_commute, ih]

def lookup [DecidableEq κ] (g : C.CFG ν φ κ) (ℓ : κ) :
    Option (C.Block ν φ κ) :=
  (g.blocks.find? fun p => p.1 = ℓ).map Prod.snd

private theorem lookup_map [DecidableEq κ] (g : C.CFG ν φ κ) (h : PhiFree g)
    (ℓ : κ) :
    Densem.CFG.lookup (cfg g h) ℓ =
      (lookup g ℓ).map block := by
  unfold Densem.CFG.lookup cfg lookup
  induction g.blocks with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.map_cons, List.find?_cons]
      split <;> simp_all

def continueFuel [DecidableEq ν] [DecidableEq κ]
    (M : Densem.Model φ) (g : C.CFG ν φ κ) :
    Nat → Env M ν → Densem.Exit κ M.Val → Option M.Val
  | _, _, .return a => some a
  | 0, _, .branch _ => none
  | fuel + 1, ρ, .branch ℓ => do
      let b ← lookup g ℓ
      let (ρ', exit) ← blockDenote M ρ b
      continueFuel M g fuel ρ' exit

def cfgRunFuel [DecidableEq ν] [DecidableEq κ] (M : Densem.Model φ)
    (g : C.CFG ν φ κ) : Nat → Env M ν → Option M.Val
  | 0, _ => none
  | fuel + 1, ρ => do
      let (ρ', exit) ← blockDenote M ρ g.entry
      continueFuel M g fuel ρ' exit

theorem continueFuel_commute [DecidableEq ν] [DecidableEq κ]
    (M : Densem.Model φ) (g : C.CFG ν φ κ) (h : PhiFree g)
    (fuel : Nat) (ρ : Env M ν) (e : Densem.Exit κ M.Val) :
    Densem.CFG.continueFuel M (cfg g h) fuel ρ e =
      continueFuel M g fuel ρ e := by
  induction fuel generalizing ρ e with
  | zero => cases e <;> rfl
  | succ fuel ih =>
      cases e with
      | «return» a => rfl
      | branch ℓ =>
        simp only [Densem.CFG.continueFuel, continueFuel]
        rw [lookup_map]
        cases hb : lookup g ℓ with
        | none => rfl
        | some b =>
          dsimp
          rw [block_commute]
          cases hd : blockDenote M ρ b with
          | none => rfl
          | some p =>
            cases p with
            | mk ρ' e => simpa only [Option.bind_some] using ih ρ' e

theorem cfg_runFuel_commute [DecidableEq ν] [DecidableEq κ]
    (M : Densem.Model φ) (g : C.CFG ν φ κ) (h : PhiFree g)
    (fuel : Nat) (ρ : Env M ν) :
    Densem.CFG.runFuel M (cfg g h) fuel ρ = cfgRunFuel M g fuel ρ := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp only [Densem.CFG.runFuel, cfgRunFuel, cfg]
      rw [block_commute]
      cases he : blockDenote M ρ g.entry with
      | none => rfl
      | some p =>
        cases p with
        | mk ρ' e => simpa only [Option.bind_some] using
            continueFuel_commute M g h fuel ρ' e

theorem cfg_denotes_iff [DecidableEq ν] [DecidableEq κ]
    (M : Densem.Model φ) (g : C.CFG ν φ κ) (h : PhiFree g)
    (fuel : Nat) (ρ : Env M ν) (a : M.Val) :
    Densem.CFG.Denotes M (cfg g h) fuel ρ a ↔ cfgRunFuel M g fuel ρ = some a := by
  unfold Densem.CFG.Denotes
  rw [cfg_runFuel_commute]

end Executable

end Isotope.TAC.Densem.Classical
