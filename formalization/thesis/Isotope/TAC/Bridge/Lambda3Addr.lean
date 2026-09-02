import Isotope.TAC.Densem.Classical
import Isotope.TAC.Densem.MonadicClassical
import Mathlib.Logic.Equiv.Defs

/-! # Lambda three-address code and flat classical TAC

The nested densem block syntax is the lambda-style presentation of
three-address code: instruction destinations scope over the remaining block.
This file records its exact isomorphism with the phi-free fragment of the
paper's flat classical syntax.
-/

namespace Isotope.TAC.Bridge.Lambda3Addr

open Isotope.TAC

universe u v w

abbrev Syntax := Densem.CFG

def ofTerminator : Densem.Terminator φ ν κ → Classical.Terminator ν φ κ
  | .br label => .br label
  | .ret value => .ret (Densem.Classical.ofValue value)
  | .ite discr left right =>
      .cond (Densem.Classical.ofOperand discr)
        (ofTerminator left) (ofTerminator right)

def ofBlock : Densem.Block φ ν κ → Classical.Block ν φ κ
  | .terminator term => ⟨[], [], ofTerminator term⟩
  | .let₁ dst rhs rest =>
      let block := ofBlock rest
      { block with body := .assign dst (Densem.Classical.ofOperand rhs) :: block.body }
  | .let₂ fst snd rhs rest =>
      let block := ofBlock rest
      { block with
        body := .assignPair fst snd (Densem.Classical.ofOperand rhs) :: block.body }

@[simp] theorem value_ofValue (value : Densem.Value ν) :
    Densem.Classical.value (Densem.Classical.ofValue value) = value := by
  induction value <;>
    simp [Densem.Classical.value, Densem.Classical.ofValue, *]

@[simp] theorem operand_ofOperand (operand : Densem.Operand φ ν) :
    Densem.Classical.operand (Densem.Classical.ofOperand operand) = operand := by
  cases operand <;>
    simp [Densem.Classical.operand, Densem.Classical.ofOperand]

@[simp] theorem ofTerminator_terminator (term : Classical.Terminator ν φ κ) :
    ofTerminator (Densem.Classical.terminator term) = term := by
  induction term <;> simp [Densem.Classical.terminator, ofTerminator, *]

@[simp] theorem terminator_ofTerminator (term : Densem.Terminator φ ν κ) :
    Densem.Classical.terminator (ofTerminator term) = term := by
  induction term <;> simp [Densem.Classical.terminator, ofTerminator, *]

@[simp] theorem ofBlock_phis (block : Densem.Block φ ν κ) :
    (ofBlock block).phis = [] := by
  induction block <;> simp [ofBlock, *]

@[simp] theorem block_ofBlock (block : Densem.Block φ ν κ) :
    Densem.Classical.block (ofBlock block) = block := by
  induction block with
  | terminator term =>
      simp [ofBlock, Densem.Classical.block, Densem.Classical.instructions]
  | let₁ dst rhs rest ih =>
      change Densem.Classical.instructions (ofBlock rest).body
        (Densem.Classical.terminator (ofBlock rest).terminator) = rest at ih
      simp only [ofBlock, Densem.Classical.block, Densem.Classical.instructions,
        operand_ofOperand]
      rw [ih]
  | let₂ fst snd rhs rest ih =>
      change Densem.Classical.instructions (ofBlock rest).body
        (Densem.Classical.terminator (ofBlock rest).terminator) = rest at ih
      simp only [ofBlock, Densem.Classical.block, Densem.Classical.instructions,
        operand_ofOperand]
      rw [ih]

theorem ofBlock_block (block : Classical.Block ν φ κ) (hphi : block.phis = []) :
    ofBlock (Densem.Classical.block block) = block := by
  rcases block with ⟨phis, body, terminator⟩
  simp only at hphi
  subst phis
  induction body with
  | nil => simp [Densem.Classical.block, Densem.Classical.instructions, ofBlock]
  | cons instr rest ih =>
      change ofBlock (Densem.Classical.instructions rest
        (Densem.Classical.terminator terminator)) =
          { phis := [], body := rest, terminator := terminator } at ih
      cases instr <;>
        simp only [Densem.Classical.block, Densem.Classical.instructions, ofBlock,
          Densem.Classical.ofOperand_operand] <;>
        rw [ih]

def ofCFG (cfg : Densem.CFG φ ν κ) : Classical.CFG ν φ κ where
  entry := ofBlock cfg.entry
  blocks := cfg.blocks.map fun pair => (pair.1, ofBlock pair.2)

theorem ofCFG_phiFree (cfg : Densem.CFG φ ν κ) :
    Densem.Classical.PhiFree (ofCFG cfg) := by
  constructor
  · exact ofBlock_phis cfg.entry
  · intro pair hpair
    simp only [ofCFG, List.mem_map] at hpair
    rcases hpair with ⟨source, _, rfl⟩
    exact ofBlock_phis source.2

@[simp] theorem cfg_ofCFG (cfg : Densem.CFG φ ν κ) :
    Densem.Classical.cfg (ofCFG cfg) (ofCFG_phiFree cfg) = cfg := by
  cases cfg with
  | mk entry blocks =>
      simp [ofCFG, Densem.Classical.cfg, block_ofBlock, Function.comp_def]

theorem ofCFG_cfg (cfg : Classical.CFG ν φ κ)
    (hphi : Densem.Classical.PhiFree cfg) :
    ofCFG (Densem.Classical.cfg cfg hphi) = cfg := by
  cases cfg with
  | mk entry blocks =>
      simp only [Densem.Classical.cfg, ofCFG]
      congr 1
      · exact ofBlock_block entry hphi.entry
      · induction blocks with
        | nil => rfl
        | cons pair rest ih =>
            simp only [List.map_cons]
            apply congrArg₂ List.cons
            · exact congrArg (Prod.mk pair.1)
                (ofBlock_block pair.2 (hphi.blocks pair (by simp)))
            · apply ih
              constructor
              · exact hphi.entry
              · intro p hp
                exact hphi.blocks p (by simp [hp])

/-- Flat classical three-address programs, with absence of phi nodes carried
as part of the representation. -/
abbrev ClassicalSyntax (ν : Type u) (φ : Type v) (κ : Type w) :=
  { cfg : Classical.CFG ν φ κ // Densem.Classical.PhiFree cfg }

/-- The lambda-style nested and classical flat presentations are exactly
isomorphic; no quotient or ordering convention is needed in the phi-free
fragment. -/
def classicalEquiv : ClassicalSyntax ν φ κ ≃ Syntax φ ν κ where
  toFun cfg := Densem.Classical.cfg cfg.1 cfg.2
  invFun cfg := ⟨ofCFG cfg, ofCFG_phiFree cfg⟩
  left_inv cfg := by
    apply Subtype.ext
    exact ofCFG_cfg cfg.1 cfg.2
  right_inv := cfg_ofCFG

/-- The executable semantics commutes with the classical/lambda-three-address
isomorphism at every fuel bound. -/
theorem runFuel_classicalEquiv [DecidableEq ν] [DecidableEq κ]
    (M : Densem.Model φ) (cfg : ClassicalSyntax ν φ κ)
    (fuel : Nat) (env : Densem.Env M ν) :
    Densem.Phi.runFuel M cfg.1 fuel env =
      Densem.CFG.runFuel M (classicalEquiv cfg) fuel env := by
  exact Densem.Phi.runFuel_phiFree M cfg.1 cfg.2 fuel env

/-- The same square commutes for the direct complete-Elgot monadic semantics.
The distinguished failure element must be a left zero, exactly as required by
the phi-free semantic bridge. -/
theorem denote_classicalEquiv [Monad m] [LawfulMonad m]
    [Isotope.Elgot.Iterate m] [Isotope.Elgot.LawfulElgotMonad m]
    [DecidableEq ν] [DecidableEq κ]
    (M : Densem.Monadic.Model φ m) [Densem.Phi.Monadic.LawfulFailure M]
    (cfg : ClassicalSyntax ν φ κ) (env : Densem.Monadic.Env M ν) :
    Densem.Phi.Monadic.denote M cfg.1 env =
      Densem.Monadic.CFG.denote M (classicalEquiv cfg) env := by
  exact Densem.Phi.Monadic.denote_phiFree M cfg.1 cfg.2 env

end Isotope.TAC.Bridge.Lambda3Addr
