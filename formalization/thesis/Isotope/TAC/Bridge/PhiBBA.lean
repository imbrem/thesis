import Isotope.TAC.Classical.Syntax
import Mathlib.Logic.Equiv.Defs

/-! # Classical phi nodes and basic-block arguments

The paper takes flat basic blocks with arguments as its standard SSA syntax.
This module records that syntax and the exact, finite-matrix correspondence
between a block's phi interface and its block-argument interface.  The finite
indices make predecessor and parameter order explicit; no proof-irrelevance or
quotient by duplicate predecessor entries is hidden in the correspondence.
-/

namespace Isotope.TAC.Bridge.PhiBBA

open Isotope.TAC.Classical

universe u v w

/-- A BBA terminator.  Every jump supplies the target block's arguments. -/
inductive Terminator (Var : Type u) (Op : Type v) (Label : Type w) where
  | br (target : Label) (arguments : List (Value Var))
  | ret (value : Value Var)
  | cond (scrutinee : Operand Var Op)
      (thenBranch elseBranch : Terminator Var Op Label)
deriving DecidableEq, Repr

/-- A flat basic block with parameters rather than phi nodes. -/
structure Block (Var : Type u) (Op : Type v) (Label : Type w) where
  parameters : List Var
  body : List (Instr Var Op)
  terminator : Terminator Var Op Label
deriving DecidableEq, Repr

/-- Paper-style flat BBA SSA, with a distinguished nameless entry block. -/
structure CFG (Var : Type u) (Op : Type v) (Label : Type w) where
  entry : Block Var Op Label
  blocks : List (Label × Block Var Op Label)
deriving DecidableEq, Repr

variable {Var : Type u} {Op : Type v} {Label : Type w}

namespace Terminator

/-- Forget jump arguments, obtaining the underlying classical CFG control. -/
def eraseArguments : Terminator Var Op Label → Classical.Terminator Var Op Label
  | .br target _ => .br target
  | .ret value => .ret value
  | .cond discr left right =>
      .cond discr left.eraseArguments right.eraseArguments

/-- Target and argument-vector occurrences, in textual left-to-right order. -/
def edges : Terminator Var Op Label → List (Label × List (Value Var))
  | .br target arguments => [(target, arguments)]
  | .ret _ => []
  | .cond _ left right => left.edges ++ right.edges

@[simp] theorem targets_eraseArguments (t : Terminator Var Op Label) :
    t.eraseArguments.targets = t.edges.map Prod.fst := by
  induction t with
  | br => rfl
  | ret => rfl
  | cond discr left right ihLeft ihRight =>
      simp [eraseArguments, edges, ihLeft, ihRight,
        Classical.Terminator.targets, List.map_append]

end Terminator

namespace CFG

/-- Erase block parameters and edge arguments.  This is the common CFG
skeleton shared by phi-SSA and BBA SSA. -/
def eraseArguments (cfg : CFG Var Op Label) : Classical.CFG Var Op Label where
  entry := {
    phis := []
    body := cfg.entry.body
    terminator := cfg.entry.terminator.eraseArguments
  }
  blocks := cfg.blocks.map fun (label, block) => (label, {
    phis := []
    body := block.body
    terminator := block.terminator.eraseArguments
  })

@[simp] theorem eraseArguments_entry_body (cfg : CFG Var Op Label) :
    cfg.eraseArguments.entry.body = cfg.entry.body := rfl

@[simp] theorem eraseArguments_block_labels (cfg : CFG Var Op Label) :
    cfg.eraseArguments.blocks.map Prod.fst = cfg.blocks.map Prod.fst := by
  simp [eraseArguments]

end CFG

/-- A normalized phi interface with `P` ordered predecessor occurrences and
`A` ordered phi destinations.  `incoming a p` is phi-row-major. -/
structure PhiTable (Var : Type u) (Label : Type w) (P A : Nat) where
  destination : Fin A → Var
  predecessor : Fin P → BlockId Label
  incoming : Fin A → Fin P → Value Var

/-- The same interface in block-argument form.  `argument p a` is
edge-row-major, i.e. the transpose of `PhiTable.incoming`. -/
structure Header (Var : Type u) (Label : Type w) (P A : Nat) where
  parameter : Fin A → Var
  predecessor : Fin P → BlockId Label
  argument : Fin P → Fin A → Value Var

namespace PhiTable

def toHeader (table : PhiTable Var Label P A) : Header Var Label P A where
  parameter := table.destination
  predecessor := table.predecessor
  argument p a := table.incoming a p

/-- Render a normalized table in the repository's ordinary list-based phi
syntax.  Both list orders are now canonical and duplicate edge occurrences
remain distinguishable by their positions. -/
def toPhis (table : PhiTable Var Label P A) : List (Phi Var Label) :=
  List.ofFn fun a => {
    dst := table.destination a
    incoming := List.ofFn fun p => {
      predecessor := table.predecessor p
      value := table.incoming a p
    }
  }

@[simp] theorem toPhis_length (table : PhiTable Var Label P A) :
    table.toPhis.length = A := by simp [toPhis]

end PhiTable

namespace Header

def toPhiTable (header : Header Var Label P A) : PhiTable Var Label P A where
  destination := header.parameter
  predecessor := header.predecessor
  incoming a p := header.argument p a

def parameters (header : Header Var Label P A) : List Var :=
  List.ofFn header.parameter

def edgeArguments (header : Header Var Label P A) : List (List (Value Var)) :=
  List.ofFn fun p => List.ofFn fun a => header.argument p a

@[simp] theorem parameters_length (header : Header Var Label P A) :
    header.parameters.length = A := by simp [parameters]

@[simp] theorem edgeArguments_length (header : Header Var Label P A) :
    header.edgeArguments.length = P := by simp [edgeArguments]

theorem edgeArguments_rectangular (header : Header Var Label P A)
    (arguments : List (Value Var)) (h : arguments ∈ header.edgeArguments) :
    arguments.length = A := by
  simp only [edgeArguments, List.mem_ofFn] at h
  obtain ⟨p, rfl⟩ := h
  simp

end Header

@[simp] theorem PhiTable.toPhiTable_toHeader (table : PhiTable Var Label P A) :
    table.toHeader.toPhiTable = table := by
  cases table
  rfl

@[simp] theorem Header.toHeader_toPhiTable (header : Header Var Label P A) :
    header.toPhiTable.toHeader = header := by
  cases header
  rfl

/-- Exact phi-node/block-argument correspondence for a fixed ordered
predecessor interface and fixed block arity. -/
def phiTableEquivHeader :
    PhiTable Var Label P A ≃ Header Var Label P A where
  toFun := PhiTable.toHeader
  invFun := Header.toPhiTable
  left_inv := PhiTable.toPhiTable_toHeader
  right_inv := Header.toHeader_toPhiTable

/-- The concrete matrix-transposition law: the value supplied by predecessor
occurrence `p` to block parameter `a` is exactly the corresponding phi input. -/
@[simp] theorem argument_toHeader (table : PhiTable Var Label P A)
    (p : Fin P) (a : Fin A) :
    table.toHeader.argument p a = table.incoming a p := rfl

@[simp] theorem incoming_toPhiTable (header : Header Var Label P A)
    (a : Fin A) (p : Fin P) :
    header.toPhiTable.incoming a p = header.argument p a := rfl

end Isotope.TAC.Bridge.PhiBBA
