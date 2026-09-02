import Isotope.TAC.Classical.Syntax

/-! # Classical SSA well-formedness without a dominator-tree syntax -/

namespace Isotope.TAC.Classical

namespace CFG

universe u v w
variable {Var : Type u} {Op : Type v} {Label : Type w}
variable [DecidableEq Label]

def lookup (cfg : CFG Var Op Label) : BlockId Label → Option (Block Var Op Label)
  | .entry => some cfg.entry
  | .named label => cfg.blocks.lookup label

def labels (cfg : CFG Var Op Label) : List Label := cfg.blocks.map Prod.fst

def successors (cfg : CFG Var Op Label) (b : BlockId Label) : List (BlockId Label) :=
  match cfg.lookup b with
  | none => []
  | some block => block.terminator.targets.map BlockId.named

/-- A nonempty control-flow path, represented independently of any dominator tree. -/
inductive Path (cfg : CFG Var Op Label) :
    BlockId Label → List (BlockId Label) → BlockId Label → Prop
  | single (b) : Path cfg b [b] b
  | step {src next dst : BlockId Label} {rest : List (BlockId Label)} :
      next ∈ cfg.successors src → Path cfg next rest dst →
      Path cfg src (src :: rest) dst

/-- `d` dominates `b` iff every entry-to-`b` path contains `d`. -/
def Dominates (cfg : CFG Var Op Label) (d b : BlockId Label) : Prop :=
  ∀ path : List (BlockId Label), Path cfg .entry path b → d ∈ path

theorem Path.dst_mem {cfg : CFG Var Op Label} {src dst : BlockId Label}
    {path : List (BlockId Label)} (h : Path cfg src path dst) : dst ∈ path := by
  induction h with
  | single => simp
  | step _ _ ih => exact List.mem_cons_of_mem _ ih

theorem dominates_refl (cfg : CFG Var Op Label) (b : BlockId Label) :
    cfg.Dominates b b := fun _ path => path.dst_mem

def instrDefs (block : Block Var Op Label) : List Var := block.body.flatMap Instr.defs

def defs (block : Block Var Op Label) : List Var :=
  block.phis.map Phi.dst ++ instrDefs block

def allDefs (cfg : CFG Var Op Label) : List Var :=
  defs cfg.entry ++ cfg.blocks.flatMap fun p => defs p.2

def targetsExist (cfg : CFG Var Op Label) : Prop :=
  ∀ b target, target ∈ cfg.successors b → ∃ block, cfg.lookup target = some block

def uniqueLabels (cfg : CFG Var Op Label) : Prop := cfg.labels.Nodup

def singleAssignment [DecidableEq Var] (cfg : CFG Var Op Label) : Prop :=
  cfg.allDefs.Nodup

def AvailableFromDominatingBlock [DecidableEq Var] (cfg : CFG Var Op Label)
    (externals : List Var) (bid : BlockId Label) (x : Var) : Prop :=
  x ∈ externals ∨ ∃ d db, cfg.lookup db = some d ∧ x ∈ defs d ∧
    db ≠ bid ∧ cfg.Dominates db bid

/-- Uses in an instruction may refer to dominating definitions or earlier
definitions in the same straight-line body. -/
def BodyUsesWellScoped [DecidableEq Var] (cfg : CFG Var Op Label)
    (externals : List Var) (bid : BlockId Label) (block : Block Var Op Label) : Prop :=
  ∀ i (hi : i < block.body.length) x, x ∈ block.body[i].uses →
    cfg.AvailableFromDominatingBlock externals bid x ∨
    x ∈ block.phis.map Phi.dst ∨
    ∃ j, ∃ hj : j < i, x ∈ block.body[j].defs

/-- A terminator is after every ordinary definition in its block. -/
def TerminatorUsesWellScoped [DecidableEq Var] (cfg : CFG Var Op Label)
    (externals : List Var) (bid : BlockId Label) (block : Block Var Op Label) : Prop :=
  ∀ x ∈ block.terminator.uses,
    cfg.AvailableFromDominatingBlock externals bid x ∨ x ∈ defs block

/-- Phi incoming values are checked at the end of their named predecessor,
the classical exceptional scoping rule. -/
def PhisWellFormed [DecidableEq Var] (cfg : CFG Var Op Label)
    (externals : List Var) (bid : BlockId Label) (block : Block Var Op Label) : Prop :=
  ∀ (phi : Phi Var Label), phi ∈ block.phis →
    (phi.incoming.map Incoming.predecessor).Nodup ∧
    (∀ (incoming : Incoming Var Label), incoming ∈ phi.incoming →
      bid ∈ cfg.successors incoming.predecessor ∧
      ∀ x ∈ incoming.value.uses,
        x ∈ externals ∨ ∃ d, cfg.lookup incoming.predecessor = some d ∧ x ∈ defs d ∨
          ∃ d db, cfg.lookup db = some d ∧ x ∈ defs d ∧
            db ≠ incoming.predecessor ∧ cfg.Dominates db incoming.predecessor)

/-- Explicit classical SSA property: a flat, closed CFG; globally unique
definitions; dominance-scoped ordinary uses; and predecessor-scoped phi uses. -/
structure WellFormed [DecidableEq Var] (externals : List Var)
    (cfg : CFG Var Op Label) : Prop where
  externalsNodup : externals.Nodup
  externalsFresh : List.Disjoint externals cfg.allDefs
  uniqueLabels : cfg.uniqueLabels
  targetsExist : cfg.targetsExist
  singleAssignment : cfg.singleAssignment
  entryBody : cfg.BodyUsesWellScoped externals .entry cfg.entry
  entryTerminator : cfg.TerminatorUsesWellScoped externals .entry cfg.entry
  entryPhis : cfg.PhisWellFormed externals .entry cfg.entry
  blockBody (label block) (h : cfg.lookup (.named label) = some block) :
    cfg.BodyUsesWellScoped externals (.named label) block
  blockTerminator (label block) (h : cfg.lookup (.named label) = some block) :
    cfg.TerminatorUsesWellScoped externals (.named label) block
  blockPhis (label block) (h : cfg.lookup (.named label) = some block) :
    cfg.PhisWellFormed externals (.named label) block

theorem WellFormed.defs_unique [DecidableEq Var] {cfg : CFG Var Op Label}
    {externals : List Var} (h : cfg.WellFormed externals) : cfg.allDefs.Nodup :=
  h.singleAssignment

example : Incoming Nat Nat := ⟨.entry, .var 0⟩

end CFG

end Isotope.TAC.Classical
