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

/-- Uses in an instruction may refer to dominating definitions or earlier
definitions in the same straight-line body. -/
def BodyUsesWellScoped [DecidableEq Var] (cfg : CFG Var Op Label)
    (bid : BlockId Label) (block : Block Var Op Label) : Prop :=
  ∀ i (hi : i < block.body.length) x, x ∈ block.body[i].uses →
    (∃ d db, cfg.lookup db = some d ∧ x ∈ defs d ∧ cfg.Dominates db bid) ∨
    ∃ j, ∃ hj : j < i, x ∈ block.body[j].defs

/-- Phi incoming values are checked at the end of their named predecessor,
the classical exceptional scoping rule. -/
def PhisWellFormed [DecidableEq Var] (cfg : CFG Var Op Label)
    (bid : BlockId Label) (block : Block Var Op Label) : Prop :=
  ∀ (phi : Phi Var Label), phi ∈ block.phis →
    (phi.incoming.map Incoming.predecessor).Nodup ∧
    (∀ (incoming : Incoming Var Label), incoming ∈ phi.incoming →
      bid ∈ cfg.successors (.named incoming.predecessor) ∧
      ∀ x ∈ incoming.value.uses,
        ∃ d db, cfg.lookup db = some d ∧ x ∈ defs d ∧
          cfg.Dominates db (.named incoming.predecessor))

/-- Explicit classical SSA property: a flat, closed CFG; globally unique
definitions; dominance-scoped ordinary uses; and predecessor-scoped phi uses. -/
structure WellFormed [DecidableEq Var] (cfg : CFG Var Op Label) : Prop where
  uniqueLabels : cfg.uniqueLabels
  targetsExist : cfg.targetsExist
  singleAssignment : cfg.singleAssignment
  entryBody : cfg.BodyUsesWellScoped .entry cfg.entry
  entryPhis : cfg.PhisWellFormed .entry cfg.entry
  blockBody (label block) (h : cfg.lookup (.named label) = some block) :
    cfg.BodyUsesWellScoped (.named label) block
  blockPhis (label block) (h : cfg.lookup (.named label) = some block) :
    cfg.PhisWellFormed (.named label) block

theorem WellFormed.defs_unique [DecidableEq Var] {cfg : CFG Var Op Label}
    (h : cfg.WellFormed) : cfg.allDefs.Nodup := h.singleAssignment

end CFG

end Isotope.TAC.Classical
