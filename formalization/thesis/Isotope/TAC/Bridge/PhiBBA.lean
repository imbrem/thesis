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

/-! ## Whole-CFG normalization

Classical phi syntax names a predecessor, whereas a BBA places the same value
on an edge.  The translations below choose the textual order of the entry
block followed by the named blocks as the canonical predecessor order.  A BBA
is normalized precisely when every edge to a given target from a given source
has the same, correctly-sized argument vector.  On the phi side this says that
the entry has no phis and every named block contains exactly the corresponding
canonical predecessor matrix.  The executable fixed-point predicates below
also reject missing blocks, missing phi rows, and missing predecessor entries.
-/

section CFGConversion

variable [DecidableEq Label]

/-- Look up a named classical block. -/
def findPhiBlock (cfg : Classical.CFG Var Op Label) (label : Label) :
    Option (Classical.Block Var Op Label) :=
  (cfg.blocks.find? fun block => block.1 = label).map Prod.snd

/-- The value selected by one phi row for a particular predecessor. -/
def findIncoming (predecessor : BlockId Label) (phi : Phi Var Label) :
    Option (Value Var) :=
  (phi.incoming.find? fun incoming => incoming.predecessor = predecessor).map
    Incoming.value

namespace Terminator

/-- Put phi operands on every outgoing edge.  Failure exposes exactly the two
ill-formed cases relevant here: an absent target or an absent predecessor row. -/
def ofPhi (cfg : Classical.CFG Var Op Label) (source : BlockId Label) :
    Classical.Terminator Var Op Label → Option (Terminator Var Op Label)
  | .br target =>
      (findPhiBlock cfg target).bind fun block =>
        (block.phis.mapM fun phi => findIncoming source phi).map fun arguments =>
          Terminator.br target arguments
  | .ret value => pure (.ret value)
  | .cond discr left right =>
      return .cond discr (← ofPhi cfg source left) (← ofPhi cfg source right)

@[simp] theorem eraseArguments_ofPhi {cfg : Classical.CFG Var Op Label}
    {source : BlockId Label} {term : Classical.Terminator Var Op Label}
    {result : Terminator Var Op Label} (h : ofPhi cfg source term = some result) :
    result.eraseArguments = term := by
  induction term generalizing result with
  | br target =>
      cases hblock : findPhiBlock cfg target with
      | none => simp [ofPhi, hblock] at h
      | some block =>
        cases hargs : block.phis.mapM (fun phi => findIncoming source phi) with
        | none => simp [ofPhi, hblock, hargs] at h
        | some arguments =>
          simp [ofPhi, hblock, hargs] at h
          cases h
          rfl
  | ret value => simp [ofPhi] at h; cases h; rfl
  | cond discr left right ihLeft ihRight =>
      cases hleft : ofPhi cfg source left with
      | none => simp [ofPhi, hleft] at h
      | some left' =>
        cases hright : ofPhi cfg source right with
        | none => simp [ofPhi, hleft, hright] at h
        | some right' =>
          simp [ofPhi, hleft, hright] at h
          cases h
          simp [eraseArguments, ihLeft hleft, ihRight hright]

end Terminator

namespace CFG

/-- Convert a classical phi CFG to a flat BBA, moving each phi operand to its
source edge.  The distinguished entry cannot carry parameters. -/
def ofPhi (cfg : Classical.CFG Var Op Label) : Option (CFG Var Op Label) := do
  if cfg.entry.phis.isEmpty then
    let entryTerm ← Terminator.ofPhi cfg .entry cfg.entry.terminator
    let blocks ← cfg.blocks.mapM fun (label, block) => do
      let term ← Terminator.ofPhi cfg (.named label) block.terminator
      pure (label, {
        parameters := block.phis.map Phi.dst
        body := block.body
        terminator := term
      })
    pure {
      entry := { parameters := [], body := cfg.entry.body, terminator := entryTerm }
      blocks := blocks
    }
  else none

/-- All edge occurrences, decorated by their source block, in canonical
entry-then-textual-block order. -/
def sourcedEdges (cfg : CFG Var Op Label) :
    List (BlockId Label × Label × List (Value Var)) :=
  (cfg.entry.terminator.edges.map fun edge => (.entry, edge.1, edge.2)) ++
    cfg.blocks.flatMap fun (source, block) =>
      block.terminator.edges.map fun edge => (.named source, edge.1, edge.2)

/-- Canonical incoming column `index` for a target.  Short edge vectors are
omitted; the normalization predicate below therefore rejects them. -/
def incomingColumn (cfg : CFG Var Op Label) (target : Label) (index : Nat) :
    List (Incoming Var Label) :=
  cfg.sourcedEdges.filterMap fun (source, destination, arguments) =>
    if destination = target then
      (arguments[index]?).map fun value => ⟨source, value⟩
    else none

/-- Move edge arguments into phi rows.  Textual source order fixes the order of
every incoming list. -/
def toPhi (cfg : CFG Var Op Label) : Classical.CFG Var Op Label where
  entry := {
    phis := []
    body := cfg.entry.body
    terminator := cfg.entry.terminator.eraseArguments
  }
  blocks := cfg.blocks.map fun (label, block) => (label, {
    phis := block.parameters.mapIdx fun index parameter => {
      dst := parameter
      incoming := cfg.incomingColumn label index
    }
    body := block.body
    terminator := block.terminator.eraseArguments
  })

/-! ### Structural normalization

The predicates in this section state normalization directly on the two source
syntaxes.  In particular, they do not define well-formedness by running either
conversion and comparing its result. -/

/-- Predecessor occurrences of `target`, in the same entry-then-block and
left-to-right order used by `incomingColumn`. -/
def phiPredecessors (cfg : Classical.CFG Var Op Label) (target : Label) :
    List (BlockId Label) :=
  (if target ∈ cfg.entry.terminator.targets then [.entry] else []) ++
    cfg.blocks.flatMap fun (source, block) =>
      if target ∈ block.terminator.targets then [.named source] else []

/-- Every control-flow target denotes exactly one named block. -/
def PhiTargetsDefined (cfg : Classical.CFG Var Op Label) : Prop :=
  ∀ target,
    target ∈ cfg.entry.terminator.targets ∨
      (∃ source block, (source, block) ∈ cfg.blocks ∧
        target ∈ block.terminator.targets) →
    ∃! block, (target, block) ∈ cfg.blocks

/-- Independent structural conditions for canonical classical phi form:
destinations and block labels are unique, every target resolves, and each phi
has exactly one incoming row per predecessor, in canonical predecessor order. -/
def PhiStructurallyNormalized (cfg : Classical.CFG Var Op Label) : Prop :=
  cfg.entry.phis = [] ∧
  (cfg.blocks.map Prod.fst).Nodup ∧
  PhiTargetsDefined cfg ∧
  ∀ label block, (label, block) ∈ cfg.blocks →
    (block.phis.map Phi.dst).Nodup ∧
    ∀ phi, phi ∈ block.phis →
      phi.incoming.map Incoming.predecessor = phiPredecessors cfg label ∧
      (phi.incoming.map Incoming.predecessor).Nodup

/-- Target lookup in the BBA syntax, used only to state its structural arity
condition. -/
def findBlock (cfg : CFG Var Op Label) (label : Label) : Option (Block Var Op Label) :=
  (cfg.blocks.find? fun block => block.1 = label).map Prod.snd

/-- All source/target occurrences after forgetting the argument vectors. -/
def edgeKeys (cfg : CFG Var Op Label) : List (BlockId Label × Label) :=
  cfg.sourcedEdges.map fun (source, target, _) => (source, target)

/-- Independent structural conditions for canonical BBA form.  Entry has no
parameters, block parameters and labels are unique, each source has at most one
edge to a target, and every edge vector has the target block's arity. -/
def BBAStructurallyNormalized (cfg : CFG Var Op Label) : Prop :=
  cfg.entry.parameters = [] ∧
  (cfg.blocks.map Prod.fst).Nodup ∧
  cfg.edgeKeys.Nodup ∧
  (∀ label block, (label, block) ∈ cfg.blocks → block.parameters.Nodup) ∧
  ∀ source target arguments, (source, target, arguments) ∈ cfg.sourcedEdges →
    ∃ block, cfg.findBlock target = some block ∧
      arguments.length = block.parameters.length

/-- Structural phi normalization exposes uniqueness of every incoming
predecessor without referring to either translation. -/
theorem PhiStructurallyNormalized.incoming_predecessors_nodup
    {cfg : Classical.CFG Var Op Label} (hcfg : PhiStructurallyNormalized cfg)
    {label : Label} {block : Classical.Block Var Op Label}
    (hblock : (label, block) ∈ cfg.blocks) {phi : Phi Var Label}
    (hphi : phi ∈ block.phis) :
    (phi.incoming.map Incoming.predecessor).Nodup :=
  (hcfg.2.2.2 label block hblock).2 phi hphi |>.2

/-- Structural BBA normalization gives the uniform target arity required by
the phi/BBA matrix transpose. -/
theorem BBAStructurallyNormalized.edge_arity
    {cfg : CFG Var Op Label} (hcfg : BBAStructurallyNormalized cfg)
    {source : BlockId Label} {target : Label} {arguments : List (Value Var)}
    (hedge : (source, target, arguments) ∈ cfg.sourcedEdges) :
    ∃ block, cfg.findBlock target = some block ∧
      arguments.length = block.parameters.length :=
  hcfg.2.2.2.2 source target arguments hedge

/-- In canonical BBA form source/target pairs have no duplicate occurrence. -/
theorem BBAStructurallyNormalized.edge_keys_nodup
    {cfg : CFG Var Op Label} (hcfg : BBAStructurallyNormalized cfg) :
    cfg.edgeKeys.Nodup :=
  hcfg.2.2.1

/-- A normalized phi CFG is one on which moving operands to edges succeeds and
canonicalizing them back is literally the identity.  Expanded, this requires
an empty entry phi list, resolvable and coherent target definitions, one
incoming value for each source/target occurrence and phi row, and canonical
row/source order. -/
def PhiNormalized (cfg : Classical.CFG Var Op Label) : Prop :=
  ∃ bba, ofPhi cfg = some bba ∧ toPhi bba = cfg

/-- A normalized BBA has rectangular edge vectors and is source-functional for
each target; equivalently its canonical phis move back to the identical CFG. -/
def BBANormalized (cfg : CFG Var Op Label) : Prop :=
  ofPhi (toPhi cfg) = some cfg

@[simp] theorem toPhi_entry_phis (cfg : CFG Var Op Label) :
    (toPhi cfg).entry.phis = [] := rfl

/-- Erase phi rows while retaining the classical control-flow skeleton. -/
def erasePhis (cfg : Classical.CFG Var Op Label) : Classical.CFG Var Op Label :=
  { cfg with
      entry := { cfg.entry with phis := [] }
      blocks := cfg.blocks.map fun (label, block) =>
        (label, { block with phis := [] }) }

/-- Both presentations erase to exactly the same control-flow graph. -/
theorem erasePhis_toPhi (cfg : CFG Var Op Label) :
    erasePhis (toPhi cfg) = cfg.eraseArguments := by
  cases cfg with
  | mk entry blocks =>
    cases entry
    simp [erasePhis, toPhi, eraseArguments]

/-- The phi-to-BBA-to-phi round trip for any successful normalized
translation. -/
theorem toPhi_ofPhi {cfg : Classical.CFG Var Op Label}
    (hcfg : PhiNormalized cfg) {bba : CFG Var Op Label}
    (h : ofPhi cfg = some bba) : toPhi bba = cfg := by
  rcases hcfg with ⟨canonical, hcanonical, hround⟩
  have : canonical = bba := Option.some.inj (hcanonical.symm.trans h)
  simpa [this] using hround

/-- The BBA-to-phi-to-BBA round trip is the executable content of BBA
normalization. -/
theorem ofPhi_toPhi {cfg : CFG Var Op Label} (hcfg : BBANormalized cfg) :
    ofPhi (toPhi cfg) = some cfg := hcfg

/-- A successful normalized conversion preserves the erased CFG exactly. -/
theorem erase_ofPhi {cfg : Classical.CFG Var Op Label}
    (hcfg : PhiNormalized cfg) {bba : CFG Var Op Label}
    (h : ofPhi cfg = some bba) : erasePhis cfg = bba.eraseArguments := by
  rw [← toPhi_ofPhi hcfg h]
  exact erasePhis_toPhi bba

/-- Exact equivalence between the two normalized whole-CFG presentations. -/
noncomputable def normalizedEquiv :
    {cfg : Classical.CFG Var Op Label // PhiNormalized cfg} ≃
      {cfg : CFG Var Op Label // BBANormalized cfg} where
  toFun cfg := by
    let bba := Classical.choose cfg.property
    have hbba := (Classical.choose_spec cfg.property).1
    have hround := (Classical.choose_spec cfg.property).2
    exact ⟨bba, by rw [BBANormalized, hround]; exact hbba⟩
  invFun cfg := ⟨toPhi cfg, ⟨cfg, cfg.property, rfl⟩⟩
  left_inv cfg := by
    apply Subtype.ext
    exact (Classical.choose_spec cfg.property).2
  right_inv cfg := by
    apply Subtype.ext
    let hx : PhiNormalized (toPhi cfg.val) :=
      ⟨cfg.val, (show ofPhi (toPhi cfg.val) = some cfg.val from cfg.property), rfl⟩
    have hchosen := (Classical.choose_spec hx).1
    exact Option.some.inj (hchosen.symm.trans cfg.property)

end CFG

end CFGConversion

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
