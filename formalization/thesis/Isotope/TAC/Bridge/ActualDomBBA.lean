import Isotope.TAC.Bridge.DomFlat
import Isotope.TAC.Bridge.PhiBBA
import Mathlib.Data.List.FinRange

/-!
# Lexical dominator trees as actual flat BBA CFGs

Unlike `DomFlat`, this module targets the paper's ordinary block-with-arguments
CFG syntax.  Structural paths name every non-entry block.  Lambda terms are
retained as symbolic operands; locally bound results receive structural names.
-/

namespace Isotope.TAC.Bridge.ActualDomBBA

open Isotope
open Isotope.LambdaSSA
open Isotope.TAC.Bridge.LambdaSSA

universe u v w

variable {Phi : Type u}

abbrev Address := Bridge.BlockAddress

/-- Globally distinct instruction results, or a symbolic lambda-SSA operand. -/
abbrev Var (Phi : Type u) := (Address × Nat) ⊕ Tm Phi

/-- Primitive operations retain their complete lambda term.  This is the
syntax-only lowering used in the paper-level correspondence. -/
abbrev Op (Phi : Type u) := Tm Phi

def value (term : Tm Phi) : Classical.Value (Var Phi) := .var (.inr term)

def operand (term : Tm Phi) : Classical.Operand (Var Phi) (Op Phi) :=
  .app term .unit

def lowerBodyAt (address : Address) : Nat → Body Phi → List (Classical.Instr (Var Phi) (Op Phi))
  | _, .nil => []
  | next, .let₁ term rest =>
      .assign (.inl (address, next)) (operand term) :: lowerBodyAt address (next + 1) rest
  | next, .let₂ term rest =>
      .assignPair (.inl (address, next)) (.inl (address, next + 1)) (operand term) ::
        lowerBodyAt address (next + 2) rest

def target (scope : List Address) (label : Nat) : Address :=
  scope.getD label []

def lowerTerminator (scope : List Address) : LambdaSSA.Terminator Phi →
    PhiBBA.Terminator (Var Phi) (Op Phi) Address
  | .br label argument => .br (target scope label) [value argument]
  | .case discr left right =>
      .cond (operand discr) (lowerTerminator scope left) (lowerTerminator scope right)

/-- Lower one lexical block.  Every named block has the single argument bound
by lambda-SSA's block convention; the distinguished entry has none. -/
def lowerBlock (named : Bool) (address : Address) (scope : List Address)
    (block : LambdaSSA.Block Phi) : PhiBBA.Block (Var Phi) (Op Phi) Address where
  parameters := if named then [.inl (address, 0)] else []
  body := lowerBodyAt address (if named then 1 else 0) block.body
  terminator := lowerTerminator scope block.terminator

/-- An actual BBA CFG equipped with an explicit immediate-dominator tree. -/
inductive Tree (V : Type u) (O : Type v) (L : Type w) where
  | node (block : PhiBBA.Block V O L) (arity : Nat)
      (children : Fin arity → L × Tree V O L)

namespace Tree

def root : Tree V O L → PhiBBA.Block V O L
  | .node block _ _ => block

noncomputable def namedBlocks : Tree V O L → List (L × PhiBBA.Block V O L) :=
  Tree.rec (motive_1 := fun _ => List (L × PhiBBA.Block V O L))
    (motive_2 := fun _ => List (L × PhiBBA.Block V O L))
    (fun _ arity children recurse =>
      (List.ofFn fun i =>
        ((children i).1, (children i).2.root) :: recurse i).flatten)
    (fun _ _ recurse => recurse)

noncomputable def toCFG (tree : Tree V O L) : PhiBBA.CFG V O L where
  entry := tree.root
  blocks := tree.namedBlocks

/-- A dominator-tree witness for an independently supplied flat CFG.  Block
order is deliberately quotiented by permutation, as in the paper. -/
structure Presents (tree : Tree V O L) (cfg : PhiBBA.CFG V O L) : Prop where
  entry_eq : tree.root = cfg.entry
  blocks_perm : tree.namedBlocks.Perm cfg.blocks

/-- `toReg` recovers the explicitly chosen dominator organization. -/
def toReg (_cfg : PhiBBA.CFG V O L) (tree : Tree V O L) (_ : tree.Presents _cfg) :
    Tree V O L := tree

/-- Flattening a CFG with its valid dominator-tree witness reconstructs the
original classical graph modulo the semantically irrelevant block order. -/
theorem toCFG_toReg (cfg : PhiBBA.CFG V O L) (tree : Tree V O L)
    (h : tree.Presents cfg) :
    (tree.toReg cfg h).toCFG.entry = cfg.entry ∧
      (tree.toReg cfg h).toCFG.blocks.Perm cfg.blocks :=
  ⟨h.entry_eq, h.blocks_perm⟩

@[simp] theorem presents_toCFG (tree : Tree V O L) : tree.Presents tree.toCFG :=
  ⟨rfl, .refl _⟩

end Tree

namespace LabelRenaming

/-- Coherent relabeling acts on every branch occurrence, including branches
nested below a conditional. -/
def renameTerminator (rho : L → L') : PhiBBA.Terminator V O L → PhiBBA.Terminator V O L'
  | .br target arguments => .br (rho target) arguments
  | .ret result => .ret result
  | .cond discr left right =>
      .cond discr (renameTerminator rho left) (renameTerminator rho right)

@[simp] theorem renameTerminator_id (term : PhiBBA.Terminator V O L) :
    renameTerminator id term = term := by
  induction term with
  | br => rfl
  | ret => rfl
  | cond discr left right ihl ihr => simp [renameTerminator, ihl, ihr]

def renameBlock (rho : L → L') (block : PhiBBA.Block V O L) :
    PhiBBA.Block V O L' :=
  { parameters := block.parameters
    body := block.body
    terminator := renameTerminator rho block.terminator }

@[simp] theorem renameBlock_id (block : PhiBBA.Block V O L) :
    renameBlock id block = block := by
  cases block
  simp [renameBlock]

def renameCFG (rho : L → L') (cfg : PhiBBA.CFG V O L) :
    PhiBBA.CFG V O L' where
  entry := renameBlock rho cfg.entry
  blocks := cfg.blocks.map fun (label, block) => (rho label, renameBlock rho block)

/-- Equality of actual flat BBAs up to one coherent label equivalence and an
irrelevant permutation of the named block collection.  In particular this
does not mistake raw sibling permutation for soundness: all branch targets are
transported by the same equivalence as block definitions. -/
def LabelEquivalent (left : PhiBBA.CFG V O L) (right : PhiBBA.CFG V O L') : Prop :=
  ∃ e : L ≃ L',
    (renameBlock e left.entry = right.entry) ∧
    (left.blocks.map fun (label, block) => (e label, renameBlock e block)).Perm right.blocks

@[refl] theorem LabelEquivalent.refl (cfg : PhiBBA.CFG V O L) :
    LabelEquivalent cfg cfg := by
  refine ⟨Equiv.refl L, ?_, ?_⟩
  · cases cfg.entry
    simp [renameBlock]
  · simpa using List.Perm.refl cfg.blocks

end LabelRenaming

namespace LexicalDomTree

private def childAddress (here : Address) (i : Nat) := here ++ [i]

/-- Concrete lowering of a lexical dominator tree to an actual BBA dominator
tree.  The scope lists structural addresses in de Bruijn-label order. -/
noncomputable def toActualTreeAt (named : Bool) (here : Address)
    (outer : List Address) : Bridge.LambdaSSA.DomTree Phi → Tree (Var Phi) (Op Phi) Address
  | .node block arity children =>
      let childScope := List.ofFn fun i : Fin arity => childAddress here i
      .node (lowerBlock named here (childScope ++ outer) block) arity fun i =>
        let address := childAddress here i
        (address, toActualTreeAt true address (childScope ++ outer) (children i))

noncomputable def toActualTree (tree : Bridge.LambdaSSA.DomTree Phi) :
    Tree (Var Phi) (Op Phi) Address :=
  toActualTreeAt false [] [] tree

/-- The paper's `toCFG`, now landing in `PhiBBA.CFG` rather than an auxiliary
flat-node datatype. -/
noncomputable def toActualCFG (tree : Bridge.LambdaSSA.DomTree Phi) :
    PhiBBA.CFG (Var Phi) (Op Phi) Address := (toActualTree tree).toCFG

@[simp] theorem toActualTree_presents (tree : Bridge.LambdaSSA.DomTree Phi) :
    (toActualTree tree).Presents (toActualCFG tree) := Tree.presents_toCFG _

/-- Choosing the generated dominator tree and applying `toReg` is an exact
left inverse of the concrete flattening. -/
@[simp] theorem toReg_toActualCFG (tree : Bridge.LambdaSSA.DomTree Phi) :
    Tree.toReg (toActualCFG tree) (toActualTree tree) (toActualTree_presents tree) =
      toActualTree tree := rfl

/-- Re-flattening the recovered dominator organization reconstructs the actual
BBA CFG (and hence, a fortiori, reconstructs it modulo block permutation). -/
theorem toActualCFG_toReg (tree : Bridge.LambdaSSA.DomTree Phi) :
    let recovered := Tree.toReg (toActualCFG tree) (toActualTree tree)
      (toActualTree_presents tree)
    recovered.toCFG = toActualCFG tree := by
  rfl

/-- The exact reconstruction also implies the paper's weaker observation:
the recovered graph is unchanged up to coherent label equivalence and block
permutation. -/
theorem toActualCFG_toReg_labelEquivalent (tree : Bridge.LambdaSSA.DomTree Phi) :
    let recovered := Tree.toReg (toActualCFG tree) (toActualTree tree)
      (toActualTree_presents tree)
    LabelRenaming.LabelEquivalent recovered.toCFG (toActualCFG tree) := by
  exact LabelRenaming.LabelEquivalent.refl _

end LexicalDomTree

end Isotope.TAC.Bridge.ActualDomBBA
