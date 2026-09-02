import Isotope.LambdaSSA.Syntax

/-!
# The entry/dominator decomposition of lexical SSA

This is the proof-relevant form of the paper's `toEntry`, `toDom`, and
`addDom` construction.  The witness that a raw region is lexical SSA is data,
not a proposition which must be eliminated to obtain a dominator tree.
-/

namespace Isotope.TAC.Bridge.LambdaSSA

universe u

open Isotope.LambdaSSA

def terminatorRegion : Terminator Φ → Region Φ
  | .br label arg => .br label arg
  | .case discr left right =>
      .case discr (terminatorRegion left) (terminatorRegion right)

def wrapBody : Body Φ → Region Φ → Region Φ
  | .nil, region => region
  | .let₁ value rest, region => .let₁ value (wrapBody rest region)
  | .let₂ value rest, region => .let₂ value (wrapBody rest region)

/-- The paper's explicit dominator-tree view of a lexical SSA region. -/
inductive DomTree (Φ : Type u) where
  | node (entry : Block Φ) (arity : Nat) (children : Fin arity → DomTree Φ)

namespace DomTree

/-- `addDom`: reassemble an entry block and its immediate dominated subtrees. -/
def addDom : DomTree Φ → Region Φ
  | .node entry arity children =>
      wrapBody entry.body
        (.cfg (terminatorRegion entry.terminator) arity
          (fun i => addDom (children i)))

/-- `toEntry`: the root basic block. -/
def toEntry : DomTree Φ → Block Φ
  | .node entry _ _ => entry

/-- The number of root children. -/
def domArity : DomTree Φ → Nat
  | .node _ arity _ => arity

/-- `toDom`: the root's ordered immediate dominated subregions. -/
def toDom (tree : DomTree Φ) : Fin tree.domArity → DomTree Φ :=
  match tree with
  | .node _ _ children => children

def assemble (entry : Block Φ) (arity : Nat) (children : Fin arity → DomTree Φ) :
    DomTree Φ := .node entry arity children

@[simp] theorem toEntry_assemble (entry : Block Φ) (arity) (children : Fin arity → DomTree Φ) :
    (assemble entry arity children).toEntry = entry := rfl

@[simp] theorem domArity_assemble (entry : Block Φ) (arity) (children : Fin arity → DomTree Φ) :
    (assemble entry arity children).domArity = arity := rfl

@[simp] theorem toDom_assemble (entry : Block Φ) (arity) (children : Fin arity → DomTree Φ) :
    (assemble entry arity children).toDom = children := rfl

/-- The exact `addDom (toEntry r) (toDom r) = r` tree-level round trip. -/
@[simp] theorem assemble_toEntry_toDom (tree : DomTree Φ) :
    assemble tree.toEntry tree.domArity tree.toDom = tree := by cases tree; rfl

end DomTree

/-- A proof-relevant parser certificate for precisely the lexical SSA fragment
of raw `Region`. -/
inductive Decomposition : Region Φ → Type u where
  | node (entry : Block Φ) (arity : Nat) (children : Fin arity → DomTree Φ) :
      Decomposition (DomTree.addDom (.node entry arity children))

namespace Decomposition

/-- Extract the explicit dominator tree from a proof-relevant parse. -/
def tree {region : Region Φ} : Decomposition region → DomTree Φ
  | .node entry arity children => .node entry arity children

/-- Reassembly of a parsed region is definitionally faithful. -/
@[simp] theorem addDom_tree {region : Region Φ} (parsed : Decomposition region) :
    parsed.tree.addDom = region := by cases parsed; rfl

/-- Every explicit dominator tree gives a certificate for its reassembly. -/
def ofTree (tree : DomTree Φ) : Decomposition tree.addDom := by
  cases tree with
  | node entry arity children => exact .node entry arity children

/-- Parsing after reassembly recovers the exact original tree. -/
@[simp] theorem tree_ofTree (tree : DomTree Φ) : (ofTree tree).tree = tree := by
  cases tree
  rfl

/-- Paper-level round trip stated directly for any certified lexical region. -/
theorem addDom_toEntry_toDom {region : Region Φ} (parsed : Decomposition region) :
    DomTree.addDom
      (DomTree.assemble parsed.tree.toEntry parsed.tree.domArity parsed.tree.toDom) = region := by
  rw [DomTree.assemble_toEntry_toDom, addDom_tree]

end Decomposition
end Isotope.TAC.Bridge.LambdaSSA
