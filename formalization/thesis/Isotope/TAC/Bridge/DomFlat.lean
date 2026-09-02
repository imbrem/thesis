import Isotope.TAC.Bridge.Decompose
import Isotope.TAC.Bridge.FlatBBA
import Mathlib.Data.List.FinRange

/-!
# Erasing a lexical dominator tree to a flat block collection

This is the proof-relevant version of the paper's `toCFG`: structural paths
provide temporary block names, while forgetting those names leaves a block
collection which is invariant under every choice of sibling ordering.
-/

namespace Isotope.TAC.Bridge.LambdaSSA

universe u

open Isotope.LambdaSSA

/-- A block together with the structural address assigned by a particular
ordered presentation of the dominator tree. -/
structure AddressedBlock (Φ : Type u) where
  address : Bridge.BlockAddress
  block : Block Φ

/-- A flat presentation has a distinguished nameless entry and named
non-entry blocks, just as the paper's classical CFG does. -/
structure FlatDomCFG (Φ : Type u) where
  entry : Block Φ
  blocks : List (AddressedBlock Φ)

namespace DomTree

/-- Preorder flattening below a structural address. -/
noncomputable def flattenAt (tree : DomTree Φ) :
    Bridge.BlockAddress → List (AddressedBlock Φ) :=
  DomTree.rec (motive := fun _ => Bridge.BlockAddress → List (AddressedBlock Φ))
    (fun entry arity _ recurse here =>
      ⟨here, entry⟩ ::
        (List.ofFn fun i : Fin arity =>
          recurse i (here ++ [i.val])).flatten) tree

/-- The paper's `toCFG`: retain the root as the nameless entry and flatten
all immediate-dominator subtrees into the ordinary block collection. -/
noncomputable def toFlatCFG : DomTree Φ → FlatDomCFG Φ
  | .node entry arity children =>
      { entry
        blocks := (List.ofFn fun i : Fin arity =>
          flattenAt (children i) [i.val]).flatten }

/-- Erase temporary structural block names.  This is the quotient observation
needed when sibling order (and hence structural addresses) is changed. -/
def forgetAddresses (cfg : FlatDomCFG Φ) : Block Φ × List (Block Φ) :=
  (cfg.entry, cfg.blocks.map AddressedBlock.block)

/-- Two explicit dominator trees differing only by independent permutations
of siblings.  Labels inside blocks are deliberately not rewritten here; the
relation records only the choice used to enumerate the tree. -/
inductive Reordered : DomTree Φ → DomTree Φ → Prop where
  | node (entry : Block Φ) (arity : Nat)
      (left right : Fin arity → DomTree Φ) (σ : Equiv.Perm (Fin arity))
      (children : ∀ i, Reordered (right i) (left (σ i))) :
      Reordered (.node entry arity left) (.node entry arity right)

@[simp] theorem Reordered.entry_eq {left right : DomTree Φ}
    (h : Reordered left right) : left.toFlatCFG.entry = right.toFlatCFG.entry := by
  cases h
  rfl

private theorem map_block_flattenAt_address (tree : DomTree Φ) (left right) :
    (tree.flattenAt left).map AddressedBlock.block =
      (tree.flattenAt right).map AddressedBlock.block := by
  induction tree generalizing left right with
  | node entry arity children ih =>
    simp only [flattenAt, List.map_cons, List.map_flatten]
    congr 1
    apply congrArg List.flatten
    simp only [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact ih i _ _

private theorem map_block_flattenAt (tree : DomTree Φ) (address) :
    (tree.flattenAt address).map AddressedBlock.block =
      tree.toFlatCFG.entry :: tree.toFlatCFG.blocks.map AddressedBlock.block := by
  cases tree with
  | node entry arity children =>
    simp only [flattenAt, toFlatCFG, List.map_cons, List.map_flatten]
    congr 1
    apply congrArg List.flatten
    simp only [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact map_block_flattenAt_address (children i) _ _

/-- Flattenings of reordered trees contain the same block payloads.  Their
lists may be permuted and their structural addresses may differ. -/
theorem Reordered.blocks_perm {left right : DomTree Φ}
    (h : Reordered left right) :
    List.Perm (left.toFlatCFG.blocks.map AddressedBlock.block)
      (right.toFlatCFG.blocks.map AddressedBlock.block) := by
  induction h with
  | node entry arity left right σ children ih =>
    simp only [toFlatCFG, List.map_flatten]
    let f : Fin arity → List (Block Φ) := fun i =>
      (flattenAt (left i) [i.val]).map AddressedBlock.block
    let g : Fin arity → List (Block Φ) := fun i =>
      (flattenAt (right i) [i.val]).map AddressedBlock.block
    simp only [List.map_ofFn]
    change List.Perm (List.ofFn f).flatten (List.ofFn g).flatten
    have hg : ∀ i, List.Perm (g i) (f (σ i)) := by
      intro i
      dsimp [f, g]
      rw [map_block_flattenAt, map_block_flattenAt]
      rw [Reordered.entry_eq (children i)]
      exact (ih i).cons _
    have hpoint : List.Perm (List.ofFn g).flatten
        (List.ofFn (f ∘ σ)).flatten := by
      apply List.Perm.flatten_congr
      rw [List.forall₂_iff_get]
      constructor
      · simp
      · intro i hi hj
        simpa using hg ⟨i, by simpa using hi⟩
    exact (hpoint.trans (σ.ofFn_comp_perm f).flatten).symm

/-- Consequently the classical, unaddressed CFG observation is independent
of the chosen ordering of every dominator-tree sibling family. -/
theorem Reordered.forgetAddresses_eqv {left right : DomTree Φ}
    (h : Reordered left right) :
    (forgetAddresses left.toFlatCFG).1 = (forgetAddresses right.toFlatCFG).1 ∧
      List.Perm (forgetAddresses left.toFlatCFG).2
        (forgetAddresses right.toFlatCFG).2 := by
  cases h with
  | node entry arity left right σ children =>
    exact ⟨rfl, Reordered.blocks_perm (.node entry arity left right σ children)⟩

/-- Connection to the existing address-level `FlatBBA` implementation: both
routes first reassemble the tree with `addDom`, then erase lexical `cfg`s. -/
def toFlatBBA (tree : DomTree Φ) : Bridge.FlatBBA Φ :=
  Bridge.LexicalBBA.flatten
    (Bridge.LexicalBBA.ofLambdaSSA tree.addDom)

@[simp] theorem toFlatBBA_eq_flatten_addDom (tree : DomTree Φ) :
    tree.toFlatBBA = Bridge.LexicalBBA.flatten
      (Bridge.LexicalBBA.ofLambdaSSA tree.addDom) := rfl

/-- The bridge also commutes for any proof-relevant lexical parse, rather than
merely for trees constructed independently. -/
@[simp] theorem Decomposition.toFlatBBA_addDom
    {region : Region Φ} (parsed : Decomposition region) :
    parsed.tree.toFlatBBA =
      Bridge.LexicalBBA.flatten (Bridge.LexicalBBA.ofLambdaSSA region) := by
  rw [toFlatBBA_eq_flatten_addDom, Decomposition.addDom_tree]

end DomTree
end Isotope.TAC.Bridge.LambdaSSA
