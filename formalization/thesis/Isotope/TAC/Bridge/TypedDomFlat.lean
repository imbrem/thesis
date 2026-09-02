import Isotope.TAC.Bridge.DomFlat
import Isotope.LambdaSSA.Typing

/-! # Typed flat/dominator-tree correspondence -/

namespace Isotope.TAC.Bridge.LambdaSSA

open Isotope.LambdaSSA

universe u v

variable {Phi : Type u} {Ty : Type v}
variable [LambdaIter.TypeFormers Ty] [LambdaIter.HasTy Phi Ty]

namespace DomTree

/-- Typing of an explicit lexical dominator tree. Each child is checked with
its block parameter in scope, while the mutually recursive family is in scope
in the root terminator and every child. -/
inductive HasType : VCtx Ty -> DomTree Phi -> LCtx Ty -> Prop where
  | node {Gamma Delta : VCtx Ty} {L : LCtx Ty} {entry : Block Phi}
      {arity : Nat} {children : Fin arity -> DomTree Phi}
      (R : Fin arity -> Ty)
      (body : Body.HasType Gamma entry.body Delta)
      (terminator : Terminator.HasType Delta entry.terminator (List.ofFn R ++ L))
      (childrenTyped : forall i, HasType (R i :: Delta) (children i) (List.ofFn R ++ L)) :
      HasType Gamma (.node entry arity children) L

private theorem terminatorRegion_hasType
    {Gamma : VCtx Ty} {term : Terminator Phi} {L : LCtx Ty}
    (h : Terminator.HasType Gamma term L) :
    Region.HasType Gamma (terminatorRegion term) L := by
  induction h with
  | br hl ha => exact .br hl ha
  | case ha hl hr ihl ihr => exact .case ha ihl ihr

private theorem hasType_terminatorRegion
    {Gamma : VCtx Ty} {term : Terminator Phi} {L : LCtx Ty}
    (h : Region.HasType Gamma (terminatorRegion term) L) :
    Terminator.HasType Gamma term L := by
  induction term generalizing Gamma with
  | br label arg =>
      simp only [terminatorRegion] at h
      cases h with
      | br hl ha => exact .br hl ha
  | case discr left right ihl ihr =>
      simp only [terminatorRegion] at h
      cases h with
      | case ha hl hr => exact .case ha (ihl hl) (ihr hr)

private theorem wrapBody_hasType
    {Gamma Delta : VCtx Ty} {body : Body Phi} {region : Region Phi} {L : LCtx Ty}
    (hb : Body.HasType Gamma body Delta) (hr : Region.HasType Delta region L) :
    Region.HasType Gamma (wrapBody body region) L := by
  induction hb with
  | nil => exact hr
  | let₁ ha _ ih => exact .let₁ ha (ih hr)
  | let₂ ha _ ih => exact .let₂ ha (ih hr)

private theorem hasType_wrapBody
    {Gamma : VCtx Ty} {body : Body Phi} {region : Region Phi} {L : LCtx Ty}
    (h : Region.HasType Gamma (wrapBody body region) L) :
    exists Delta, Body.HasType Gamma body Delta /\ Region.HasType Delta region L := by
  induction body generalizing Gamma with
  | nil => exact ⟨Gamma, .nil, h⟩
  | let₁ value rest ih =>
      simp only [wrapBody] at h
      cases h with
      | let₁ ha hr =>
          rcases ih hr with ⟨Delta, hb, ht⟩
          exact ⟨Delta, .let₁ ha hb, ht⟩
  | let₂ value rest ih =>
      simp only [wrapBody] at h
      cases h with
      | let₂ ha hr =>
          rcases ih hr with ⟨Delta, hb, ht⟩
          exact ⟨Delta, .let₂ ha hb, ht⟩

/-- A typed chosen dominator tree reassembles to a typed lambda-SSA region. -/
theorem addDom_hasType {Gamma : VCtx Ty} {tree : DomTree Phi} {L : LCtx Ty}
    (h : HasType Gamma tree L) : Region.HasType Gamma tree.addDom L := by
  induction h with
  | node R hb ht hc ih =>
      apply wrapBody_hasType hb
      exact .cfg R (terminatorRegion_hasType ht) ih

/-- Typing of a reassembled lexical region determines typing of its explicit
dominator tree. -/
theorem hasType_addDom {Gamma : VCtx Ty} {tree : DomTree Phi} {L : LCtx Ty}
    (h : Region.HasType Gamma tree.addDom L) : HasType Gamma tree L := by
  induction tree generalizing Gamma L with
  | node entry arity children ih =>
      simp only [addDom] at h
      rcases hasType_wrapBody h with ⟨Delta, hb, hcfg⟩
      cases hcfg with
      | cfg R hentry hchildren =>
          exact .node R hb (hasType_terminatorRegion hentry)
            (fun i => ih i (hchildren i))

theorem hasType_addDom_iff {Gamma : VCtx Ty} {tree : DomTree Phi} {L : LCtx Ty} :
    Region.HasType Gamma tree.addDom L <-> HasType Gamma tree L :=
  ⟨hasType_addDom, addDom_hasType⟩

end DomTree

/-- A flat CFG together with the explicit dominator-tree choice which realizes
its structural addresses. -/
structure DominanceWellFormedFlat (Phi : Type u) where
  cfg : FlatDomCFG Phi
  tree : DomTree Phi
  realizes : tree.toFlatCFG = cfg

namespace DominanceWellFormedFlat

def toLambdaSSA (flat : DominanceWellFormedFlat Phi) : Region Phi := flat.tree.addDom

noncomputable def ofDomTree (tree : DomTree Phi) : DominanceWellFormedFlat Phi :=
  ⟨tree.toFlatCFG, tree, rfl⟩

@[simp] theorem toLambdaSSA_ofDomTree (tree : DomTree Phi) :
    (ofDomTree tree).toLambdaSSA = tree.addDom := rfl

/-- A dominance-well-formed flat presentation plus its choice is exactly an
explicit lexical dominator tree. -/
noncomputable def domTreeEquiv : DominanceWellFormedFlat Phi ≃ DomTree Phi where
  toFun := fun flat => flat.tree
  invFun := ofDomTree
  left_inv := by
    intro flat
    cases flat with
    | mk cfg tree realizes => cases realizes; rfl
  right_inv := fun tree => rfl

theorem hasType_toLambdaSSA_iff (flat : DominanceWellFormedFlat Phi)
    {Gamma : VCtx Ty} {L : LCtx Ty} :
    Region.HasType Gamma flat.toLambdaSSA L <-> DomTree.HasType Gamma flat.tree L :=
  DomTree.hasType_addDom_iff

/-- Sibling-order choices are explicitly forgotten only modulo block
permutation, matching the paper's equational-theory boundary. -/
theorem forget_eqv_of_reordered
    {left right : DominanceWellFormedFlat Phi}
    (h : DomTree.Reordered left.tree right.tree) :
    (DomTree.forgetAddresses left.cfg).1 = (DomTree.forgetAddresses right.cfg).1 /\
      List.Perm (DomTree.forgetAddresses left.cfg).2
        (DomTree.forgetAddresses right.cfg).2 := by
  rw [<- left.realizes, <- right.realizes]
  exact h.forgetAddresses_eqv

end DominanceWellFormedFlat
end Isotope.TAC.Bridge.LambdaSSA
