import Isotope.LambdaSSA.Structural
import Isotope.LambdaSSA.Semantics.Collective

/-! # Typed simultaneous reindexing of a lambda-SSA CFG binder -/

namespace Isotope.LambdaSSA

universe u v

variable {Φ : Type u} {τ : Type v}
variable [LambdaIter.TypeFormers τ] [LambdaIter.HasTy Φ τ]

namespace Region

@[simp] theorem renameLabels_id (region : Region Φ) :
    region.renameLabels id = region := by
  induction region with
  | br => rfl
  | case discr left right ihl ihr => simp [renameLabels, ihl, ihr]
  | let₁ value body ih => simp [renameLabels, ih]
  | let₂ value body ih => simp [renameLabels, ih]
  | cfg entry arity blocks ihe ihb =>
      simp [renameLabels, ihe]
      funext i
      exact ihb i

/-- Data for a simultaneous permutation of one `cfg` binder.  The label
renaming is explicit because it must act on the entry and on every child,
while the same permutation acts contravariantly on the child family.  Keeping
the typed renaming as data supports heterogeneous block-argument types. -/
structure CfgReindexing {n : Nat} (R R' : Fin n → τ) (L : LCtx τ) where
  permutation : Equiv.Perm (Fin n)
  rename : Nat → Nat
  types : R' = R ∘ permutation
  onLocal (i : Fin n) : rename i = (permutation.symm i).val
  onExternal (i : Nat) : rename (n + i) = n + i
  labels : Ren (List.ofFn R ++ L) (List.ofFn R' ++ L) rename

namespace CfgReindexing

/-- Reindex the complete body of a CFG binder.  Branch occurrences and block
definitions move together; this is the operation absent from raw
`DomTree.Reordered`. -/
def apply {n : Nat} {R R' : Fin n → τ} {L : LCtx τ}
    (p : CfgReindexing R R' L) (entry : Region Φ)
    (blocks : Fin n → Region Φ) : Region Φ :=
  .cfg (entry.renameLabels p.rename) n
    (fun i => (blocks (p.permutation i)).renameLabels p.rename)

/-- Simultaneous CFG reindexing preserves exact typing, including
heterogeneous block parameter types. -/
theorem hasType {n : Nat} {R R' : Fin n → τ} {Γ : VCtx τ} {L : LCtx τ}
    (p : CfgReindexing R R' L)
    {entry : Region Φ} {blocks : Fin n → Region Φ}
    (he : Region.HasType Γ entry (List.ofFn R ++ L))
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    Region.HasType Γ (p.apply entry blocks) L := by
  apply Region.HasType.cfg R'
  · exact he.renameLabels p.labels
  · intro i
    have hi := (hb (p.permutation i)).renameLabels p.labels
    have htype : R' i = R (p.permutation i) := by
      simpa [Function.comp_apply] using congrFun p.types i
    simpa [htype] using hi

/-- The identity reindexing is definitionally the original CFG up to the
already-proved identity label renaming laws. -/
def identity {n : Nat} (R : Fin n → τ) (L : LCtx τ) : CfgReindexing R R L where
  permutation := Equiv.refl _
  rename := id
  types := rfl
  onLocal := fun _ => rfl
  onExternal := fun _ => rfl
  labels := Ren.id _

@[simp] theorem apply_identity {n : Nat} (R : Fin n → τ) (L : LCtx τ)
    (entry : Region Φ) (blocks : Fin n → Region Φ) :
    (identity R L).apply entry blocks = .cfg entry n blocks := by
  simp [apply, identity]

end CfgReindexing
end Region

namespace Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open LambdaIter.Subtyping.Semantics.Categorical

variable {V : Type u} [Category V] [CartesianMonoidalCategory V]
variable [LambdaIter.Subtyping τ]
variable [HasFiniteCoproducts V] (M : TypeModel τ V)

/-- Reindexing isomorphism for the finite coproduct of locally bound labels. -/
noncomputable def finiteLabelPermIso {n : Nat} {R R' : Fin n → τ} {L : LCtx τ}
    (p : Region.CfgReindexing R R' L) :
    finiteLabelObj M R ≅ finiteLabelObj M R' := by
  exact Limits.Sigma.whiskerEquiv p.permutation.symm
    (fun j => eqToIso (congrArg M.obj (by
      simpa [Function.comp_apply] using congrFun p.types (p.permutation.symm j))))

/-- The finite-label permutation sends each old injection to the corresponding
new injection. -/
@[reassoc]
theorem finiteLabelInject_perm {n : Nat} {R R' : Fin n → τ} {L : LCtx τ}
    (p : Region.CfgReindexing R R' L) (i : Fin n) :
    finiteLabelInject M R i ≫ (finiteLabelPermIso M p).hom =
      eqToHom (congrArg M.obj (by
        simpa [Function.comp_apply] using
          (congrFun p.types (p.permutation.symm i)).symm)) ≫
        finiteLabelInject M R' (p.permutation.symm i) := by
  unfold finiteLabelInject finiteLabelPermIso
  rw [Limits.Sigma.whiskerEquiv_hom]
  apply Limits.Sigma.ι_comp_map'

end Semantics.Categorical
end Isotope.LambdaSSA
