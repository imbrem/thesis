import Isotope.LambdaSSA.Structural

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
  labels := Ren.id _

@[simp] theorem apply_identity {n : Nat} (R : Fin n → τ) (L : LCtx τ)
    (entry : Region Φ) (blocks : Fin n → Region Φ) :
    (identity R L).apply entry blocks = .cfg entry n blocks := by
  simp [apply, identity]

end CfgReindexing
end Region
end Isotope.LambdaSSA
