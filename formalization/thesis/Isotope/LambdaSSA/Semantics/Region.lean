import Isotope.LambdaSSA.Semantics.Label
import Isotope.LambdaSSA.Semantics.Inversion

/-! # Relational categorical semantics of lambda-SSA regions

This module gives the paper's equations for branches, case regions, and
straight-line bindings.  The relation is indexed by the existing extrinsic
typing derivation, just as the term semantics is.
-/

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Isotope.LambdaSSA.Semantics.Categorical

set_option autoImplicit true
set_option relaxedAutoImplicit true

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.PremonoidalCategory
open Isotope.LambdaIter.Subtyping.Semantics.Categorical
open scoped MonoidalCategory

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
  (M : TypeModel τ V)
  {Φ : Type u₄} [LambdaIter.HasTy Φ τ] [InstructionModel J M Φ]

/-- Separate external from locally bound labels in an appended label context.
The local labels occur first because label contexts use de Bruijn order. -/
noncomputable def labelAppendSplit (R L : LCtx τ) :
    labelObj M (R ++ L) ⟶ labelObj M L ⨿ labelObj M R := by
  apply Limits.Sigma.desc
  intro i
  by_cases hi : i.val < R.length
  · exact labelInject M i.val (by
      simp only [At, List.getElem?_eq_getElem, List.length_append]
      simp [hi]) ≫ coprod.inr
  · let j := i.val - R.length
    exact labelInject M j (by
      change L[j]? = some (R ++ L)[i.val]
      have ht : (R ++ L)[i.val]? = some (R ++ L)[i.val] := by simp
      rw [List.getElem?_append_right (by omega)] at ht
      simpa [j] using ht) ≫ coprod.inl

/-- A collective block arrow is characterized by its restriction to every
local-label summand, with the read-only SSA context carried on the left. -/
structure CollectiveDenotes (Γ : VCtx τ) {n : Nat} (R : Fin n → τ) (L : LCtx τ)
    (block : ∀ i, J.obj (ctxObj M (R i :: Γ)) ⟶
      J.obj (labelObj M (List.ofFn R ++ L)))
    (f : J.obj (ctxObj M Γ ⊗ labelObj M (List.ofFn R)) ⟶
      J.obj (labelObj M (List.ofFn R ++ L))) : Prop where
  restrict (i : Fin n) :
    J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ labelInject M i.val (by
      simp [At, i.isLt])) ≫ f = block i

/-- Structural denotation graph for the non-recursive region constructors.
The absence of a `cfg` constructor is intentional: recursive CFG wiring is a
separate Elgot construction, whereas these rules require only a distributive
Freyd category. -/
inductive RegionDenotes : {Γ : VCtx τ} → {r : Region Φ} → {L : LCtx τ} →
    Region.HasType Γ r L → (J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)) → Prop where
  | br (dt : Denotes J M ha fa) :
      RegionDenotes (.br h ha) (fa ≫ J.map (labelInject M _ h))
  | case (de : Denotes J M he fe)
      (dl : RegionDenotes hl fl) (dr : RegionDenotes hr fr) :
      RegionDenotes (.case he hl hr)
        (caseWithContext J (fe ≫ J.map (M.coprodIso _ _).hom) fl fr)
  | let₁ (da : Denotes J M ha fa) (db : RegionDenotes hb fb) :
      RegionDenotes (.let₁ ha hb) (bind J fa fb)
  | let₂ (da : Denotes J M ha fa) (db : RegionDenotes hb fb) :
      RegionDenotes (.let₂ ha hb) (bind J fa (
        J.map ((𝟙 _) ⊗ₘ (M.tensorIso _ _).hom) ≫
          J.map (ctxPairIso M _ _ _).hom ≫ fb))
  | cfg {n : Nat} {R : Fin n → τ} {Γ : VCtx τ} {L : LCtx τ}
      {entry : Region Φ} {blocks : Fin n → Region Φ}
      (he : Region.HasType Γ entry (List.ofFn R ++ L))
      (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L))
      {fe : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (List.ofFn R ++ L))}
      {fb : ∀ i, J.obj (ctxObj M (R i :: Γ)) ⟶
        J.obj (labelObj M (List.ofFn R ++ L))}
      {collective : J.obj (ctxObj M Γ ⊗ labelObj M (List.ofFn R)) ⟶
        J.obj (labelObj M (List.ofFn R ++ L))}
      (de : RegionDenotes he fe)
      (db : ∀ i, RegionDenotes (hb i) (fb i))
      (dc : CollectiveDenotes J M Γ R L fb collective) :
      RegionDenotes (.cfg R he hb) (bind J
        (fe ≫ J.map (labelAppendSplit M (List.ofFn R) L)) (
          J.map (DistributiveTensor.leftIso (ctxObj M Γ)
            (labelObj M L) (labelObj M (List.ofFn R))).inv ≫
          splitMapCoprod J _ _ ≫ coprod.desc
            (J.map (CartesianMonoidalCategory.snd _ _))
            (contextualLoop J
              (collective ≫ J.map (labelAppendSplit M (List.ofFn R) L)))))

/-- Transport the graph across proof-irrelevant region typing evidence. -/
theorem RegionDenotes.proof_irrel
    {Γ : VCtx τ} {r : Region Φ} {L : LCtx τ}
    {h h' : Region.HasType Γ r L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M h f) : RegionDenotes J M h' f := by
  rw [Subsingleton.elim h' h]
  exact d

/-- Optional coherence for the relational region semantics. -/
class RegionTypingCoherent : Prop where
  denotes_eq {Γ : VCtx τ} {r : Region Φ} {L : LCtx τ}
      {h : Region.HasType Γ r L}
      {f g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)} :
      RegionDenotes J M h f → RegionDenotes J M h g → f = g

end Isotope.LambdaSSA.Semantics.Categorical
