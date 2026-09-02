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
  (J : Functor V C) [DistributiveFreydCategory J]
  {τ : Type u₃} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
  (M : TypeModel τ V)
  {Φ : Type u₄} [LambdaIter.HasTy Φ τ] [InstructionModel J M Φ]

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
