import Isotope.LambdaIter.Subtyping.LocallyNameless.TypingSubst
import Isotope.LambdaIter.Subtyping.Semantics.Freyd.Empty

/-!
# Structural axioms in an arbitrary Freyd category

The beta/eta schemes of `LambdaIter.LocallyNameless.StructuralAxiom` that do
not involve substitution or weakening are discharged here, for the categorical
denotation, in an arbitrary strong Elgot Freyd category.  Each theorem is
stated for the *constructed* derivations of the two endpoints, exactly as the
monadic `Subtyping.Semantics.sound_*` lemmas are; connecting them to arbitrary
endpoint derivations is the separate job of typing coherence.

Covered: `letEta`, `unitEta`, `caseBetaL`, `caseBetaR`, `caseEta` and
`emptyInitial` — six of the nine structural schemes.  `letBeta` and `pairBeta`
need the categorical substitution and weakening lemmas, which this directory
does not yet provide.  `pairEta` needs neither, and reduces to the single
cartesian identity

    envPairHom M Γ β A B ≫ lift (boundVar M 1) (boundVar M 0) =
      snd (envObj M Γ β) (M.obj A ⊗ M.obj B)

together with `bind_map_snd` and `pair_map_map` (both proved in
`Freyd/Combinators.lean`); it is left open only because that identity resisted
`simp`, `cat_disch` and a hand-written associator chase in this instance
setting.
-/

universe v₁ v₂ u₁ u₂ u₃ u₄ u₅

namespace Isotope.LambdaIter.Subtyping.Semantics.Categorical

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  [Functor.StrongPremonoidalCentral J]
  {τ : Type u₃} [TypeFormers τ] [Subtyping τ] (M : TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type u₅} [HasTy Φ τ] [InstructionModel J M Φ]

/-- A bound variable denotes the corresponding environment projection. -/
theorem denote_bv {Γ : Ctx ν τ} {n : Nat}
    {β : LocallyNameless.BoundCtx τ n} {ι : Fin n} :
    denote J M (LocallyNameless.HasType.bv (Φ := Φ) (Γ := Γ) (β := β) (ι := ι)) =
      J.map (boundVar M ι) := by
  rw [denote]

/-- The newest bound variable denotes the second projection of the extended
environment. -/
theorem denote_newest {Γ : Ctx ν τ} {n : Nat}
    {β : LocallyNameless.BoundCtx τ n} {A : τ} :
    denote J M (LocallyNameless.HasType.newest (Φ := Φ) (Γ := Γ) (β := β) (A := A)) =
      J.map (boundVar M (0 : Fin (n + 1))) := denote_bv J M

/-- The previous bound variable denotes the appropriate projection. -/
theorem denote_previous {Γ : Ctx ν τ} {n : Nat}
    {β : LocallyNameless.BoundCtx τ n} {A B : τ} :
    denote J M
        (LocallyNameless.HasType.previous (Φ := Φ) (Γ := Γ) (β := β) (A := A) (B := B)) =
      J.map (boundVar M (1 : Fin (n + 2))) := denote_bv J M

/-- Bound lookup at the newest slot. -/
theorem boundLookup_zero {n : Nat} (β : LocallyNameless.BoundCtx τ n) (A : τ) :
    boundLookup M (β := .snoc β A) (0 : Fin (n + 1)) =
      (CartesianMonoidalCategory.snd (boundObj M β) (M.obj A) :
        boundObj M (.snoc β A) ⟶ M.obj A) := by
  rfl

/-- Bound lookup at the slot below the newest. -/
theorem boundLookup_one {n : Nat} (β : LocallyNameless.BoundCtx τ n) (A B : τ) :
    boundLookup M (β := .snoc (.snoc β A) B) (1 : Fin (n + 2)) =
      (CartesianMonoidalCategory.fst (boundObj M β ⊗ M.obj A) (M.obj B) ≫
        CartesianMonoidalCategory.snd (boundObj M β) (M.obj A) :
          boundObj M (.snoc (.snoc β A) B) ⟶ M.obj A) := by
  rfl

/-- Extending the environment and then reading the newest slot is the second
projection. -/
theorem envSnocIso_comp_boundVar_zero (Γ : Ctx ν τ) {n : Nat}
    (β : LocallyNameless.BoundCtx τ n) (A : τ) :
    (envSnocIso M Γ β A).hom ≫ boundVar M (0 : Fin (n + 1)) =
      CartesianMonoidalCategory.snd (envObj M Γ β) (M.obj A) := by
  simp only [envSnocIso, boundVar, boundLookup_zero, envObj, boundObj]
  exact CartesianMonoidalCategory.associator_hom_snd_snd _ _ _

/-- The image of the newest-slot lookup, in the form used by every `let`-like
denotation clause. -/
theorem map_envSnocIso_comp_denote_newest {Γ : Ctx ν τ} {n : Nat}
    {β : LocallyNameless.BoundCtx τ n} {A : τ} :
    J.map (envSnocIso M Γ β A).hom ≫
        denote J M (LocallyNameless.HasType.newest (Φ := Φ) (Γ := Γ) (β := β) (A := A)) =
      J.map (CartesianMonoidalCategory.snd (envObj M Γ β) (M.obj A)) := by
  rw [denote_newest]
  exact (J.map_comp _ _).symm.trans
    (congrArg J.map (envSnocIso_comp_boundVar_zero M Γ β A))

/-- **`let` eta.** -/
theorem sound_letEta {Γ : Ctx ν τ} {n : Nat} {β : LocallyNameless.BoundCtx τ n}
    {a : LocallyNameless.Tm ν Φ n} {A : τ}
    (ha : LocallyNameless.HasType Φ Γ β a A) :
    denote J M (.let₁ ha LocallyNameless.HasType.newest) = denote J M ha := by
  rw [denote, map_envSnocIso_comp_denote_newest]
  exact bind_map_snd J (denote J M ha)

/-- **Unit eta.** -/
theorem sound_unitEta {Γ : Ctx ν τ} {n : Nat} {β : LocallyNameless.BoundCtx τ n}
    {a : LocallyNameless.Tm ν Φ n}
    (ha : LocallyNameless.HasType Φ Γ β a (TypeFormers.unit : τ)) :
    denote J M (.let₁ ha LocallyNameless.HasType.unit) = denote J M ha := by
  have hval : (envSnocIso M Γ β (TypeFormers.unit : τ)).hom ≫
      (CartesianMonoidalCategory.toUnit
        (envObj M Γ (LocallyNameless.BoundCtx.snoc β (TypeFormers.unit : τ))) ≫
          M.unitIso.inv) =
      CartesianMonoidalCategory.snd (envObj M Γ β) (M.obj (TypeFormers.unit : τ)) := by
    rw [← Category.assoc, Iso.comp_inv_eq]
    apply CartesianMonoidalCategory.toUnit_unique
  have hunit : J.map (envSnocIso M Γ β (TypeFormers.unit : τ)).hom ≫
      denote J M (LocallyNameless.HasType.unit (Φ := Φ) (Γ := Γ)
        (β := LocallyNameless.BoundCtx.snoc β (TypeFormers.unit : τ))) =
      J.map (CartesianMonoidalCategory.snd (envObj M Γ β)
        (M.obj (TypeFormers.unit : τ))) := by
    rw [denote]
    exact (J.map_comp _ _).symm.trans (congrArg J.map hval)
  rw [denote, hunit]
  exact bind_map_snd J (denote J M ha)

/-- **Left case beta.** -/
theorem sound_caseBetaL {Γ : Ctx ν τ} {n : Nat} {β : LocallyNameless.BoundCtx τ n}
    {e : LocallyNameless.Tm ν Φ n} {l r : LocallyNameless.Tm ν Φ (n + 1)} {A B D : τ}
    (he : LocallyNameless.HasType Φ Γ β e A)
    (hl : LocallyNameless.HasType Φ Γ (.snoc β A) l D)
    (hr : LocallyNameless.HasType Φ Γ (.snoc β B) r D) :
    denote J M (.case (.inl he (B := B)) hl hr) = denote J M (.let₁ he hl) := by
  have hs : denote J M (LocallyNameless.HasType.inl he (B := B)) ≫
      J.map (M.coprodIso A B).hom =
        denote J M he ≫ J.map (coprod.inl : M.obj A ⟶ M.obj A ⨿ M.obj B) := by
    rw [denote, Category.assoc, ← Functor.map_comp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  rw [denote, denote, hs, caseWithContext_map_inl]

/-- **Right case beta.** -/
theorem sound_caseBetaR {Γ : Ctx ν τ} {n : Nat} {β : LocallyNameless.BoundCtx τ n}
    {e : LocallyNameless.Tm ν Φ n} {l r : LocallyNameless.Tm ν Φ (n + 1)} {A B D : τ}
    (he : LocallyNameless.HasType Φ Γ β e B)
    (hl : LocallyNameless.HasType Φ Γ (.snoc β A) l D)
    (hr : LocallyNameless.HasType Φ Γ (.snoc β B) r D) :
    denote J M (.case (.inr he (A := A)) hl hr) = denote J M (.let₁ he hr) := by
  have hs : denote J M (LocallyNameless.HasType.inr he (A := A)) ≫
      J.map (M.coprodIso A B).hom =
        denote J M he ≫ J.map (coprod.inr : M.obj B ⟶ M.obj A ⨿ M.obj B) := by
    rw [denote, Category.assoc, ← Functor.map_comp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  rw [denote, denote, hs, caseWithContext_map_inr]

/-- The left branch of the case eta rule denotes a value morphism. -/
theorem branch_inl_newest {Γ : Ctx ν τ} {n : Nat}
    {β : LocallyNameless.BoundCtx τ n} {A B : τ} :
    J.map (envSnocIso M Γ β A).hom ≫
        denote J M (LocallyNameless.HasType.inl
          (LocallyNameless.HasType.newest (Φ := Φ) (Γ := Γ) (β := β) (A := A)) (B := B)) =
      J.map (CartesianMonoidalCategory.snd (envObj M Γ β) (M.obj A) ≫
        (coprod.inl : M.obj A ⟶ M.obj A ⨿ M.obj B)) ≫ J.map (M.coprodIso A B).inv := by
  rw [denote, ← Category.assoc, map_envSnocIso_comp_denote_newest]
  exact ((J.map_comp _ _).symm.trans
    (congrArg J.map (Category.assoc _ _ _).symm)).trans (J.map_comp _ _)

/-- The right branch of the case eta rule denotes a value morphism. -/
theorem branch_inr_newest {Γ : Ctx ν τ} {n : Nat}
    {β : LocallyNameless.BoundCtx τ n} {A B : τ} :
    J.map (envSnocIso M Γ β B).hom ≫
        denote J M (LocallyNameless.HasType.inr
          (LocallyNameless.HasType.newest (Φ := Φ) (Γ := Γ) (β := β) (A := B)) (A := A)) =
      J.map (CartesianMonoidalCategory.snd (envObj M Γ β) (M.obj B) ≫
        (coprod.inr : M.obj B ⟶ M.obj A ⨿ M.obj B)) ≫ J.map (M.coprodIso A B).inv := by
  rw [denote, ← Category.assoc, map_envSnocIso_comp_denote_newest]
  exact ((J.map_comp _ _).symm.trans
    (congrArg J.map (Category.assoc _ _ _).symm)).trans (J.map_comp _ _)

/-- **Case eta.** -/
theorem sound_caseEta {Γ : Ctx ν τ} {n : Nat} {β : LocallyNameless.BoundCtx τ n}
    {e : LocallyNameless.Tm ν Φ n} {A B : τ}
    (he : LocallyNameless.HasType Φ Γ β e (TypeFormers.coprod A B)) :
    denote J M
        (.case he (.inl LocallyNameless.HasType.newest)
          (.inr LocallyNameless.HasType.newest)) = denote J M he := by
  rw [denote, branch_inl_newest, branch_inr_newest]
  refine Eq.trans (Eq.symm (caseWithContext_comp J
    (denote J M he ≫ J.map (M.coprodIso A B).hom)
    (J.map (CartesianMonoidalCategory.snd (envObj M Γ β) (M.obj A) ≫
      (coprod.inl : M.obj A ⟶ M.obj A ⨿ M.obj B)))
    (J.map (CartesianMonoidalCategory.snd (envObj M Γ β) (M.obj B) ≫
      (coprod.inr : M.obj B ⟶ M.obj A ⨿ M.obj B)))
    (J.map (M.coprodIso A B).inv))) ?_
  refine Eq.trans (congrArg (fun q => q ≫ J.map (M.coprodIso A B).inv)
    (caseWithContext_eta J (denote J M he ≫ J.map (M.coprodIso A B).hom))) ?_
  show (denote J M he ≫ J.map (M.coprodIso A B).hom) ≫ J.map (M.coprodIso A B).inv =
    denote J M he
  rw [Category.assoc, ← J.map_comp, Iso.hom_inv_id, J.map_id, Category.comp_id]

/-- **Empty initiality.**  Once an empty-typed computation has run, both the
continuation and the type at which `abort` was used are irrelevant. -/
theorem sound_emptyInitial [TensorEmptyStrict M] {Γ : Ctx ν τ} {n : Nat}
    {β : LocallyNameless.BoundCtx τ n} {z : LocallyNameless.Tm ν Φ n}
    {b c : LocallyNameless.Tm ν Φ (n + 1)} {A A' D : τ}
    (hz : LocallyNameless.HasType Φ Γ β z (TypeFormers.empty : τ))
    (hb : LocallyNameless.HasType Φ Γ (.snoc β A) b D)
    (hc : LocallyNameless.HasType Φ Γ (.snoc β A') c D) :
    denote J M (.let₁ (LocallyNameless.HasType.abort hz (C := A)) hb) =
      denote J M (.let₁ (LocallyNameless.HasType.abort hz (C := A')) hc) := by
  rw [denote, denote, denote, denote, abort, abort, bind, bind,
    extend_comp_map, extend_comp_map, Category.assoc, Category.assoc]
  congr 1
  exact computationTensorEmptyIsInitial J M (envObj M Γ β) _ _

end Isotope.LambdaIter.Subtyping.Semantics.Categorical
