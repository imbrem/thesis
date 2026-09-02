import Isotope.LambdaIter.Subtyping.Semantics.Effects

/-!
# The two-point effect model of a Freyd category

Every strict Freyd category carries a canonical effect lattice over `Bool`: `⊥` is the image of
`J` — the value morphisms — and `⊤` is everything.  This file checks that it satisfies all the
laws of an effect model, so that the effect-soundness theorems apply to *any* strict Freyd
category with no further hypotheses.  Concrete models are then obtained simply by exhibiting a
Freyd category, which `Isotope.CategoryTheory.Monad.Effectful` does for Kleisli categories.
-/

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Isotope.LambdaIter.Subtyping.Semantics.Categorical

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.PremonoidalCategory
open CategoryTheory.EffectfulFreydCategory (twoPoint twoPoint_monotone)
open Functor.IsStrictPremonoidal
open scoped MonoidalCategory

section Base

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  (J : Functor V C) [FreydCategory J] [Functor.IsStrictPremonoidal J]

/-- The coherence isomorphism of a strict Freyd inclusion has an `eqToHom` inverse. -/
theorem tensorIso_inv_eq (X Y : V) :
    (Functor.StrongPremonoidal.tensorIso (J := J) X Y).inv =
      eqToHom (obj_tensor (J := J) X Y) := by
  have h : (Functor.StrongPremonoidal.tensorIso (J := J) X Y).hom ≫
      eqToHom (obj_tensor (J := J) X Y) = 𝟙 _ := by
    rw [tensorIso_hom]; simp
  have h' := congrArg (fun k : J.obj X ⊗ J.obj Y ⟶ J.obj X ⊗ J.obj Y =>
    (Functor.StrongPremonoidal.tensorIso (J := J) X Y).inv ≫ k) h
  simpa using h'.symm

/-- The two-point effect lattice: `⊥` is the image of `J`, `⊤` is all of `C`. -/
instance twoPointImageEffectLattice : EffectLattice Bool (twoPoint J.imageProperty) where
  eff_mono := twoPoint_monotone _
  eff_subcategory e := by
    cases e
    · exact inferInstanceAs (IsSymmetricSubcategory J.imageProperty)
    · exact inferInstanceAs (IsSymmetricSubcategory (⊤ : MorphismProperty C))

instance twoPointImageEffectModel : EffectModel Bool J (twoPoint J.imageProperty) where
  map_mem f := J.imageProperty_map f
  tensorIso_hom_mem X Y := by
    rw [tensorIso_hom]; exact FreydCategory.mem_eqToHom J _
  tensorIso_inv_mem X Y := by
    rw [tensorIso_inv_eq]; exact FreydCategory.mem_eqToHom J _

end Base

section Distributive

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : Functor V C) [DistributiveFreydCategory J] [Functor.IsStrictPremonoidal J]

/-- Splitting a mapped coproduct and then copairing two *value* morphisms is again the image of
a value morphism.  Neither factor is; only this composite is independent of which colimit cocone
Mathlib happens to have chosen. -/
theorem splitMapCoprod_desc_map {A B D : V} (l : A ⟶ D) (r : B ⟶ D) :
    splitMapCoprod J A B ≫ coprod.desc (J.map l) (J.map r) = J.map (coprod.desc l r) := by
  rw [splitMapCoprod, IsIso.inv_comp_eq]
  refine coprod.hom_ext ?_ ?_
  · rw [← Category.assoc, coprodComparison_inl, ← J.map_comp, coprod.inl_desc, coprod.inl_desc]
  · rw [← Category.assoc, coprodComparison_inr, ← J.map_comp, coprod.inr_desc, coprod.inr_desc]

instance twoPointImageDistributiveEffectModel :
    DistributiveEffectModel Bool J (twoPoint J.imageProperty) where
  splitDesc_mem := by
    intro e A B D l r hl hr
    cases e
    · obtain ⟨A₁, D₁, hA, hD, l', rfl⟩ := hl
      obtain ⟨B₁, D₂, hB, hD', r', rfl⟩ := hr
      obtain rfl := FreydCategory.obj_injective J hA
      obtain rfl := FreydCategory.obj_injective J hB
      obtain rfl := FreydCategory.obj_injective J (hD.trans hD'.symm)
      have hl' : eqToHom hA.symm ≫ J.map l' ≫ eqToHom hD = J.map l' ≫ eqToHom hD := by simp
      have hr' : eqToHom hB.symm ≫ J.map r' ≫ eqToHom hD' = J.map r' ≫ eqToHom hD := by simp
      rw [hl', hr', ← coprod.desc_comp, ← Category.assoc, splitMapCoprod_desc_map]
      exact FreydCategory.mem_comp J (J.imageProperty_map _) (FreydCategory.mem_eqToHom J _)
    · trivial

instance twoPointImageIterativeEffects [Iteration C] :
    IterativeEffects Bool J (twoPoint J.imageProperty) (fun b => b = true) where
  iterate_mem := by
    rintro (_ | _) he A B f hf
    · exact absurd he (by simp)
    · trivial

end Distributive

end Isotope.LambdaIter.Subtyping.Semantics.Categorical
