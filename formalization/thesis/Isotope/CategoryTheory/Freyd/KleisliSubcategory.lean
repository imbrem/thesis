import Isotope.CategoryTheory.AddMonoidal.Kleisli
import Isotope.CategoryTheory.Freyd.SubcategoryElgot
import Isotope.CategoryTheory.Freyd.EffectfulElgot

/-!
# A concrete model of the subcategory presentation

The subcategory presentation of a Freyd category takes the value category to be a wide
subcategory `C_⊥ ⊆ C` of *pure* morphisms rather than a separate category.  This file exhibits
its first concrete model: the Kleisli category of a strong Elgot monad on `Type u`, with `C_⊥`
the image of the Kleisli inclusion — the *value* morphisms `f ≫ η`.

Everything the presentation asks for is checked here of the chosen coproduct structure of
`Kleisli (TM m)`, which is `Sum` on the nose:

* `IsCocartesianSubcategory` — the injections are `pure ∘ Sum.inl` and `pure ∘ Sum.inr`, and
  the Kleisli inclusion preserves copairing, so values are closed under case analysis;
* `IsDistributiveSubcategory` — the distributor's inverse is the type-level distribution map,
  a value;
* `IsUniformIteration` and `IsStrongIteration` — the uniformity and strength axioms of the
  ambient Elgot iteration, which the Kleisli Elgot structure already provides.

The payoff is `pureInclusionStrongElgotFreyd'`: the inclusion of the pure subcategory of
`Kleisli (TM m)` is a strong Elgot Freyd category, with no separate value category.  The same
structure presented as the two-point effect lattice `Kleisli.eff` gives
`effStrongElgotFreydCategory`.
-/

universe u

namespace CategoryTheory

open Category Limits PremonoidalCategory
open scoped MonoidalCategory AddMonoidalCategory

namespace Kleisli.Type

variable (m : Type u → Type u) [_root_.Monad m] [LawfulMonad m]

/-! ### Recognising value morphisms -/

theorem toKleisli_obj_injective :
    Function.Injective (Kleisli.Adjunction.toKleisli (TM m)).obj :=
  fun _ _ h => congrArg Kleisli.of h

/-- A value morphism of the Kleisli category is `J.map` of a function, on the nose: the object
equalities carried by `Functor.imageProperty` are all `rfl` because the Kleisli inclusion is the
identity on objects. -/
theorem exists_map_of_mem {X Y : Kleisli (TM m)} {f : X ⟶ Y}
    (hf : (Kleisli.Adjunction.toKleisli (TM m)).imageProperty f) :
    ∃ g : X.of ⟶ Y.of, f = (Kleisli.Adjunction.toKleisli (TM m)).map g :=
  (Kleisli.Adjunction.toKleisli (TM m)).imageProperty_of_injective
    (toKleisli_obj_injective m) hf

/-! ### The value morphisms are closed under the chosen coproduct -/

/-- `toKleisli_map_desc`, phrased for objects of the Kleisli category rather than for their
images: copairing two value morphisms is a value morphism. -/
theorem toKleisli_map_desc' {X Y Z : Kleisli (TM m)} (f : X.of ⟶ Z.of) (g : Y.of ⟶ Z.of) :
    CocartesianMonoidalCategory.desc (T := Z) (X := X) (Y := Y)
        ((Kleisli.Adjunction.toKleisli (TM m)).map f)
        ((Kleisli.Adjunction.toKleisli (TM m)).map g) =
      (Kleisli.Adjunction.toKleisli (TM m)).map (CocartesianMonoidalCategory.desc f g) :=
  (toKleisli_map_desc m f g).symm

/-- **Values are closed under the chosen finite coproduct structure.**  The injections are
`J.map Sum.inl` and `J.map Sum.inr`, the map out of the initial object is `J.map PEmpty.elim`,
and copairing of values is `J.map` of a copairing because the Kleisli inclusion, a left adjoint,
preserves coproducts. -/
instance isCocartesianSubcategory :
    IsCocartesianSubcategory (Kleisli.Adjunction.toKleisli (TM m)).imageProperty where
  fromZero_mem X := by
    have h : CocartesianMonoidalCategory.fromZero X
        = (Kleisli.Adjunction.toKleisli (TM m)).map (PEmpty.elim : PEmpty → X.of) :=
      CocartesianMonoidalCategory.fromZero_unique _ _
    rw [h]
    exact (Kleisli.Adjunction.toKleisli (TM m)).imageProperty_map _
  inl_mem := inl_mem_eff_bot m
  inr_mem := inr_mem_eff_bot m
  desc_mem := by
    intro X Y Z f g hf hg
    obtain ⟨f', rfl⟩ := exists_map_of_mem m hf
    obtain ⟨g', rfl⟩ := exists_map_of_mem m hg
    rw [toKleisli_map_desc' m]
    exact (Kleisli.Adjunction.toKleisli (TM m)).imageProperty_map _

/-! ### The distributor has a value inverse -/

/-- The type-level left distribution map, the inverse of the chosen distributor. -/
def leftDistrib (X Y Z : Type u) : X × (Y ⊕ Z) → (X × Y) ⊕ (X × Z) :=
  fun p => Sum.elim (fun y => Sum.inl (p.1, y)) (fun z => Sum.inr (p.1, z)) p.2

/-- **The chosen distributor of the Kleisli category has a value inverse**, namely the
type-level distribution map. -/
instance isDistributiveSubcategory :
    IsDistributiveSubcategory (Kleisli.Adjunction.toKleisli (TM m)).imageProperty where
  exists_addLeftInv X Y Z := by
    refine ⟨(Kleisli.Adjunction.toKleisli (TM m)).map (leftDistrib X.of Y.of Z.of),
      (Kleisli.Adjunction.toKleisli (TM m)).imageProperty_map _, ?_, ?_⟩
    · apply Kleisli.hom_ext
      funext p
      rcases p with p | p <;>
        simp [addLeftHom, leftDistrib, Kleisli.whiskerLeft_of, typeMonadStrength, joinM]
    · apply Kleisli.hom_ext
      funext p
      rcases p with ⟨x, y | z⟩ <;>
        simp [addLeftHom, leftDistrib, Kleisli.whiskerLeft_of, typeMonadStrength, joinM]

/-! ### The Elgot axioms -/

variable [Isotope.Elgot.Iterate m] [Isotope.Elgot.LawfulElgotMonad m]

/-- **The ambient iteration is uniform for value morphisms.**  This is the `uniformity` field of
the Kleisli Elgot Freyd structure, restated for the wide subcategory of values. -/
instance isUniformIteration :
    IsUniformIteration (Kleisli.Adjunction.toKleisli (TM m)).imageProperty where
  uniformity := by
    intro A D B f g h hh comm
    obtain ⟨h', rfl⟩ := exists_map_of_mem m hh
    exact ElgotFreydCategory.uniformity (J := Kleisli.Adjunction.toKleisli (TM m)) f g h' comm

/-- **The ambient iteration is strong.**  This is a statement about the Kleisli category alone,
and is the `iterate_whiskerLeft` field of its strong Elgot Freyd structure. -/
instance isStrongIteration : IsStrongIteration (Kleisli (TM m)) where
  iterate_whiskerLeft Z f :=
    StrongElgotFreydCategory.iterate_whiskerLeft
      (J := Kleisli.Adjunction.toKleisli (TM m)) Z f

/-! ### The payoff -/

section Faithful

variable [∀ X : Type u, Mono ((TM m).η.app X)]

/-- **The subcategory presentation has a model.**  The inclusion of the wide subcategory of
value morphisms of `Kleisli (TM m)` into `Kleisli (TM m)` is a strong Elgot Freyd category —
with no separate value category, the values being a subcategory of the computations. -/
noncomputable instance pureInclusionStrongElgotFreyd' :
    StrongElgotFreydCategory
      (pureInclusion (Kleisli.Adjunction.toKleisli (TM m)).imageProperty) :=
  inferInstance

end Faithful

/-! ### The two-point effect lattice -/

/-- **The two-point effect lattice of a Kleisli category is cocartesian.**  For `⊥` this is
closure of the values under the chosen coproduct; for `⊤` there is nothing to check. -/
instance isCocartesianEffectLattice :
    IsCocartesianEffectLattice Bool (Kleisli.eff (TM m)) where
  eff_cocartesian e := by
    cases e
    · exact inferInstanceAs (IsCocartesianSubcategory
        (Kleisli.Adjunction.toKleisli (TM m)).imageProperty)
    · exact inferInstanceAs (IsCocartesianSubcategory (⊤ : MorphismProperty (Kleisli (TM m))))

instance effBotDistributiveSubcategory :
    IsDistributiveSubcategory (Kleisli.eff (TM m) ⊥) :=
  inferInstanceAs
    (IsDistributiveSubcategory (Kleisli.Adjunction.toKleisli (TM m)).imageProperty)

instance effBotUniformIteration :
    IsUniformIteration (Kleisli.eff (TM m) ⊥) :=
  inferInstanceAs
    (IsUniformIteration (Kleisli.Adjunction.toKleisli (TM m)).imageProperty)

/-- **The two-point effect lattice of a Kleisli category is an Elgot effectful Freyd
category**, in the sense of `Isotope.CategoryTheory.Freyd.EffectfulElgot`: its value category is
the pure subcategory `C_⊥`. -/
noncomputable instance effStrongElgotFreydCategory [∀ X : Type u, Mono ((TM m).η.app X)] :
    StrongElgotFreydCategory
      (EffectfulFreydCategory.inclusion (Kleisli.eff (TM m))) :=
  inferInstance

end Kleisli.Type

end CategoryTheory
