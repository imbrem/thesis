import Isotope.CategoryTheory.Freyd.Subcategory

/-!
# Effectful Freyd categories

This is the third presentation of a Freyd category used in the thesis, and the one the
refinement papers actually work with.  Instead of a functor `J : V ⥤ C` from a separate value
category, we mark out inside `C` itself a *lattice of wide subcategories indexed by effects*:
for each effect `ε` of an effect system `E` a wide symmetric premonoidal subcategory
`C_ε ⊆ C`, monotone in `ε`, whose bottom member `C_⊥` — the *pure* morphisms — is central and
cartesian.

Two theorems connect this with `Isotope.CategoryTheory.Freyd.Basic`:

* `EffectfulFreydCategory.freydCategory`: each effectful Freyd category *is* a Freyd category,
  with value category `V = C_⊥` and `J` the inclusion.
* `EffectfulFreydCategory.ofFreyd`: each (strict, faithful) Freyd category `J : V ⥤ C` gives an
  effectful Freyd category over the two-point effect system, with `⊥` the image of `J`; the
  comparison functor `FreydCategory.toImage J : V ⥤ C_⊥` is bijective on objects, full and
  faithful, and recovers `J` after forgetting purity.

The two-point effect system is the degenerate case `E = Bool`: an effect system only
distinguishes "pure" from "arbitrary".  A general `E` refines this, which is exactly what
substructural refinement needs.
-/

universe v₁ v₂ u₁ u₂ u₃

namespace CategoryTheory

open Category Limits PremonoidalCategory
open scoped MonoidalCategory

/-- A *lattice of subcategories indexed by effects*: a monotone family of wide symmetric
premonoidal subcategories `C_ε = eff ε` of a symmetric premonoidal category `C`. -/
class EffectLattice (E : Type u₃) [Preorder E]
    {C : Type u₂} [Category.{v₂} C] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
    (eff : E → MorphismProperty C) : Prop where
  /-- More permissive effects allow more morphisms. -/
  eff_mono : Monotone eff
  /-- Each effect carves out a wide symmetric premonoidal subcategory. -/
  eff_subcategory (e : E) : IsSymmetricSubcategory (eff e)

attribute [instance] EffectLattice.eff_subcategory

/-- **Effectful Freyd category (subcategory presentation).**

A symmetric premonoidal category `C` together with an effect lattice of wide subcategories
`C_ε ⊆ C`, whose bottom member — the *pure* morphisms `C_⊥` — is central and makes the
premonoidal tensor a cartesian product.  That last condition is exactly the defining condition
of a Freyd category, with `C_⊥` playing the role of the value category. -/
class EffectfulFreydCategory (E : Type u₃) [Preorder E] [OrderBot E]
    {C : Type u₂} [Category.{v₂} C] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
    (eff : E → MorphismProperty C)
    [IsCentralSubcategory (eff ⊥)] [IsSemiCartesianSubcategory (eff ⊥)]
    [IsCartesianSubcategory (eff ⊥)] : Prop extends EffectLattice E eff

namespace EffectfulFreydCategory

variable {E : Type u₃} [Preorder E] [OrderBot E]
  {C : Type u₂} [Category.{v₂} C] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  (eff : E → MorphismProperty C)
  [IsCentralSubcategory (eff ⊥)] [IsSemiCartesianSubcategory (eff ⊥)]
  [IsCartesianSubcategory (eff ⊥)] [EffectfulFreydCategory E eff]

theorem pure_le (e : E) : eff ⊥ ≤ eff e := EffectLattice.eff_mono (eff := eff) bot_le

theorem pure_mem {X Y : C} {f : X ⟶ Y} (hf : eff ⊥ f) (e : E) : eff e f := pure_le eff e _ hf

/-- Pure morphisms commute with everything. -/
theorem pure_central {X Y : C} {f : X ⟶ Y} (hf : eff ⊥ f) : IsCentral f :=
  IsCentralSubcategory.central hf

/-- The value category of an effectful Freyd category: its pure morphisms. -/
abbrev Value : Type u₂ := WideSubcategory (eff ⊥)

/-- The inclusion of the value category, i.e. of the pure morphisms. -/
abbrev inclusion : Functor (Value eff) C := pureInclusion (eff ⊥)

/-- **Each effectful Freyd category is a Freyd category**, with `V = C_⊥` and `J` the
inclusion of the pure morphisms. -/
instance freydCategory : FreydCategory (inclusion eff) := pureInclusionFreyd (eff ⊥)

instance inclusion_faithful : (inclusion eff).Faithful := inferInstance

instance inclusion_strict : Functor.IsStrictPremonoidal (inclusion eff) :=
  pureInclusionStrict (eff ⊥)

end EffectfulFreydCategory

/-! ### The two-point effect system of a plain Freyd category -/

namespace EffectfulFreydCategory

variable {C : Type u₂} [Category.{v₂} C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]

/-- The degenerate two-point effect system attached to a wide subcategory `P`: `⊥` is `P` and
`⊤` is all of `C`. -/
def twoPoint (P : MorphismProperty C) : Bool → MorphismProperty C
  | false => P
  | true => ⊤

@[simp] theorem twoPoint_bot (P : MorphismProperty C) : twoPoint P ⊥ = P := rfl

@[simp] theorem twoPoint_top (P : MorphismProperty C) : twoPoint P ⊤ = ⊤ := rfl

instance twoPointBotCentral (P : MorphismProperty C) [IsCentralSubcategory P] :
    IsCentralSubcategory (twoPoint P ⊥) := inferInstanceAs (IsCentralSubcategory P)

instance twoPointBotSemiCartesian (P : MorphismProperty C) [IsCentralSubcategory P]
    [IsSemiCartesianSubcategory P] : IsSemiCartesianSubcategory (twoPoint P ⊥) :=
  inferInstanceAs (IsSemiCartesianSubcategory P)

instance twoPointBotCartesian (P : MorphismProperty C) [IsCentralSubcategory P]
    [IsSemiCartesianSubcategory P] [IsCartesianSubcategory P] :
    IsCartesianSubcategory (twoPoint P ⊥) := inferInstanceAs (IsCartesianSubcategory P)

theorem twoPoint_monotone (P : MorphismProperty C) : Monotone (twoPoint P) := by
  rintro (_ | _) (_ | _) h
  · exact le_rfl
  · exact le_top
  · exact absurd h (by simp)
  · exact le_rfl

/-- Any cartesian central wide subcategory is the pure part of an effectful Freyd category over
the two-point effect system. -/
instance twoPointEffectful (P : MorphismProperty C) [IsCentralSubcategory P]
    [IsSemiCartesianSubcategory P] [IsCartesianSubcategory P] :
    EffectfulFreydCategory Bool (twoPoint P) where
  eff_mono := twoPoint_monotone P
  eff_subcategory e := by
    cases e
    · exact inferInstanceAs (IsSymmetricSubcategory P)
    · exact inferInstanceAs (IsSymmetricSubcategory (⊤ : MorphismProperty C))

end EffectfulFreydCategory

/-! ### Every Freyd category maps to an effectful Freyd category -/

namespace FreydCategory

open EffectfulFreydCategory

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  (J : Functor V C) [FreydCategory J] [Functor.IsStrictPremonoidal J] [J.Faithful]

/-- The effect system attached to a Freyd category: `⊥` is the image of `J`. -/
abbrev freydEff : Bool → MorphismProperty C := twoPoint J.imageProperty

/-- `⊥` is exactly the image of `J`. -/
@[simp] theorem freydEff_bot : freydEff J ⊥ = J.imageProperty := rfl

@[simp] theorem freydEff_top : freydEff J ⊤ = ⊤ := rfl

/-- **Every (strict, faithful) Freyd category maps to an effectful Freyd category**, with `⊥`
the image of `J`. -/
instance ofFreyd : EffectfulFreydCategory Bool (freydEff J) :=
  twoPointEffectful J.imageProperty

/-- The value category of the induced effectful Freyd category is the wide subcategory of pure
morphisms, and `FreydCategory.toImage J` is the comparison functor into it.  It is bijective on
objects, full and faithful, and composing with the inclusion recovers `J`. -/
theorem toImage_spec :
    Function.Bijective (toImage J).obj ∧
      toImage J ⋙ inclusion (freydEff J) = J :=
  ⟨toImage_obj_bijective J, toImage_comp_pureInclusion J⟩

end FreydCategory

end CategoryTheory
