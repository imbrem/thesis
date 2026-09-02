import Isotope.CategoryTheory.Freyd.Effectful
import Isotope.CategoryTheory.Monad.Kleisli

/-!
# Kleisli categories as effectful Freyd categories

The Kleisli category of a strong monad on a cartesian monoidal category is the standard example
of a Freyd category, with the value morphisms as the pure ones.  Its inclusion is *strict* — the
Kleisli category has the same objects and the same tensor — and it is *faithful* exactly when
the unit of the monad is a monomorphism.  So `FreydCategory.ofFreyd` applies and gives a
concrete effectful Freyd category over the two-point effect system.
-/

universe v u

namespace CategoryTheory

open Category Limits
open scoped MonoidalCategory

namespace Kleisli

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D] [SymmetricCategory D]
  (S : Monad D) [S.Strong]

/-- The Kleisli inclusion is strict: it is the identity on objects and preserves the tensor on
the nose. -/
instance toKleisliStrict : Functor.IsStrictPremonoidal (Kleisli.Adjunction.toKleisli S) where
  obj_unit := rfl
  obj_tensor _ _ := rfl
  unitIso_hom := rfl
  tensorIso_hom _ _ := rfl

/-- The Kleisli inclusion is faithful when the unit of the monad is a monomorphism: distinct
value morphisms then remain distinct as computations. -/
instance toKleisliFaithful [∀ X : D, Mono (S.η.app X)] :
    (Kleisli.Adjunction.toKleisli S).Faithful where
  map_injective {_ Y _ _} h :=
    (cancel_mono (S.η.app Y)).1 (congrArg Kleisli.Hom.of h)

/-- The two-point effect lattice of a Kleisli category: `⊥` is the value morphisms — those of
the form `f ≫ η` — and `⊤` is all computations. -/
abbrev eff : Bool → MorphismProperty (Kleisli S) :=
  EffectfulFreydCategory.twoPoint (Kleisli.Adjunction.toKleisli S).imageProperty

/-- **A concrete effectful Freyd category.** -/
instance effectfulFreydCategory [∀ X : D, Mono (S.η.app X)] :
    EffectfulFreydCategory Bool (eff S) := inferInstance

theorem eff_bot : eff S ⊥ = (Kleisli.Adjunction.toKleisli S).imageProperty := rfl

theorem eff_top : eff S ⊤ = ⊤ := rfl

/-- A Kleisli morphism is pure exactly when it is `f ≫ η` for a morphism `f` of the base. -/
theorem eff_bot_iff {X Y : Kleisli S} (f : X ⟶ Y) :
    eff S ⊥ f ↔ ∃ g : X.of ⟶ Y.of, f = Kleisli.Hom.mk (g ≫ S.η.app Y.of) := by
  constructor
  · rintro ⟨A, B, hA, hB, g, rfl⟩
    cases hA; cases hB
    exact ⟨g, by simp; rfl⟩
  · rintro ⟨g, rfl⟩
    exact (Kleisli.Adjunction.toKleisli S).imageProperty_map g

end Kleisli

end CategoryTheory
