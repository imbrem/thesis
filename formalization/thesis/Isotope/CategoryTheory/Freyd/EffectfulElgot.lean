import Isotope.CategoryTheory.Freyd.Effectful
import Isotope.CategoryTheory.Freyd.SubcategoryElgot

/-!
# Elgot effectful Freyd categories

This is the bridge from the effect-lattice presentation to the categorical semantics of λ-iter.
An effectful Freyd category whose effects are closed under the coproduct structure, whose pure
distributor is invertible purely, and whose ambient iteration is pure-uniform and strong, is a
`StrongElgotFreydCategory` in the sense of `Isotope.CategoryTheory.Freyd.Elgot` — with value
category `C_⊥` and `J` the inclusion of the pure morphisms, rather than a separate category.
-/

universe v₂ u₂ u₃

namespace CategoryTheory

open Category Limits PremonoidalCategory
open scoped MonoidalCategory

variable {C : Type u₂} [Category.{v₂} C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]

/-- Every effect is closed under the finite coproduct structure of `C`: the injections and the
maps out of the initial object are pure, and case analysis stays inside an effect. -/
class IsCocartesianEffectLattice (E : Type u₃) [Preorder E]
    (eff : E → MorphismProperty C) : Prop where
  eff_cocartesian (e : E) : IsCocartesianSubcategory (eff e)

attribute [instance] IsCocartesianEffectLattice.eff_cocartesian

/-- The effects closed under iteration: the paper's `E^∞`. -/
class IterativeEffects (E : Type u₃) [Preorder E] [Iteration C]
    (eff : E → MorphismProperty C) (iterative : E → Prop) : Prop where
  iterate_mem {e : E} (he : iterative e) {X Y : C} {f : X ⟶ Y ⨿ X} :
    eff e f → eff e (iterate f)

namespace EffectfulFreydCategory

variable {E : Type u₃} [Preorder E] [OrderBot E]
  (eff : E → MorphismProperty C)
  [IsCentralSubcategory (eff ⊥)] [IsSemiCartesianSubcategory (eff ⊥)]
  [IsCartesianSubcategory (eff ⊥)] [EffectfulFreydCategory E eff]
  [IsCocartesianEffectLattice E eff]

section Distributive

variable [DistributiveTensor C] [IsDistributiveSubcategory (eff ⊥)]

/-- **The value category `C_⊥` is distributive**, and the inclusion preserves finite
coproducts. -/
instance distributiveFreydCategory : DistributiveFreydCategory (inclusion eff) :=
  pureInclusionDistributiveFreyd (eff ⊥)

section Elgot

variable [Iteration C] [ElgotCategory C] [IsUniformIteration (eff ⊥)]

instance elgotFreydCategory : ElgotFreydCategory (inclusion eff) :=
  pureInclusionElgotFreyd (eff ⊥)

variable [IsStrongIteration C]

/-- **An Elgot effectful Freyd category is a strong Elgot Freyd category**, with `V = C_⊥`. -/
instance strongElgotFreydCategory : StrongElgotFreydCategory (inclusion eff) :=
  pureInclusionStrongElgotFreyd (eff ⊥)

end Elgot

end Distributive

end EffectfulFreydCategory

end CategoryTheory
