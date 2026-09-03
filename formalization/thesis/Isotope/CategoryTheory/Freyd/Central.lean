import Isotope.CategoryTheory.Freyd.Subcategory

/-!
# Centrality of the coherence isomorphisms of a strong premonoidal functor

`Functor.StrongPremonoidal` requires the *images* `J.map f` to be central
(`map_central`) but says nothing about its own structure maps `unitIso` and
`tensorIso`.  Those two centrality statements are **independent** of the stated
axioms: every field of `Functor.StrongPremonoidal` relating `unitIso` or
`tensorIso` to a computation morphism does so only through a value morphism
`J.map g`, so nothing forces `unitIso.hom ⋉ f = unitIso.hom ⋊ f` for an
arbitrary computation `f`.

They are nevertheless part of the standard meaning of *strong* in the
premonoidal literature, and they are needed already for the very first
syntactic law: the `let` eta rule `let x = a in x ≡ a` reduces to
`extend J f ≫ J.map (snd _ _) = f`, whose proof must slide `f` past the
composite `J.map (toUnit R) ≫ unitIso.inv`.

Rather than strengthen the shared class, this file supplies the two laws as an
optional mixin, in the same style as `TensorEmptyStrict`, together with a
generic instance for every *strict* premonoidal functor — which covers every
`Functor.StrongPremonoidal` instance currently in the development, the Kleisli
inclusion of a monad included.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category
open PremonoidalCategory
open scoped MonoidalCategory

/-- The coherence isomorphisms of `J` are central.  This is the half of
"strongness" that `Functor.StrongPremonoidal` omits; see the module docstring
for why it is not derivable there. -/
class Functor.StrongPremonoidalCentral {V : Type u₁} {C : Type u₂}
    [Category.{v₁} V] [Category.{v₂} C] [MonoidalCategory V] [PremonoidalCategory C]
    (J : Functor V C) [Functor.StrongPremonoidal J] : Prop where
  unitIso_central :
    IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom
  tensorIso_central (X Y : V) :
    IsCentral (Functor.StrongPremonoidal.tensorIso (J := J) X Y).hom

namespace Functor.StrongPremonoidalCentral

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C] [MonoidalCategory V] [PremonoidalCategory C]
  (J : Functor V C) [Functor.StrongPremonoidal J] [Functor.StrongPremonoidalCentral J]

/-- The inverse unit coherence isomorphism is central. -/
theorem unitIso_inv_central :
    IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).inv :=
  IsCentral.inv _ unitIso_central

/-- The inverse tensor coherence isomorphisms are central. -/
theorem tensorIso_inv_central (X Y : V) :
    IsCentral (Functor.StrongPremonoidal.tensorIso (J := J) X Y).inv :=
  IsCentral.inv _ (tensorIso_central X Y)

end Functor.StrongPremonoidalCentral

/-- A strict premonoidal functor has `eqToHom` coherence isomorphisms, so they
are central for free.  In particular the Kleisli inclusion of any monad and the
inclusion of any pure wide subcategory satisfy the mixin. -/
instance Functor.strongPremonoidalCentralOfStrict {V : Type u₁} {C : Type u₂}
    [Category.{v₁} V] [Category.{v₂} C] [MonoidalCategory V] [PremonoidalCategory C]
    (J : Functor V C) [Functor.StrongPremonoidal J] [Functor.IsStrictPremonoidal J] :
    Functor.StrongPremonoidalCentral J where
  unitIso_central := by
    rw [Functor.IsStrictPremonoidal.unitIso_hom (J := J)]
    exact PremonoidalCategory.isCentral_eqToHom _
  tensorIso_central X Y := by
    rw [Functor.IsStrictPremonoidal.tensorIso_hom (J := J) X Y]
    exact PremonoidalCategory.isCentral_eqToHom _

end CategoryTheory
