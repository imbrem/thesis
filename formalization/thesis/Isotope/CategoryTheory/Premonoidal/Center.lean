import Isotope.CategoryTheory.Premonoidal.Basic
import Mathlib.CategoryTheory.Widesubcategory

/-!
# The center of a premonoidal category

The center has the same objects and only the central morphisms. This first slice constructs its
category and faithful inclusion. A later layer can lift the premonoidal tensor to a monoidal
structure after proving closure of central morphisms under whiskering.
-/

universe v u

namespace CategoryTheory

namespace PremonoidalCategory

variable (C : Type u) [Category.{v} C] [PremonoidalCategory C]

/-- Centrality as a Mathlib morphism property. -/
def central : MorphismProperty C := fun {_ _} f ↦ IsCentral f

instance : (central C).IsMultiplicative where
  id_mem X := isCentral_id X
  comp_mem _ _ hf hg := hf.comp hg

/-- The wide subcategory of central morphisms. -/
abbrev Center := WideSubcategory (central C)

/-- Forget that a morphism lies in the center. -/
abbrev centerInclusion : Functor (Center C) C := wideSubcategoryInclusion (central C)

@[simp] theorem centerInclusion_obj (X : Center C) : (centerInclusion C).obj X = X.obj := rfl

@[simp] theorem centerInclusion_map {X Y : Center C} (f : X ⟶ Y) :
    (centerInclusion C).map f = f.1 := rfl

instance : (centerInclusion C).Faithful := inferInstance

end PremonoidalCategory

end CategoryTheory
