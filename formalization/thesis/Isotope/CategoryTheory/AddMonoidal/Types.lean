import Isotope.CategoryTheory.AddMonoidal.Cocartesian
import Mathlib.CategoryTheory.Limits.Types.Shapes

/-!
# `Type u` is cocartesian monoidal, with `Sum` as the chosen coproduct

This is the point of a *chosen* structure: `X ⊕ₘ Y` is `X ⊕ Y` on the nose, `inl` is `Sum.inl`,
and `desc` is `Sum.elim` — all definitionally, with no `Classical.choice` in sight.
-/

universe u

namespace CategoryTheory

open Limits
open scoped AddMonoidalCategory

namespace Types

/-- `Type u` is additively monoidal with `Sum`. -/
instance addMonoidalCategory : AddMonoidalCategory (Type u) where
  addObj X Y := X ⊕ Y
  addWhiskerLeft := fun _ {_ _} f => Sum.map id f
  addWhiskerRight := fun {_ _} f _ => Sum.map f id
  addHom := fun {_ _ _ _} f g => Sum.map f g
  addUnit := PEmpty
  addAssociator X Y Z := (Equiv.sumAssoc X Y Z).toIso
  addLeftUnitor X := (Equiv.emptySum PEmpty X).toIso
  addRightUnitor X := (Equiv.sumEmpty X PEmpty).toIso
  addHom_def _ _ := by funext x; rcases x with x | x <;> rfl
  id_addHom_id _ _ := by funext x; rcases x with x | x <;> rfl
  addHom_comp_addHom _ _ _ _ := by funext x; rcases x with x | x <;> rfl
  addWhiskerLeft_id _ _ := by funext x; rcases x with x | x <;> rfl
  id_addWhiskerRight _ _ := by funext x; rcases x with x | x <;> rfl
  addAssociator_naturality _ _ _ := by
    funext x; rcases x with (x | x) | x <;> rfl
  addLeftUnitor_naturality _ := by
    funext x
    rcases x with x | x
    · exact x.elim
    · rfl
  addRightUnitor_naturality _ := by
    funext x
    rcases x with x | x
    · rfl
    · exact x.elim
  addPentagon _ _ _ _ := by funext x; rcases x with ((x | x) | x) | x <;> rfl
  addTriangle _ _ := by
    funext x
    rcases x with (x | x) | x
    · rfl
    · exact x.elim
    · rfl

@[simp] theorem addObj_def (X Y : Type u) : X ⊕ₘ Y = (X ⊕ Y) := rfl

@[simp] theorem addUnit_def : (𝟘_ (Type u)) = PEmpty := rfl

/-- `Type u` is cocartesian monoidal: `Sum` really is the coproduct. -/
instance cocartesianMonoidalCategory : CocartesianMonoidalCategory (Type u) where
  isInitialAddUnit :=
    IsInitial.ofUniqueHom (fun _ x => x.elim) (fun _ _ => by funext x; exact x.elim)
  inl _ _ := Sum.inl
  inr _ _ := Sum.inr
  inl_def _ _ := by funext x; rfl
  inr_def _ _ := by funext x; rfl
  addObjIsBinaryCoproduct X Y :=
    BinaryCofan.IsColimit.mk _
      (fun f g => Sum.elim f g)
      (fun _ _ => rfl)
      (fun _ _ => rfl)
      (fun f g m h₁ h₂ => by
        funext x
        rcases x with x | x
        · exact congrFun h₁ x
        · exact congrFun h₂ x)

@[simp] theorem inl_def' (X Y : Type u) :
    CocartesianMonoidalCategory.inl X Y = Sum.inl := rfl

@[simp] theorem inr_def' (X Y : Type u) :
    CocartesianMonoidalCategory.inr X Y = Sum.inr := rfl

@[simp] theorem desc_def {X Y T : Type u} (f : X ⟶ T) (g : Y ⟶ T) :
    CocartesianMonoidalCategory.desc f g = Sum.elim f g := by
  funext x; rcases x with x | x
  · exact congrFun (CocartesianMonoidalCategory.inl_desc f g) x
  · exact congrFun (CocartesianMonoidalCategory.inr_desc f g) x

/-- The chosen structure computes.  Unlike `X ⨿ Y`, whose apex and injections come from
`Classical.choice`, `⊕ₘ`, `inl` and `desc` all reduce definitionally. -/
example (X Y : Type u) :
    CocartesianMonoidalCategory.inl X Y ≫
        CocartesianMonoidalCategory.desc (Sum.inr : X ⟶ Y ⊕ X) (Sum.inl : Y ⟶ Y ⊕ X) =
      Sum.inr :=
  rfl

end Types

end CategoryTheory
