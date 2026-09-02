import Isotope.CategoryTheory.Freyd.Basic
import Isotope.CategoryTheory.Premonoidal.Subcategory

/-!
# Freyd categories from wide subcategories, and back

`Isotope.CategoryTheory.Freyd.Basic` packages a Freyd category as a functor `J : V ⥤ C`.  The
original presentation instead marks out a wide subcategory `C_⊥ ⊆ C` of *pure* morphisms.  This
file relates the two.

* `PremonoidalCategory.pureInclusion P` exhibits the inclusion of a cartesian central wide
  subcategory as a Freyd category.  This is the "each of these becomes a Freyd category with
  `V = C_⊥`" direction.
* `Functor.imageProperty J` is the wide subcategory of morphisms in the image of `J`.  For a
  *strict* Freyd inclusion this is a cartesian central wide subcategory, and the comparison
  functor `Functor.toImage J : V ⥤ WideSubcategory (imageProperty J)` is bijective on objects,
  full, and commutes with the two inclusions.  This is the "every Freyd category maps to one of
  these, with `⊥` the image of `J`" direction.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits
open scoped MonoidalCategory

/-! ### The image of a Freyd inclusion -/

namespace Functor

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]

/-- The morphisms of `C` which are images of morphisms of `V` under `J`.  Since a Freyd
inclusion is bijective on objects, the object equalities carried here are unique, and this is a
wide subcategory of `C`. -/
def imageProperty (J : Functor V C) : MorphismProperty C :=
  fun {X Y} f => ∃ (X' Y' : V) (hX : J.obj X' = X) (hY : J.obj Y' = Y) (g : X' ⟶ Y'),
    f = eqToHom hX.symm ≫ J.map g ≫ eqToHom hY

theorem imageProperty_map (J : Functor V C) {X Y : V} (g : X ⟶ Y) :
    J.imageProperty (J.map g) := ⟨X, Y, rfl, rfl, g, by simp⟩

theorem imageProperty_eqToHom (J : Functor V C) (hsurj : Function.Surjective J.obj)
    {X Y : C} (h : X = Y) : J.imageProperty (eqToHom h) := by
  obtain ⟨X', rfl⟩ := hsurj X
  subst h
  simpa using imageProperty_map J (𝟙 X')

theorem imageProperty_of_injective (J : Functor V C) (hinj : Function.Injective J.obj)
    {X' Y' : V} {f : J.obj X' ⟶ J.obj Y'} (hf : J.imageProperty f) :
    ∃ g : X' ⟶ Y', f = J.map g := by
  obtain ⟨A, B, hA, hB, g, rfl⟩ := hf
  obtain rfl := hinj hA
  obtain rfl := hinj hB
  exact ⟨g, by simp⟩

open scoped MonoidalCategory in
/-- A Freyd inclusion is *strict* when it preserves the tensor and the unit on the nose, its
coherence isomorphisms being the corresponding identities.  This is the original
Levy–Power–Thielecke presentation, and it is what makes the image of `J` closed under the
structural isomorphisms of `C`. -/
class IsStrictPremonoidal {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
    [MonoidalCategory V] [PremonoidalCategory C] (J : Functor V C)
    [Functor.StrongPremonoidal J] : Prop where
  obj_unit : J.obj (𝟙_ V) = 𝟙_ C
  obj_tensor (X Y : V) : J.obj (X ⊗ Y) = J.obj X ⊗ J.obj Y
  unitIso_hom : (Functor.StrongPremonoidal.unitIso (J := J)).hom = eqToHom obj_unit.symm
  tensorIso_hom (X Y : V) :
    (Functor.StrongPremonoidal.tensorIso (J := J) X Y).hom = eqToHom (obj_tensor X Y).symm

end Functor

namespace PremonoidalCategory

variable {C : Type u₂} [Category.{v₂} C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C] (P : MorphismProperty C)
  [IsCentralSubcategory P] [IsSemiCartesianSubcategory P] [IsCartesianSubcategory P]

/-- The inclusion of the pure subcategory into the ambient premonoidal category. -/
abbrev pureInclusion : Functor (WideSubcategory P) C := wideSubcategoryInclusion P

instance pureInclusionStrongSymmetricPremonoidal :
    Functor.StrongSymmetricPremonoidal (pureInclusion P) where
  unitIso := Iso.refl _
  tensorIso _ _ := Iso.refl _
  tensor_naturality_left _ _ := by simp
  tensor_naturality_right _ _ := by simp
  associativity _ _ _ := by simp
  left_unitality _ := by simp
  right_unitality _ := by simp
  map_central f := IsCentralSubcategory.central f.2
  braiding _ _ := by simp

/-- **The subcategory presentation is a Freyd category.**  The value category is the wide
subcategory of pure morphisms itself, and the Freyd inclusion is the forgetful functor. -/
instance pureInclusionFreyd : FreydCategory (pureInclusion P) where
  obj_bijective :=
    ⟨fun _ _ h => WideSubcategory.ext h, fun X => ⟨⟨X⟩, rfl⟩⟩

@[simp] theorem pureInclusion_unitIso :
    (Functor.StrongPremonoidal.unitIso (J := pureInclusion P)) = Iso.refl _ := rfl

@[simp] theorem pureInclusion_tensorIso (X Y : WideSubcategory P) :
    (Functor.StrongPremonoidal.tensorIso (J := pureInclusion P) X Y) = Iso.refl _ := rfl

/-- The inclusion of a wide subcategory is strict: it is the identity on objects, so both
coherence isomorphisms are identities. -/
instance pureInclusionStrict : Functor.IsStrictPremonoidal (pureInclusion P) where
  obj_unit := rfl
  obj_tensor _ _ := rfl
  unitIso_hom := by simp
  tensorIso_hom _ _ := by simp

end PremonoidalCategory


/-! ### The image of a strict Freyd inclusion is a cartesian central wide subcategory -/

namespace FreydCategory

open Functor Functor.StrongPremonoidal Functor.IsStrictPremonoidal
open PremonoidalCategory

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  (J : Functor V C) [FreydCategory J] [Functor.IsStrictPremonoidal J]

theorem obj_surjective : Function.Surjective J.obj :=
  (FreydCategory.obj_bijective (J := J)).2

theorem obj_injective : Function.Injective J.obj :=
  (FreydCategory.obj_bijective (J := J)).1

theorem mem_eqToHom {X Y : C} (h : X = Y) : J.imageProperty (eqToHom h) :=
  J.imageProperty_eqToHom (obj_surjective J) h

theorem mem_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : J.imageProperty f) (hg : J.imageProperty g) : J.imageProperty (f ≫ g) := by
  obtain ⟨A, B, rfl, rfl, a, rfl⟩ := hf
  obtain ⟨B', D, hB, rfl, b, rfl⟩ := hg
  obtain rfl := obj_injective J hB
  exact ⟨A, D, rfl, rfl, a ≫ b, by simp⟩

/-- The canonical shape of a morphism in the image. -/
theorem mem_conj {X Y : C} {X' Y' : V} (hX : J.obj X' = X) (hY : J.obj Y' = Y) (g : X' ⟶ Y') :
    J.imageProperty (eqToHom hX.symm ≫ J.map g ≫ eqToHom hY) := ⟨X', Y', hX, hY, g, rfl⟩

instance imageProperty_isMultiplicative : (J.imageProperty).IsMultiplicative where
  id_mem X := by
    obtain ⟨X', rfl⟩ := obj_surjective J X
    simpa using J.imageProperty_map (𝟙 X')
  comp_mem _ _ hf hg := mem_comp J hf hg

/-! #### Structural morphisms of `C` lie in the image -/

theorem whiskerLeft_map_eq (Z : V) {X Y : V} (g : X ⟶ Y) :
    J.obj Z ◁ J.map g =
      eqToHom (obj_tensor (J := J) Z X).symm ≫ J.map (Z ◁ g) ≫
        eqToHom (obj_tensor (J := J) Z Y) := by
  have h := tensor_naturality_right (J := J) Z g
  rw [tensorIso_hom, tensorIso_hom] at h
  rw [← Category.assoc, ← h]
  simp

theorem whiskerRight_map_eq {X Y : V} (g : X ⟶ Y) (Z : V) :
    J.map g ▷ J.obj Z =
      eqToHom (obj_tensor (J := J) X Z).symm ≫ J.map (g ▷ Z) ≫
        eqToHom (obj_tensor (J := J) Y Z) := by
  have h := tensor_naturality_left (J := J) g Z
  rw [tensorIso_hom, tensorIso_hom] at h
  rw [← Category.assoc, ← h]
  simp

theorem mem_whiskerLeft (Z : C) {X Y : C} {f : X ⟶ Y} (hf : J.imageProperty f) :
    J.imageProperty (Z ◁ f) := by
  obtain ⟨Z', rfl⟩ := obj_surjective J Z
  obtain ⟨A, B, rfl, rfl, g, rfl⟩ := hf
  rw [PremonoidalCategory.whiskerLeft_comp, PremonoidalCategory.whiskerLeft_comp,
    PremonoidalCategory.whiskerLeft_eqToHom, PremonoidalCategory.whiskerLeft_eqToHom,
    whiskerLeft_map_eq]
  exact mem_comp J (mem_eqToHom J _)
    (mem_comp J (mem_comp J (mem_eqToHom J _)
      (mem_comp J (J.imageProperty_map _) (mem_eqToHom J _))) (mem_eqToHom J _))

theorem mem_whiskerRight {X Y : C} {f : X ⟶ Y} (hf : J.imageProperty f) (Z : C) :
    J.imageProperty (f ▷ Z) := by
  obtain ⟨Z', rfl⟩ := obj_surjective J Z
  obtain ⟨A, B, rfl, rfl, g, rfl⟩ := hf
  rw [PremonoidalCategory.comp_whiskerRight, PremonoidalCategory.comp_whiskerRight,
    PremonoidalCategory.whiskerRight_eqToHom, PremonoidalCategory.whiskerRight_eqToHom,
    whiskerRight_map_eq]
  exact mem_comp J (mem_eqToHom J _)
    (mem_comp J (mem_comp J (mem_eqToHom J _)
      (mem_comp J (J.imageProperty_map _) (mem_eqToHom J _))) (mem_eqToHom J _))

/-- If a morphism in the image is a two-sided inverse for an isomorphism, then that
isomorphism's inverse lies in the image.  Inverses are *not* preserved in general: only the
structural isomorphisms, which are `J.map` of isomorphisms of `V`, are recovered this way. -/
theorem mem_inv_of {X Y : C} (e : X ≅ Y) (g : Y ⟶ X) (h : e.hom ≫ g = 𝟙 X)
    (hg : J.imageProperty g) : J.imageProperty e.inv := by
  have he : e.inv = g := by
    have h' := congrArg (fun k : X ⟶ X => e.inv ≫ k) h
    simpa using h'.symm
  rwa [he]

theorem associator_hom_eq (X Y Z : V) :
    (α_ (J.obj X) (J.obj Y) (J.obj Z)).hom =
      eqToHom (by rw [obj_tensor (J := J), obj_tensor (J := J)] :
          (J.obj X ⊗ J.obj Y) ⊗ J.obj Z = J.obj ((X ⊗ Y) ⊗ Z)) ≫
        J.map (α_ X Y Z).hom ≫
        eqToHom (by rw [obj_tensor (J := J), obj_tensor (J := J)] :
          J.obj (X ⊗ (Y ⊗ Z)) = J.obj X ⊗ (J.obj Y ⊗ J.obj Z)) := by
  have h := associativity (J := J) X Y Z
  rw [tensorIso_hom, tensorIso_hom, tensorIso_hom, tensorIso_hom] at h
  simp only [PremonoidalCategory.whiskerLeft_eqToHom, PremonoidalCategory.whiskerRight_eqToHom,
    eqToHom_trans] at h
  rw [comp_eqToHom_iff] at h
  simpa using h

theorem leftUnitor_hom_eq (X : V) :
    (λ_ (J.obj X)).hom =
      eqToHom (by rw [obj_tensor (J := J), obj_unit (J := J)] :
          𝟙_ C ⊗ J.obj X = J.obj (𝟙_ V ⊗ X)) ≫ J.map (λ_ X).hom := by
  have h := left_unitality (J := J) X
  rw [tensorIso_hom, unitIso_hom] at h
  simp only [PremonoidalCategory.whiskerRight_eqToHom] at h
  rw [← h]
  simp

theorem rightUnitor_hom_eq (X : V) :
    (ρ_ (J.obj X)).hom =
      eqToHom (by rw [obj_tensor (J := J), obj_unit (J := J)] :
          J.obj X ⊗ 𝟙_ C = J.obj (X ⊗ 𝟙_ V)) ≫ J.map (ρ_ X).hom := by
  have h := right_unitality (J := J) X
  rw [tensorIso_hom, unitIso_hom] at h
  simp only [PremonoidalCategory.whiskerLeft_eqToHom] at h
  rw [← h]
  simp

theorem braiding_hom_eq (X Y : V) :
    (BraidedPremonoidalCategory.braiding (J.obj X) (J.obj Y)).hom =
      eqToHom (by rw [obj_tensor (J := J)] : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y)) ≫
        J.map (BraidedCategory.braiding X Y).hom ≫
        eqToHom (by rw [obj_tensor (J := J)] : J.obj (Y ⊗ X) = J.obj Y ⊗ J.obj X) := by
  have h := Functor.StrongSymmetricPremonoidal.braiding (J := J) X Y
  rw [tensorIso_hom, tensorIso_hom] at h
  rw [← Category.assoc, h]
  simp

theorem mem_associator_hom (A B D : C) : J.imageProperty (α_ A B D).hom := by
  obtain ⟨X, rfl⟩ := obj_surjective J A
  obtain ⟨Y, rfl⟩ := obj_surjective J B
  obtain ⟨Z, rfl⟩ := obj_surjective J D
  rw [associator_hom_eq]
  exact mem_comp J (mem_eqToHom J _) (mem_comp J (J.imageProperty_map _) (mem_eqToHom J _))

theorem mem_associator_inv (A B D : C) : J.imageProperty (α_ A B D).inv := by
  obtain ⟨X, rfl⟩ := obj_surjective J A
  obtain ⟨Y, rfl⟩ := obj_surjective J B
  obtain ⟨Z, rfl⟩ := obj_surjective J D
  refine mem_inv_of J _
    (eqToHom (by rw [obj_tensor (J := J), obj_tensor (J := J)] :
        J.obj X ⊗ (J.obj Y ⊗ J.obj Z) = J.obj (X ⊗ (Y ⊗ Z))) ≫
      J.map (α_ X Y Z).inv ≫
      eqToHom (by rw [obj_tensor (J := J), obj_tensor (J := J)] :
        J.obj ((X ⊗ Y) ⊗ Z) = (J.obj X ⊗ J.obj Y) ⊗ J.obj Z)) ?_ ?_
  · rw [associator_hom_eq]; simp [← J.map_comp]
  · exact mem_comp J (mem_eqToHom J _) (mem_comp J (J.imageProperty_map _) (mem_eqToHom J _))

theorem mem_leftUnitor_hom (A : C) : J.imageProperty (λ_ A).hom := by
  obtain ⟨X, rfl⟩ := obj_surjective J A
  rw [leftUnitor_hom_eq]
  exact mem_comp J (mem_eqToHom J _) (J.imageProperty_map _)

theorem mem_leftUnitor_inv (A : C) : J.imageProperty (λ_ A).inv := by
  obtain ⟨X, rfl⟩ := obj_surjective J A
  refine mem_inv_of J _
    (J.map (λ_ X).inv ≫ eqToHom (by rw [obj_tensor (J := J), obj_unit (J := J)] :
        J.obj (𝟙_ V ⊗ X) = 𝟙_ C ⊗ J.obj X)) ?_ ?_
  · rw [leftUnitor_hom_eq]; simp [← J.map_comp]
  · exact mem_comp J (J.imageProperty_map _) (mem_eqToHom J _)

theorem mem_rightUnitor_hom (A : C) : J.imageProperty (ρ_ A).hom := by
  obtain ⟨X, rfl⟩ := obj_surjective J A
  rw [rightUnitor_hom_eq]
  exact mem_comp J (mem_eqToHom J _) (J.imageProperty_map _)

theorem mem_rightUnitor_inv (A : C) : J.imageProperty (ρ_ A).inv := by
  obtain ⟨X, rfl⟩ := obj_surjective J A
  refine mem_inv_of J _
    (J.map (ρ_ X).inv ≫ eqToHom (by rw [obj_tensor (J := J), obj_unit (J := J)] :
        J.obj (X ⊗ 𝟙_ V) = J.obj X ⊗ 𝟙_ C)) ?_ ?_
  · rw [rightUnitor_hom_eq]; simp [← J.map_comp]
  · exact mem_comp J (J.imageProperty_map _) (mem_eqToHom J _)

theorem mem_braiding_hom (A B : C) :
    J.imageProperty (BraidedPremonoidalCategory.braiding A B).hom := by
  obtain ⟨X, rfl⟩ := obj_surjective J A
  obtain ⟨Y, rfl⟩ := obj_surjective J B
  rw [braiding_hom_eq]
  exact mem_comp J (mem_eqToHom J _) (mem_comp J (J.imageProperty_map _) (mem_eqToHom J _))

theorem mem_central {X Y : C} {f : X ⟶ Y} (hf : J.imageProperty f) : IsCentral f := by
  obtain ⟨A, B, rfl, rfl, g, rfl⟩ := hf
  exact (isCentral_eqToHom _).comp
    ((FreydCategory.image_central J g).comp (isCentral_eqToHom _))

/-- The image of a strict Freyd inclusion is a premonoidal wide subcategory. -/
instance imageIsPremonoidalSubcategory : IsPremonoidalSubcategory (J.imageProperty) where
  whiskerLeft_mem := by intro Z _ _ _ hf; exact mem_whiskerLeft J Z hf
  whiskerRight_mem := by intro _ _ _ Z hf; exact mem_whiskerRight J hf Z
  associator_hom_mem := mem_associator_hom J
  associator_inv_mem := mem_associator_inv J
  leftUnitor_hom_mem := mem_leftUnitor_hom J
  leftUnitor_inv_mem := mem_leftUnitor_inv J
  rightUnitor_hom_mem := mem_rightUnitor_hom J
  rightUnitor_inv_mem := mem_rightUnitor_inv J

instance imageIsSymmetricSubcategory : IsSymmetricSubcategory (J.imageProperty) where
  braiding_hom_mem := mem_braiding_hom J

/-- **Pure morphisms are central.**  The image of a Freyd inclusion consists of central
morphisms, so it is a symmetric monoidal wide subcategory. -/
instance imageIsCentralSubcategory : IsCentralSubcategory (J.imageProperty) where
  central := by intro _ _ _ hf; exact mem_central J hf

/-- Every pure morphism into a tensor is `J.map` of a morphism of `V`, up to the strictness
equality. -/
theorem exists_map_of_mem_tensor {T X Y : V} {h : J.obj T ⟶ J.obj X ⊗ J.obj Y}
    (hh : J.imageProperty h) :
    ∃ h' : T ⟶ X ⊗ Y, h = J.map h' ≫ eqToHom (obj_tensor (J := J) X Y) := by
  obtain ⟨h', hh'⟩ := J.imageProperty_of_injective (obj_injective J)
    (f := h ≫ eqToHom (obj_tensor (J := J) X Y).symm)
    (mem_comp J hh (mem_eqToHom J _))
  exact ⟨h', by rw [← hh']; simp⟩

/-! #### The image is cartesian when `J` is faithful

Faithfulness is exactly the statement that `V` really *is* a subcategory of `C` rather than
merely mapping into it; without it the universal property of the product can fail to transfer. -/

section Faithful

variable [J.Faithful]

instance imageIsSemiCartesianSubcategory :
    IsSemiCartesianSubcategory (J.imageProperty) where
  existsUnique_toUnit A := by
    obtain ⟨X, rfl⟩ := obj_surjective J A
    refine ⟨J.map (CartesianMonoidalCategory.toUnit X) ≫ eqToHom (obj_unit (J := J)),
      mem_comp J (J.imageProperty_map _) (mem_eqToHom J _), ?_⟩
    rintro f ⟨A', B', hA, hB, g, rfl⟩
    obtain rfl := obj_injective J hA
    obtain rfl := obj_injective J (hB.trans (obj_unit (J := J)).symm)
    rw [Subsingleton.elim g (CartesianMonoidalCategory.toUnit _)]
    simp

theorem image_toUnit_eq (X : V) :
    IsSemiCartesianSubcategory.toUnit (J.imageProperty) (J.obj X) =
      J.map (CartesianMonoidalCategory.toUnit X) ≫ eqToHom (obj_unit (J := J)) :=
  (IsSemiCartesianSubcategory.toUnit_unique _
    (mem_comp J (J.imageProperty_map _) (mem_eqToHom J _))).symm

theorem image_fst_eq (X Y : V) :
    IsSemiCartesianSubcategory.fst (J.imageProperty) (J.obj X) (J.obj Y) =
      eqToHom (obj_tensor (J := J) X Y).symm ≫ J.map (CartesianMonoidalCategory.fst X Y) := by
  have hfst : CartesianMonoidalCategory.fst X Y
      = X ◁ CartesianMonoidalCategory.toUnit Y ≫ (ρ_ X).hom :=
    CartesianMonoidalCategory.fst_def X Y
  rw [IsSemiCartesianSubcategory.fst, image_toUnit_eq, hfst, J.map_comp,
    PremonoidalCategory.whiskerLeft_comp, whiskerLeft_map_eq,
    PremonoidalCategory.whiskerLeft_eqToHom, rightUnitor_hom_eq]
  simp

theorem image_snd_eq (X Y : V) :
    IsSemiCartesianSubcategory.snd (J.imageProperty) (J.obj X) (J.obj Y) =
      eqToHom (obj_tensor (J := J) X Y).symm ≫ J.map (CartesianMonoidalCategory.snd X Y) := by
  have hsnd : CartesianMonoidalCategory.snd X Y
      = CartesianMonoidalCategory.toUnit X ▷ Y ≫ (λ_ Y).hom :=
    CartesianMonoidalCategory.snd_def X Y
  rw [IsSemiCartesianSubcategory.snd, image_toUnit_eq, hsnd, J.map_comp,
    PremonoidalCategory.comp_whiskerRight, whiskerRight_map_eq,
    PremonoidalCategory.whiskerRight_eqToHom, leftUnitor_hom_eq]
  simp

/-- **The image of a faithful strict Freyd inclusion is cartesian.**  The premonoidal tensor of
`C` restricts to a categorical product on the pure morphisms. -/
instance imageIsCartesianSubcategory : IsCartesianSubcategory (J.imageProperty) where
  existsUnique_lift := by
    intro T A B f g hf hg
    obtain ⟨T', rfl⟩ := obj_surjective J T
    obtain ⟨X, rfl⟩ := obj_surjective J A
    obtain ⟨Y, rfl⟩ := obj_surjective J B
    obtain ⟨f', rfl⟩ := J.imageProperty_of_injective (obj_injective J) hf
    obtain ⟨g', rfl⟩ := J.imageProperty_of_injective (obj_injective J) hg
    refine ⟨⟨J.map (CartesianMonoidalCategory.lift f' g') ≫ eqToHom (obj_tensor (J := J) X Y),
      mem_comp J (J.imageProperty_map _) (mem_eqToHom J _)⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [image_fst_eq]; simp [← J.map_comp]
    · rw [image_snd_eq]; simp [← J.map_comp]
    · rintro ⟨h, hh⟩ ⟨e₁, e₂⟩
      obtain ⟨h', rfl⟩ := exists_map_of_mem_tensor J hh
      apply Subtype.ext
      simp only
      congr 1
      refine congrArg J.map ?_
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · rw [CartesianMonoidalCategory.lift_fst]
        refine J.map_injective ?_
        rw [J.map_comp]
        rw [image_fst_eq] at e₁
        simpa using e₁
      · rw [CartesianMonoidalCategory.lift_snd]
        refine J.map_injective ?_
        rw [J.map_comp]
        rw [image_snd_eq] at e₂
        simpa using e₂

end Faithful

end FreydCategory


end CategoryTheory
