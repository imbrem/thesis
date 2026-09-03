import Isotope.CategoryTheory.Freyd.Central
import Isotope.LambdaIter.Subtyping.Semantics.Categorical

/-!
# The combinator algebra of a Freyd category

The syntactic axiom schemes of lambda-iter never mention `extend`, `bind`,
`pair`, `caseWithContext` or `abort` directly; they mention terms.  But every
reduction of a scheme passes through equations between those combinators, and
this file establishes them once, in an arbitrary Freyd category, before any
syntax is involved.

Three families appear:

* **naturality in the environment**: a value morphism reindexing the
  environment slides through `extend`/`bind`.  This needs only
  `FreydCategory.image_central`.
* **naturality in the value**: a value morphism applied to the result of the
  bound computation can be moved into the continuation.
* **eta**: `extend J f ≫ J.map (snd _ _) = f`, the semantic content of the
  `let` eta rule.  This is the one law that needs the coherence isomorphisms of
  `J` to be central (`Functor.StrongPremonoidalCentral`), because it must slide
  an arbitrary computation past the composite `J.map (toUnit R) ≫ unitIso.inv`.

The distributive section adds the corresponding laws for `caseWithContext`:
its two beta rules, its eta rule, and its naturality in the environment.  It
records `splitMapCoprod_comp_desc_map`, which says that splitting a pure
coproduct and descending two value branches stays pure.  (`TwoPoint.lean`
already has the same statement under the name `splitMapCoprod_desc_map`, but
only for a *strict* premonoidal `J`; the version here drops that hypothesis and
should replace it in an integration pass.)
-/

universe v₁ v₂ u₁ u₂ u₃

namespace Isotope.LambdaIter.Subtyping.Semantics.Categorical

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory

section Freyd

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  (J : Functor V C) [FreydCategory J]

/-- A `bind` whose bound computation is pure is a single value morphism:
`extend` of a value map is the cartesian pairing with the identity. -/
theorem extend_map {R A : V} (u : R ⟶ A) :
    extend J (J.map u) = J.map (CartesianMonoidalCategory.lift (𝟙 R) u) := by
  have hnat := Functor.StrongPremonoidal.tensor_naturality_right (J := J) R u
  have hlift : duplicate R ≫ (R ◁ u) = CartesianMonoidalCategory.lift (𝟙 R) u := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [duplicate]
  simp only [extend, leftTensor, PremonoidalCategory.id_whiskerRight, Category.id_comp,
    Category.assoc, hnat, Iso.inv_hom_id_assoc, ← J.map_comp, hlift]

/-- Naturality of `extend` in the environment: a value reindexing of the
environment slides through, at the cost of reindexing the retained copy. -/
theorem map_comp_extend {R' R A : V} (p : R' ⟶ R) (f : J.obj R ⟶ J.obj A) :
    J.map p ≫ extend J f = extend J (J.map p ≫ f) ≫ J.map (p ⊗ₘ 𝟙 A) := by
  have hp := FreydCategory.image_central J p
  have hpf : J.map p ▷ J.obj R ≫ J.obj R ◁ f = J.obj R' ◁ f ≫ J.map p ▷ J.obj A := by
    simpa [leftTensor, rightTensor] using hp.1 f
  have hpp : J.obj R' ◁ J.map p ≫ J.map p ▷ J.obj R =
      J.map p ▷ J.obj R' ≫ J.obj R ◁ J.map p := by
    simpa [leftTensor, rightTensor] using (hp.2 (J.map p)).symm
  have hdup : p ≫ duplicate R = duplicate R' ≫ (p ⊗ₘ p) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [duplicate]
  have hdiag0 : (J.map p ▷ J.obj R' ≫ J.obj R ◁ J.map p) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) R R).hom =
        (Functor.StrongPremonoidal.tensorIso (J := J) R' R').hom ≫ J.map (p ⊗ₘ p) := by
    rw [Category.assoc, Functor.StrongPremonoidal.tensor_naturality_right (J := J) R p,
      ← Category.assoc, Functor.StrongPremonoidal.tensor_naturality_left (J := J) p R',
      Category.assoc, ← J.map_comp, MonoidalCategory.tensorHom_def]
  have hdiag : J.map (p ⊗ₘ p) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) R R).inv =
        (Functor.StrongPremonoidal.tensorIso (J := J) R' R').inv ≫
          (J.map p ▷ J.obj R' ≫ J.obj R ◁ J.map p) := by
    calc J.map (p ⊗ₘ p) ≫ (Functor.StrongPremonoidal.tensorIso (J := J) R R).inv
        = ((Functor.StrongPremonoidal.tensorIso (J := J) R' R').inv ≫
            (Functor.StrongPremonoidal.tensorIso (J := J) R' R').hom ≫ J.map (p ⊗ₘ p)) ≫
              (Functor.StrongPremonoidal.tensorIso (J := J) R R).inv := by simp
      _ = ((Functor.StrongPremonoidal.tensorIso (J := J) R' R').inv ≫
            ((J.map p ▷ J.obj R' ≫ J.obj R ◁ J.map p) ≫
              (Functor.StrongPremonoidal.tensorIso (J := J) R R).hom)) ≫
              (Functor.StrongPremonoidal.tensorIso (J := J) R R).inv := by rw [hdiag0]
      _ = _ := by simp
  calc J.map p ≫ extend J f
      = J.map (duplicate R') ≫ (J.map (p ⊗ₘ p) ≫
          (Functor.StrongPremonoidal.tensorIso (J := J) R R).inv) ≫
          ((J.obj R ◁ f) ≫ (Functor.StrongPremonoidal.tensorIso (J := J) R A).hom) := by
        rw [extend, leftTensor]
        simp only [PremonoidalCategory.id_whiskerRight, Category.id_comp]
        rw [← Category.assoc, ← J.map_comp, hdup, J.map_comp]
        simp only [Category.assoc]
    _ = J.map (duplicate R') ≫
          (Functor.StrongPremonoidal.tensorIso (J := J) R' R').inv ≫
          (J.obj R' ◁ J.map p ≫ J.map p ▷ J.obj R) ≫
          ((J.obj R ◁ f) ≫ (Functor.StrongPremonoidal.tensorIso (J := J) R A).hom) := by
        rw [hdiag, hpp]
        simp only [Category.assoc]
    _ = J.map (duplicate R') ≫
          (Functor.StrongPremonoidal.tensorIso (J := J) R' R').inv ≫
          (J.obj R' ◁ J.map p) ≫ (J.obj R' ◁ f) ≫
          (J.map p ▷ J.obj A ≫
            (Functor.StrongPremonoidal.tensorIso (J := J) R A).hom) := by
        simp only [Category.assoc]
        rw [reassoc_of% hpf]
    _ = extend J (J.map p ≫ f) ≫ J.map (p ⊗ₘ 𝟙 A) := by
        rw [Functor.StrongPremonoidal.tensor_naturality_left (J := J) p A,
          MonoidalCategory.tensorHom_id]
        simp only [extend, leftTensor, PremonoidalCategory.id_whiskerRight, Category.id_comp,
          PremonoidalCategory.whiskerLeft_comp, Category.assoc]

/-- Naturality of `bind` in the environment. -/
theorem map_comp_bind {R' R A B : V} (p : R' ⟶ R) (f : J.obj R ⟶ J.obj A)
    (g : J.obj (R ⊗ A) ⟶ J.obj B) :
    J.map p ≫ bind J f g = bind J (J.map p ≫ f) (J.map (p ⊗ₘ 𝟙 A) ≫ g) := by
  simp only [bind, ← Category.assoc, map_comp_extend J p f]

/-- Naturality of `extend` in the produced value: a value postprocessing of the
bound computation moves into the retained pair. -/
theorem extend_comp_map {R A A' : V} (f : J.obj R ⟶ J.obj A) (q : A ⟶ A') :
    extend J (f ≫ J.map q) = extend J f ≫ J.map (𝟙 R ⊗ₘ q) := by
  simp only [extend, leftTensor, PremonoidalCategory.id_whiskerRight, Category.id_comp,
    PremonoidalCategory.whiskerLeft_comp, Category.assoc,
    MonoidalCategory.id_tensorHom,
    Functor.StrongPremonoidal.tensor_naturality_right (J := J) R q]

/-- Naturality of `bind` in the produced value. -/
theorem bind_comp_map {R A A' B : V} (f : J.obj R ⟶ J.obj A) (q : A ⟶ A')
    (g : J.obj (R ⊗ A') ⟶ J.obj B) :
    bind J (f ≫ J.map q) g = bind J f (J.map (𝟙 R ⊗ₘ q) ≫ g) := by
  simp only [bind, extend_comp_map, Category.assoc]

/-- Postcomposition is absorbed into the continuation of a `bind`. -/
theorem bind_comp {R A B B' : V} (f : J.obj R ⟶ J.obj A)
    (g : J.obj (R ⊗ A) ⟶ J.obj B) (k : J.obj B ⟶ J.obj B') :
    bind J f g ≫ k = bind J f (g ≫ k) := by
  simp [bind]

/-- A `bind` of two value morphisms is a value morphism. -/
theorem bind_map_map {R A B : V} (u : R ⟶ A) (v : R ⊗ A ⟶ B) :
    bind J (J.map u) (J.map v) =
      J.map (CartesianMonoidalCategory.lift (𝟙 R) u ≫ v) := by
  rw [bind, extend_map, ← J.map_comp]

/-- Sequential pairing of two value morphisms is the cartesian pairing: purity
is preserved by `pair`. -/
theorem pair_map_map {R A B : V} (u : R ⟶ A) (w : R ⟶ B) :
    pair J (J.map u) (J.map w) = J.map (CartesianMonoidalCategory.lift u w) := by
  rw [pair, retainedContext, ← J.map_comp, bind_map_map, bind_map_map]
  congr 1
  apply CartesianMonoidalCategory.hom_ext <;> simp

/-- The computation-side projection determined by a value environment: the
image of the terminal map followed by the inverse unit coherence isomorphism. -/
noncomputable def discard (R : V) : J.obj R ⟶ 𝟙_ C :=
  J.map (CartesianMonoidalCategory.toUnit R) ≫
    (Functor.StrongPremonoidal.unitIso (J := J)).inv

/-- The tensor coherence isomorphism turns the value second projection into
`discard` followed by the left unitor. -/
theorem tensorIso_hom_comp_map_snd (R A : V) :
    (Functor.StrongPremonoidal.tensorIso (J := J) R A).hom ≫
        J.map (CartesianMonoidalCategory.snd R A) =
      discard J R ▷ J.obj A ≫ (λ_ (J.obj A)).hom := by
  have hunit :
      (Functor.StrongPremonoidal.tensorIso (J := J) (𝟙_ V) A).hom ≫
          J.map (λ_ A).hom =
        (Functor.StrongPremonoidal.unitIso (J := J)).inv ▷ J.obj A ≫
          (λ_ (J.obj A)).hom := by
    rw [← Functor.StrongPremonoidal.left_unitality (J := J) A]
    rw [← Category.assoc, ← comp_whiskerRight, Iso.inv_hom_id]
    simp
  have hsnd : CartesianMonoidalCategory.snd R A =
      CartesianMonoidalCategory.toUnit R ▷ A ≫ (λ_ A).hom :=
    (CartesianMonoidalCategory.whiskerRight_toUnit_comp_leftUnitor_hom R A).symm
  rw [hsnd, J.map_comp, ← Category.assoc,
    ← Functor.StrongPremonoidal.tensor_naturality_left (J := J)
      (CartesianMonoidalCategory.toUnit R) A,
    Category.assoc, hunit, discard, comp_whiskerRight, Category.assoc]

variable [Functor.StrongPremonoidalCentral J]

/-- `discard` is central: it is a value image followed by a coherence
isomorphism, and both are central. -/
theorem discard_central (R : V) : IsCentral (discard J R) :=
  (FreydCategory.image_central J _).comp
    (Functor.StrongPremonoidalCentral.unitIso_inv_central J)

/-- **The `let` eta law.**  Running `f` while retaining the environment and
then projecting to the produced value is `f` itself. -/
theorem extend_comp_map_snd {R A : V} (f : J.obj R ⟶ J.obj A) :
    extend J f ≫ J.map (CartesianMonoidalCategory.snd R A) = f := by
  have hcentral := (discard_central J R).1 f
  rw [leftTensor, rightTensor] at hcentral
  calc extend J f ≫ J.map (CartesianMonoidalCategory.snd R A)
      = J.map (duplicate R) ≫
          (Functor.StrongPremonoidal.tensorIso (J := J) R R).inv ≫
          (J.obj R ◁ f) ≫
          ((Functor.StrongPremonoidal.tensorIso (J := J) R A).hom ≫
            J.map (CartesianMonoidalCategory.snd R A)) := by
        simp [extend, leftTensor]
    _ = J.map (duplicate R) ≫
          (Functor.StrongPremonoidal.tensorIso (J := J) R R).inv ≫
          ((J.obj R ◁ f) ≫ discard J R ▷ J.obj A) ≫ (λ_ (J.obj A)).hom := by
        rw [tensorIso_hom_comp_map_snd]; simp
    _ = J.map (duplicate R) ≫
          (Functor.StrongPremonoidal.tensorIso (J := J) R R).inv ≫
          (discard J R ▷ J.obj R) ≫ ((𝟙_ C) ◁ f ≫ (λ_ (J.obj A)).hom) := by
        rw [← hcentral]; simp
    _ = J.map (duplicate R) ≫
          ((Functor.StrongPremonoidal.tensorIso (J := J) R R).inv ≫
            (discard J R ▷ J.obj R) ≫ (λ_ (J.obj R)).hom) ≫ f := by
        rw [PremonoidalCategory.leftUnitor_naturality]; simp
    _ = J.map (duplicate R) ≫ J.map (CartesianMonoidalCategory.snd R R) ≫ f := by
        rw [← tensorIso_hom_comp_map_snd J R R]
        simp
    _ = f := by
        rw [← Category.assoc, ← J.map_comp, duplicate]
        simp

/-- The `let` eta law in `bind` form. -/
theorem bind_map_snd {R A : V} (f : J.obj R ⟶ J.obj A) :
    bind J f (J.map (CartesianMonoidalCategory.snd R A)) = f :=
  extend_comp_map_snd J f

end Freyd

section Distributive

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : Functor V C) [DistributiveFreydCategory J]

/-- A pure left injection is split back to the computation-category left
injection by the inverse coproduct comparison. -/
@[reassoc] theorem map_inl_comp_splitMapCoprod (X Y : V) :
    J.map (coprod.inl : X ⟶ X ⨿ Y) ≫ splitMapCoprod J X Y =
      (coprod.inl : J.obj X ⟶ J.obj X ⨿ J.obj Y) := by
  rw [splitMapCoprod]
  exact map_inl_inv_coprodComparison J

/-- A pure right injection is split back to the computation-category right
injection by the inverse coproduct comparison. -/
@[reassoc] theorem map_inr_comp_splitMapCoprod (X Y : V) :
    J.map (coprod.inr : Y ⟶ X ⨿ Y) ≫ splitMapCoprod J X Y =
      (coprod.inr : J.obj Y ⟶ J.obj X ⨿ J.obj Y) := by
  rw [splitMapCoprod]
  exact map_inr_inv_coprodComparison J

/-- Splitting a pure coproduct and then descending two *value* branches is
again a value morphism.  This is `TwoPoint.splitMapCoprod_desc_map` with the
strictness hypothesis on `J` removed. -/
theorem splitMapCoprod_comp_desc_map {X Y Z : V} (l : X ⟶ Z) (r : Y ⟶ Z) :
    splitMapCoprod J X Y ≫ coprod.desc (J.map l) (J.map r) =
      J.map (coprod.desc l r) := by
  rw [splitMapCoprod, IsIso.inv_comp_eq]
  apply coprod.hom_ext
  · rw [coprod.inl_desc, ← Category.assoc, coprodComparison_inl, ← J.map_comp,
      coprod.inl_desc]
  · rw [coprod.inr_desc, ← Category.assoc, coprodComparison_inr, ← J.map_comp,
      coprod.inr_desc]

/-- **Left case beta.**  A scrutinee that visibly takes the left branch reduces
the case analysis to a `bind` on that branch. -/
theorem caseWithContext_map_inl {R A B D : V} (f : J.obj R ⟶ J.obj A)
    (left : J.obj (R ⊗ A) ⟶ J.obj D) (right : J.obj (R ⊗ B) ⟶ J.obj D) :
    caseWithContext J (f ≫ J.map (coprod.inl : A ⟶ A ⨿ B)) left right =
      bind J f left := by
  have hdist : (𝟙 R ⊗ₘ (coprod.inl : A ⟶ A ⨿ B)) ≫
      (DistributiveTensor.leftIso R A B).inv =
        (coprod.inl : R ⊗ A ⟶ (R ⊗ A) ⨿ (R ⊗ B)) := by
    rw [Iso.comp_inv_eq]
    simp [DistributiveTensor.leftIso, MonoidalCategory.id_tensorHom]
  rw [caseWithContext, bind_comp_map]
  congr 1
  rw [← Category.assoc, ← J.map_comp, hdist, map_inl_comp_splitMapCoprod_assoc,
    coprod.inl_desc]

/-- **Right case beta.** -/
theorem caseWithContext_map_inr {R A B D : V} (f : J.obj R ⟶ J.obj B)
    (left : J.obj (R ⊗ A) ⟶ J.obj D) (right : J.obj (R ⊗ B) ⟶ J.obj D) :
    caseWithContext J (f ≫ J.map (coprod.inr : B ⟶ A ⨿ B)) left right =
      bind J f right := by
  have hdist : (𝟙 R ⊗ₘ (coprod.inr : B ⟶ A ⨿ B)) ≫
      (DistributiveTensor.leftIso R A B).inv =
        (coprod.inr : R ⊗ B ⟶ (R ⊗ A) ⨿ (R ⊗ B)) := by
    rw [Iso.comp_inv_eq]
    simp [DistributiveTensor.leftIso, MonoidalCategory.id_tensorHom]
  rw [caseWithContext, bind_comp_map]
  congr 1
  rw [← Category.assoc, ← J.map_comp, hdist, map_inr_comp_splitMapCoprod_assoc,
    coprod.inr_desc]

/-- Postcomposition is absorbed into both branches of a case analysis. -/
theorem caseWithContext_comp {R A B D D' : V}
    (scrutinee : J.obj R ⟶ J.obj (A ⨿ B))
    (left : J.obj (R ⊗ A) ⟶ J.obj D) (right : J.obj (R ⊗ B) ⟶ J.obj D)
    (k : J.obj D ⟶ J.obj D') :
    caseWithContext J scrutinee left right ≫ k =
      caseWithContext J scrutinee (left ≫ k) (right ≫ k) := by
  simp only [caseWithContext, bind_comp, Category.assoc, ← coprod.desc_comp]

/-- Naturality of case analysis in the environment. -/
theorem map_comp_caseWithContext {R' R A B D : V} (p : R' ⟶ R)
    (scrutinee : J.obj R ⟶ J.obj (A ⨿ B))
    (left : J.obj (R ⊗ A) ⟶ J.obj D) (right : J.obj (R ⊗ B) ⟶ J.obj D) :
    J.map p ≫ caseWithContext J scrutinee left right =
      caseWithContext J (J.map p ≫ scrutinee)
        (J.map (p ⊗ₘ 𝟙 A) ≫ left) (J.map (p ⊗ₘ 𝟙 B) ≫ right) := by
  have hdist : (p ⊗ₘ 𝟙 (A ⨿ B)) ≫ (DistributiveTensor.leftIso R A B).inv =
      (DistributiveTensor.leftIso R' A B).inv ≫
        coprod.map (p ⊗ₘ 𝟙 A) (p ⊗ₘ 𝟙 B) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    apply coprod.hom_ext <;>
      simp [DistributiveTensor.leftIso, MonoidalCategory.tensorHom_def,
        MonoidalCategory.whisker_exchange]
  rw [caseWithContext, caseWithContext, map_comp_bind]
  congr 1
  rw [← Category.assoc, ← J.map_comp, hdist, J.map_comp, Category.assoc]
  congr 1
  rw [splitMapCoprod, splitMapCoprod, ← Category.assoc,
    ← coprodComparison_inv_natural, Category.assoc, coprod.map_desc]

variable [Functor.StrongPremonoidalCentral J]

/-- **Case eta.**  Re-injecting the scrutinee in each branch recovers the
scrutinee. -/
theorem caseWithContext_eta {R A B : V} (f : J.obj R ⟶ J.obj (A ⨿ B)) :
    caseWithContext J f
        (J.map (CartesianMonoidalCategory.snd R A ≫ coprod.inl))
        (J.map (CartesianMonoidalCategory.snd R B ≫ coprod.inr)) = f := by
  have hdesc : (DistributiveTensor.leftIso R A B).inv ≫
      coprod.desc (CartesianMonoidalCategory.snd R A ≫ (coprod.inl : A ⟶ A ⨿ B))
        (CartesianMonoidalCategory.snd R B ≫ coprod.inr) =
      CartesianMonoidalCategory.snd R (A ⨿ B) := by
    rw [Iso.inv_comp_eq]
    apply coprod.hom_ext <;>
      simp [DistributiveTensor.leftIso, ← MonoidalCategory.id_tensorHom]
  rw [caseWithContext, splitMapCoprod_comp_desc_map, ← J.map_comp, hdesc,
    bind_map_snd]

end Distributive

end Isotope.LambdaIter.Subtyping.Semantics.Categorical
