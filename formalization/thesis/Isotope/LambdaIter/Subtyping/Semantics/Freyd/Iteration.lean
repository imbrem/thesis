import Isotope.LambdaIter.Subtyping.Semantics.Freyd.Combinators

/-!
# The contextual loop of a strong Elgot Freyd category

`Subtyping/Semantics/IterationDiagrams.lean` isolates the four *bare* Elgot
equations — fixpoint, naturality, codiagonal and pure uniformity — and says
explicitly that relating them to the syntax is separate work.  This file is the
first instalment of that work: it gives `contextualLoop`, the
environment-threading wrapper actually used by the `iter` clause of the
denotation, its own algebra.

The two ingredients are `retainLeft`, which runs a computation on the right
factor while retaining a value environment on the left, and the distributor
that routes the retained environment into both exit branches.  Everything here
is proved from `FreydCategory.image_central`, the one-variable naturality of
the tensor coherence isomorphism, and the `ElgotCategory` equations; no new
categorical law is used.
-/

universe v₁ v₂ u₁ u₂

namespace Isotope.LambdaIter.Subtyping.Semantics.Categorical

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]

/-- Naturality of `retainLeft` in the retained environment.  This is the
`retainLeft` counterpart of `map_comp_extend`, and like it uses only
centrality of value images. -/
theorem map_comp_retainLeft {R' R X Y : V} (p : R' ⟶ R) (f : J.obj X ⟶ J.obj Y) :
    J.map (p ⊗ₘ 𝟙 X) ≫ retainLeft J (R := R) f =
      retainLeft J (R := R') f ≫ J.map (p ⊗ₘ 𝟙 Y) := by
  have hp := FreydCategory.image_central J p
  have hpf : J.map p ▷ J.obj X ≫ J.obj R ◁ f = J.obj R' ◁ f ≫ J.map p ▷ J.obj Y := by
    simpa [leftTensor, rightTensor] using hp.1 f
  have hinv : J.map (p ▷ X) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) R X).inv =
        (Functor.StrongPremonoidal.tensorIso (J := J) R' X).inv ≫
          J.map p ▷ J.obj X := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact (Functor.StrongPremonoidal.tensor_naturality_left (J := J) p X).symm
  rw [MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_id, retainLeft,
    retainLeft, leftTensor, leftTensor]
  simp only [PremonoidalCategory.id_whiskerRight, Category.id_comp, Category.assoc]
  rw [← Category.assoc, hinv, Category.assoc, reassoc_of% hpf,
    Functor.StrongPremonoidal.tensor_naturality_left (J := J) p Y]

/-- A value postprocessing of the retained computation moves outside
`retainLeft`. -/
theorem retainLeft_comp_map {R X Y Y' : V} (f : J.obj X ⟶ J.obj Y) (q : Y ⟶ Y') :
    retainLeft J (R := R) (f ≫ J.map q) =
      retainLeft J (R := R) f ≫ J.map (𝟙 R ⊗ₘ q) := by
  simp only [retainLeft, leftTensor, PremonoidalCategory.id_whiskerRight,
    Category.id_comp, PremonoidalCategory.whiskerLeft_comp, Category.assoc,
    MonoidalCategory.id_tensorHom,
    Functor.StrongPremonoidal.tensor_naturality_right (J := J) R q]

/-- A value preprocessing of the retained computation moves outside
`retainLeft`. -/
theorem map_comp_retainLeft_body {R X' X Y : V} (u : X' ⟶ X)
    (f : J.obj X ⟶ J.obj Y) :
    retainLeft J (R := R) (J.map u ≫ f) =
      J.map (𝟙 R ⊗ₘ u) ≫ retainLeft J (R := R) f := by
  have hnat : J.map (R ◁ u) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) R X).inv =
        (Functor.StrongPremonoidal.tensorIso (J := J) R X').inv ≫
          J.obj R ◁ J.map u := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact (Functor.StrongPremonoidal.tensor_naturality_right (J := J) R u).symm
  rw [MonoidalCategory.id_tensorHom, retainLeft, retainLeft, leftTensor, leftTensor]
  simp only [PremonoidalCategory.id_whiskerRight, Category.id_comp,
    PremonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% hnat]

/-- The loop body that `contextualLoop` iterates: duplicate the environment,
run the body on the retained copy, and split the result along the
distributor. -/
noncomputable def contextualBody {R A B : V}
    (body : J.obj (R ⊗ A) ⟶ J.obj (B ⨿ A)) :
    J.obj (R ⊗ A) ⟶ J.obj (R ⊗ B) ⨿ J.obj (R ⊗ A) :=
  J.map (CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.fst R A) (𝟙 (R ⊗ A))) ≫
    retainLeft J body ≫
    J.map (DistributiveTensor.leftIso R B A).inv ≫
    splitMapCoprod J (R ⊗ B) (R ⊗ A)

theorem contextualLoop_eq {R A B : V} (body : J.obj (R ⊗ A) ⟶ J.obj (B ⨿ A)) :
    contextualLoop J body =
      iterate (contextualBody J body) ≫ J.map (CartesianMonoidalCategory.snd R B) :=
  rfl

/-- The contextual loop is a bare iteration whose exit branch already discards
the retained environment.  This is the form in which the Elgot equations can be
applied to it. -/
theorem contextualLoop_eq_iterate {R A B : V}
    (body : J.obj (R ⊗ A) ⟶ J.obj (B ⨿ A)) :
    contextualLoop J body =
      iterate (contextualBody J body ≫
        coprod.map (J.map (CartesianMonoidalCategory.snd R B))
          (𝟙 (J.obj (R ⊗ A)))) :=
  ElgotCategory.naturality _ _

/-- One unfolding of the contextual loop. -/
theorem contextualLoop_fixpoint {R A B : V}
    (body : J.obj (R ⊗ A) ⟶ J.obj (B ⨿ A)) :
    contextualLoop J body =
      contextualBody J body ≫
        coprod.desc (J.map (CartesianMonoidalCategory.snd R B))
          (contextualLoop J body) := by
  conv_lhs => rw [contextualLoop_eq, ElgotCategory.fixpoint]
  rw [contextualLoop_eq, Category.assoc]
  congr 1
  apply coprod.hom_ext <;> simp


/-- Naturality of the contextual loop body in the retained environment. -/
theorem map_comp_contextualBody {R' R A B : V} (p : R' ⟶ R)
    (body : J.obj (R ⊗ A) ⟶ J.obj (B ⨿ A)) :
    contextualBody J (J.map (p ⊗ₘ 𝟙 A) ≫ body) ≫
        coprod.map (J.map (p ⊗ₘ 𝟙 B)) (J.map (p ⊗ₘ 𝟙 A)) =
      J.map (p ⊗ₘ 𝟙 A) ≫ contextualBody J body := by
  have hlift : (p ⊗ₘ 𝟙 A) ≫ CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst R A) (𝟙 (R ⊗ A)) =
      CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst R' A) (𝟙 (R' ⊗ A)) ≫
          ((𝟙 R' ⊗ₘ (p ⊗ₘ 𝟙 A)) ≫ (p ⊗ₘ 𝟙 (R ⊗ A))) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have htail : J.map (DistributiveTensor.leftIso R' B A).inv ≫
      splitMapCoprod J (R' ⊗ B) (R' ⊗ A) ≫
        coprod.map (J.map (p ⊗ₘ 𝟙 B)) (J.map (p ⊗ₘ 𝟙 A)) =
      J.map (p ⊗ₘ 𝟙 (B ⨿ A)) ≫
        J.map (DistributiveTensor.leftIso R B A).inv ≫
          splitMapCoprod J (R ⊗ B) (R ⊗ A) := by
    rw [splitMapCoprod, splitMapCoprod, coprodComparison_inv_natural,
      ← Category.assoc, ← J.map_comp, ← tensor_comp_leftIso_inv, J.map_comp,
      Category.assoc]
  rw [contextualBody, contextualBody, map_comp_retainLeft_body]
  simp only [Category.assoc]
  rw [htail, ← reassoc_of% (map_comp_retainLeft J p body)]
  simp only [← Category.assoc, ← J.map_comp]
  rw [hlift]
  simp only [Category.assoc]

/-- **Naturality of the contextual loop in the environment.**  A value
reindexing of the read-only environment commutes with the loop.  This is the
one place where the Elgot *uniformity* law is needed: the two loops have
different state objects, related by a pure morphism. -/
theorem map_comp_contextualLoop {R' R A B : V} (p : R' ⟶ R)
    (body : J.obj (R ⊗ A) ⟶ J.obj (B ⨿ A)) :
    J.map (p ⊗ₘ 𝟙 A) ≫ contextualLoop J body =
      contextualLoop J (J.map (p ⊗ₘ 𝟙 A) ≫ body) := by
  have hsnd : (p ⊗ₘ 𝟙 B) ≫ CartesianMonoidalCategory.snd R B =
      CartesianMonoidalCategory.snd R' B := by
    simp
  have hcomm :
      (contextualBody J (J.map (p ⊗ₘ 𝟙 A) ≫ body) ≫
          coprod.map (J.map (CartesianMonoidalCategory.snd R' B))
            (𝟙 (J.obj (R' ⊗ A)))) ≫
        coprod.map (𝟙 (J.obj B)) (J.map (p ⊗ₘ 𝟙 A)) =
      J.map (p ⊗ₘ 𝟙 A) ≫
        (contextualBody J body ≫
          coprod.map (J.map (CartesianMonoidalCategory.snd R B))
            (𝟙 (J.obj (R ⊗ A)))) := by
    have hmap : coprod.map (J.map (p ⊗ₘ 𝟙 B)) (J.map (p ⊗ₘ 𝟙 A)) ≫
        coprod.map (J.map (CartesianMonoidalCategory.snd R B))
          (𝟙 (J.obj (R ⊗ A))) =
        coprod.map (J.map (CartesianMonoidalCategory.snd R' B))
          (𝟙 (J.obj (R' ⊗ A))) ≫
          coprod.map (𝟙 (J.obj B)) (J.map (p ⊗ₘ 𝟙 A)) := by
      rw [coprod.map_map, coprod.map_map, ← J.map_comp, hsnd]
      simp
    calc (contextualBody J (J.map (p ⊗ₘ 𝟙 A) ≫ body) ≫
            coprod.map (J.map (CartesianMonoidalCategory.snd R' B))
              (𝟙 (J.obj (R' ⊗ A)))) ≫
          coprod.map (𝟙 (J.obj B)) (J.map (p ⊗ₘ 𝟙 A))
        = contextualBody J (J.map (p ⊗ₘ 𝟙 A) ≫ body) ≫
            (coprod.map (J.map (p ⊗ₘ 𝟙 B)) (J.map (p ⊗ₘ 𝟙 A)) ≫
              coprod.map (J.map (CartesianMonoidalCategory.snd R B))
                (𝟙 (J.obj (R ⊗ A)))) := by
          rw [hmap, Category.assoc]
      _ = (contextualBody J (J.map (p ⊗ₘ 𝟙 A) ≫ body) ≫
            coprod.map (J.map (p ⊗ₘ 𝟙 B)) (J.map (p ⊗ₘ 𝟙 A))) ≫
              coprod.map (J.map (CartesianMonoidalCategory.snd R B))
                (𝟙 (J.obj (R ⊗ A))) := (Category.assoc _ _ _).symm
      _ = (J.map (p ⊗ₘ 𝟙 A) ≫ contextualBody J body) ≫
              coprod.map (J.map (CartesianMonoidalCategory.snd R B))
                (𝟙 (J.obj (R ⊗ A))) := by
          rw [map_comp_contextualBody]
      _ = _ := Category.assoc _ _ _
  rw [contextualLoop_eq_iterate, contextualLoop_eq_iterate]
  exact (ElgotFreydCategory.pure_uniformity J _ _ (p ⊗ₘ 𝟙 A) hcomm).symm

end Isotope.LambdaIter.Subtyping.Semantics.Categorical
