import Isotope.LambdaIter.Subtyping.Semantics.Agreement.Iteration

namespace Isotope.LambdaIter.Subtyping.Semantics

open CategoryTheory CategoryTheory.Limits Isotope.Elgot

universe v

namespace Categorical

variable {m : Type v → Type v} [Monad m] [LawfulMonad m]

private abbrev J := Kleisli.Adjunction.toKleisli (CategoryTheory.ofTypeMonad m)

@[simp] private theorem types_fst_apply {X Y : Type v} (p : X × Y) :
    CartesianMonoidalCategory.fst X Y p = p.1 := by rfl

@[simp] private theorem types_snd_apply {X Y : Type v} (p : X × Y) :
    CartesianMonoidalCategory.snd X Y p = p.2 := by rfl

@[simp] theorem typeJ_tensorIso_hom_of (X Y : Type v) (p : X × Y) :
    (Functor.StrongPremonoidal.tensorIso (J := J (m := m)) X Y).hom.of p =
      (pure p : m _) := rfl

@[simp] theorem typeJ_tensorIso_inv_of (X Y : Type v) (p : X × Y) :
    (Functor.StrongPremonoidal.tensorIso (J := J (m := m)) X Y).inv.of p =
      (pure p : m _) := rfl

theorem bind_of {R A B : Type v}
    (f : (J (m := m)).obj R ⟶ (J (m := m)).obj A)
    (g : (J (m := m)).obj (R × A) ⟶ (J (m := m)).obj B) (r : R) :
    (Categorical.bind (J (m := m)) f g).of r =
      Isotope.Elgot.kcomp (m := m) f.of (fun a => g.of (r, a)) r := by
  simp [Categorical.bind, Categorical.extend, Categorical.duplicate,
    PremonoidalCategory.leftTensor,
    Kleisli.Adjunction.toKleisli, CategoryTheory.Kleisli.whiskerLeft_of,
    CategoryTheory.typeMonadStrength, CategoryTheory.ofTypeMonadStrong,
    Functor.StrongPremonoidal.tensorIso,
    typeJ_tensorIso_hom_of, typeJ_tensorIso_inv_of,
    Isotope.Elgot.kcomp, joinM, bind_assoc]

theorem pair_of {R A B : Type v}
    (f : (J (m := m)).obj R ⟶ (J (m := m)).obj A)
    (g : (J (m := m)).obj R ⟶ (J (m := m)).obj B) (r : R) :
    (Categorical.pair (J (m := m)) f g).of r =
      Isotope.Elgot.kcomp (m := m) f.of (fun a =>
        Isotope.Elgot.kcomp (m := m) g.of (fun b => pure (a, b)) r) r := by
  unfold Categorical.pair
  rw [bind_of]
  apply congrArg (fun k => Isotope.Elgot.kcomp (m := m) f.of k r)
  funext a
  rw [bind_of]
  simp [Categorical.retainedContext,
    CategoryTheory.Kleisli.Type.comp_of_eq_kcomp,
    Isotope.Elgot.kcomp, joinM, bind_assoc,
    Kleisli.Adjunction.toKleisli, Functor.StrongPremonoidal.tensorIso]

theorem comp_map_of {R A B : Type v}
    (f : (J (m := m)).obj R ⟶ (J (m := m)).obj A) (g : A → B) (r : R) :
    (f ≫ (J (m := m)).map g).of r =
      Isotope.Elgot.kcomp (m := m) f.of (Isotope.Elgot.liftPure (m := m) g) r := by
  rw [CategoryTheory.Kleisli.Type.comp_of_eq_kcomp]
  rfl

theorem map_of {A B : Type v} (f : A → B) (a : A) :
    ((J (m := m)).map f).of a = (pure (f a) : m B) := rfl

theorem caseWithContext_of {R A B D : Type v}
    (scrutinee : (J (m := m)).obj R ⟶ (J (m := m)).obj (A ⨿ B : Type v))
    (left : (J (m := m)).obj (R × A) ⟶ (J (m := m)).obj D)
    (right : (J (m := m)).obj (R × B) ⟶ (J (m := m)).obj D) (r : R) :
    (Categorical.caseWithContext (J (m := m)) scrutinee left right).of r =
      Isotope.Elgot.kcomp (m := m) scrutinee.of (fun s =>
        match (Types.binaryCoproductIso A B).hom s with
        | .inl a => left.of (r, a)
        | .inr b => right.of (r, b)) r := by
  unfold Categorical.caseWithContext
  rw [bind_of]
  apply congrArg (fun k => Isotope.Elgot.kcomp (m := m) scrutinee.of k r)
  funext s
  have harrow :
      (J (m := m)).map (DistributiveTensor.leftIso R A B).inv ≫
          Categorical.splitMapCoprod (J (m := m)) (R × A) (R × B) ≫
            coprod.desc left right =
        (J (m := m)).map
            ((DistributiveTensor.leftIso R A B).inv ≫
              (Types.binaryCoproductIso (R × A) (R × B)).hom) ≫
          Kleisli.Hom.mk (Sum.elim left.of right.of) := by
    calc
      _ = (J (m := m)).map (DistributiveTensor.leftIso R A B).inv ≫
          Categorical.splitMapCoprod (J (m := m)) (R × A) (R × B) ≫
            ((Kleisli.Type.coprodIsoSum m _ _).hom ≫
              Kleisli.Hom.mk (Sum.elim left.of right.of)) := by
            rw [CategoryTheory.Kleisli.Type.coprodIsoSum_hom_sumElim (m := m)]
      _ = ((J (m := m)).map (DistributiveTensor.leftIso R A B).inv ≫
          Categorical.splitMapCoprod (J (m := m)) (R × A) (R × B) ≫
            (Kleisli.Type.coprodIsoSum m _ _).hom) ≫
              Kleisli.Hom.mk (Sum.elim left.of right.of) := by simp only [Category.assoc]
      _ = _ := by rw [routeContext_hom]; rfl
  change ((J (m := m)).map (DistributiveTensor.leftIso R A B).inv ≫
      Categorical.splitMapCoprod (J (m := m)) (R × A) (R × B) ≫
        coprod.desc left right).of (r, s) = _
  rw [harrow]
  rw [CategoryTheory.Kleisli.Type.comp_of_eq_kcomp]
  simp [Kleisli.Adjunction.toKleisli, Isotope.Elgot.kcomp, joinM]
  change Sum.elim left.of right.of
      (((DistributiveTensor.leftIso R A B).inv ≫
        (Types.binaryCoproductIso (R × A) (R × B)).hom) (r, s)) = _
  rw [routeContext_apply]
  cases (Types.binaryCoproductIso A B).hom s <;> rfl

theorem abort_of {R E A : Type v} (emptyEquiv : E ≃ Empty)
    (f : (J (m := m)).obj R ⟶ (J (m := m)).obj E) (r : R) :
    (f ≫ (J (m := m)).map (fun z => Empty.elim (emptyEquiv z))).of r =
      Isotope.Elgot.kcomp (m := m) f.of
        (fun z => (pure (Empty.elim (emptyEquiv z)) : m A)) r := by
  exact comp_map_of f (fun z => Empty.elim (emptyEquiv z)) r

end Categorical

end Isotope.LambdaIter.Subtyping.Semantics
