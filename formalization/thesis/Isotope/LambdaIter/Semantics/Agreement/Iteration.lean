import Isotope.LambdaIter.Semantics.Agreement

universe v

namespace Isotope.LambdaIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits

variable {m : Type v → Type v} [Monad m] [LawfulMonad m]

abbrev typeJ := Kleisli.Adjunction.toKleisli (ofTypeMonad m)

theorem splitMapCoprod_coprodIsoSum (X Y : Type v) :
    splitMapCoprod (typeJ (m := m)) X Y ≫
        (Kleisli.Type.coprodIsoSum m ((typeJ (m := m)).obj X)
          ((typeJ (m := m)).obj Y)).hom =
      (typeJ (m := m)).map (Types.binaryCoproductIso X Y).hom := by
  rw [← cancel_epi (coprodComparison (typeJ (m := m)) X Y)]
  apply coprod.hom_ext
  · simp only [Category.assoc, coprodComparison_inl_assoc, splitMapCoprod,
      map_inl_inv_coprodComparison_assoc]
    rw [Kleisli.Type.inl_coprodIsoSum_hom]
    apply Kleisli.hom_ext
    funext x
    simpa [Kleisli.Type.binaryCofan, Kleisli.Adjunction.toKleisli] using
      congrFun (Types.binaryCoproductIso_inl_comp_hom X Y) x
  · simp only [Category.assoc, coprodComparison_inr_assoc, splitMapCoprod,
      map_inr_inv_coprodComparison_assoc]
    rw [Kleisli.Type.inr_coprodIsoSum_hom]
    apply Kleisli.hom_ext
    funext y
    simpa [Kleisli.Type.binaryCofan, Kleisli.Adjunction.toKleisli] using
      congrFun (Types.binaryCoproductIso_inr_comp_hom X Y) y

theorem routeContext_hom (R B A : Type v) :
    (typeJ (m := m)).map (DistributiveTensor.leftIso R B A).inv ≫
        splitMapCoprod (typeJ (m := m)) (R × B) (R × A) ≫
          (Kleisli.Type.coprodIsoSum m ((typeJ (m := m)).obj (R × B))
            ((typeJ (m := m)).obj (R × A))).hom =
      (typeJ (m := m)).map
        ((DistributiveTensor.leftIso R B A).inv ≫
          (Types.binaryCoproductIso (R × B) (R × A)).hom) := by
  rw [splitMapCoprod_coprodIsoSum]
  exact ((typeJ (m := m)).map_comp _ _).symm

theorem routeContext_apply (R B A : Type v) (r : R) (s : B ⨿ A) :
    (((DistributiveTensor.leftIso R B A).inv ≫
      (Types.binaryCoproductIso (R × B) (R × A)).hom) (r, s)) =
      match (Types.binaryCoproductIso B A).hom s with
      | .inl b => .inl (r, b)
      | .inr a => .inr (r, a) := by
  cases h : (Types.binaryCoproductIso B A).hom s with
  | inl b =>
      have hs : s = (Types.binaryCoproductIso B A).inv (.inl b) := by
        calc
          s = (Types.binaryCoproductIso B A).inv
              ((Types.binaryCoproductIso B A).hom s) := by simp
          _ = _ := by rw [h]
      subst s
      have hi := congrFun (Types.binaryCoproductIso_inl_comp_inv B A) b
      change (Types.binaryCoproductIso B A).inv (.inl b) = _ at hi
      rw [hi]
      have hd' : (DistributiveTensor.leftIso R B A).hom
          ((Types.binaryCoproductIso (R × B) (R × A)).inv (.inl (r, b))) =
          (r, ((coprod.inl : B ⟶ (B ⨿ A : Type v)) : B → _) b) := by
        simpa [DistributiveTensor.leftIso, Category.comp_apply] using
          congrFun (DistributiveTensor.inl_leftHom R B A) (r, b)
      rw [← hd']
      simp
  | inr a =>
      have hs : s = (Types.binaryCoproductIso B A).inv (.inr a) := by
        calc
          s = (Types.binaryCoproductIso B A).inv
              ((Types.binaryCoproductIso B A).hom s) := by simp
          _ = _ := by rw [h]
      subst s
      have hi := congrFun (Types.binaryCoproductIso_inr_comp_inv B A) a
      change (Types.binaryCoproductIso B A).inv (.inr a) = _ at hi
      rw [hi]
      have hd' : (DistributiveTensor.leftIso R B A).hom
          ((Types.binaryCoproductIso (R × B) (R × A)).inv (.inr (r, a))) =
          (r, ((coprod.inr : A ⟶ (B ⨿ A : Type v)) : A → _) a) := by
        simpa [DistributiveTensor.leftIso, Category.comp_apply] using
          congrFun (DistributiveTensor.inr_leftHom R B A) (r, a)
      rw [← hd']
      simp

@[simp] private theorem types_fst_apply {X Y : Type v} (p : X × Y) :
    CartesianMonoidalCategory.fst X Y p = p.1 := by rfl

@[simp] private theorem typeJ_tensorIso_hom_of (X Y : Type v) (p : X × Y) :
    (Functor.StrongPremonoidal.tensorIso (J := typeJ (m := m)) X Y).hom.of p =
      (pure p : m _) := rfl

@[simp] private theorem typeJ_tensorIso_inv_of (X Y : Type v) (p : X × Y) :
    (Functor.StrongPremonoidal.tensorIso (J := typeJ (m := m)) X Y).inv.of p =
      (pure p : m _) := rfl

theorem contextualBody_of {R A B : Type v}
    (body : (typeJ (m := m)).obj (R × A) ⟶
      (typeJ (m := m)).obj (B ⨿ A : Type v)) (r : R) (a : A) :
    ((typeJ (m := m)).map (CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.fst R A) (𝟙 (R × A))) ≫
        retainLeft (typeJ (m := m)) body ≫
        (typeJ (m := m)).map (DistributiveTensor.leftIso R B A).inv ≫
        splitMapCoprod (typeJ (m := m)) (R × B) (R × A) ≫
        (Kleisli.Type.coprodIsoSum m ((typeJ (m := m)).obj (R × B))
          ((typeJ (m := m)).obj (R × A))).hom).of (r, a) =
      Isotope.Elgot.kcomp (m := m) body.of (fun s =>
        (pure (match (Types.binaryCoproductIso B A).hom s with
          | .inl b => Sum.inl (r, b)
          | .inr a' => Sum.inr (r, a')) : m ((R × B) ⊕ (R × A)))) (r, a) := by
  simp only [Category.assoc]
  rw [routeContext_hom]
  simp [retainLeft, PremonoidalCategory.leftTensor,
    Kleisli.Type.comp_of_eq_kcomp, Kleisli.whiskerLeft_of,
    typeMonadStrength, ofTypeMonadStrong, Isotope.Elgot.kcomp,
    Isotope.Elgot.liftPure, joinM, bind_assoc, routeContext_apply]
  congr 1
  funext s
  change (((DistributiveTensor.leftIso R B A).inv ≫
    (Types.binaryCoproductIso (R × B) (R × A)).hom) (r, s)) = _
  rw [routeContext_apply R B A r s]
  cases (Types.binaryCoproductIso B A).hom s <;> rfl

theorem contextualLoop_of [Isotope.Elgot.Iterate m] [Isotope.Elgot.LawfulElgotMonad m]
    {R A B : Type v}
    (body : (typeJ (m := m)).obj (R × A) ⟶
      (typeJ (m := m)).obj (B ⨿ A : Type v)) (r : R) (a : A) :
    (contextualLoop (typeJ (m := m)) body).of (r, a) =
      Isotope.Elgot.iter (m := m) (fun a =>
        Isotope.Elgot.kcomp (m := m) body.of (fun s =>
          (pure ((Types.binaryCoproductIso B A).hom s) : m (B ⊕ A))) (r, a)) a := by
  unfold contextualLoop
  rw [Kleisli.Type.comp_of_eq_kcomp, Kleisli.Type.iterate_of]
  let q : A → m (B ⊕ A) := fun x =>
    Isotope.Elgot.kcomp (m := m) body.of (fun s =>
      (pure ((Types.binaryCoproductIso B A).hom s) : m (B ⊕ A))) (r, x)
  let F : R × A → m ((R × B) ⊕ (R × A)) :=
      (((typeJ (m := m)).map (CartesianMonoidalCategory.lift
            (CartesianMonoidalCategory.fst R A) (𝟙 (R × A))) ≫
          retainLeft (typeJ (m := m)) body ≫
          (typeJ (m := m)).map (DistributiveTensor.leftIso R B A).inv ≫
          splitMapCoprod (typeJ (m := m)) (R × B) (R × A)) ≫
        (Kleisli.Type.coprodIsoSum m ((typeJ (m := m)).obj (R × B))
          ((typeJ (m := m)).obj (R × A))).hom).of
  have hb (x : A) : F (r, x) = q x >>= Sum.elim
      (fun b => (pure (Sum.inl (r, b)) : m _))
      (fun a' => (pure (Sum.inr (r, a')) : m _)) := by
    calc
      _ = Isotope.Elgot.kcomp (m := m) body.of (fun s =>
          (pure (match (Types.binaryCoproductIso B A).hom s with
            | .inl b => Sum.inl (r, b)
            | .inr a' => Sum.inr (r, a')) : m _)) (r, x) := by
        simpa only [F, Category.assoc] using contextualBody_of body r x
      _ = _ := by
        simp [q, Isotope.Elgot.kcomp]
        rw [← bind_pure_comp]
        congr 1
        funext s
        cases (Types.binaryCoproductIso B A).hom s <;> rfl
  let g : A → m ((R × B) ⊕ A) :=
    Isotope.Elgot.mapReturn (m := m) q
      (Isotope.Elgot.liftPure (m := m) (Prod.mk r))
  have comm : Isotope.Elgot.kcomp (m := m) g
        (Isotope.Elgot.liftPure (m := m) (Sum.map id (Prod.mk r))) =
      Isotope.Elgot.kcomp (m := m)
        (Isotope.Elgot.liftPure (m := m) (Prod.mk r)) F := by
    funext x
    simp only [Isotope.Elgot.kcomp, Isotope.Elgot.liftPure,
      Function.comp_apply, pure_bind]
    rw [hb]
    simp [g, Isotope.Elgot.mapReturn, Isotope.Elgot.liftPure]
    congr 1
    funext s
    cases s <;> simp
  have hu := Isotope.Elgot.LawfulElgotMonad.uniformity (m := m)
    g F (Prod.mk r) comm
  have hn := Isotope.Elgot.LawfulElgotMonad.naturality (m := m) q
    (Isotope.Elgot.liftPure (m := m) (Prod.mk r))
  change Isotope.Elgot.kcomp (m := m) (Isotope.Elgot.iter (m := m) F)
      (Isotope.Elgot.liftPure (m := m) Prod.snd) (r, a) = _
  calc
    _ = Isotope.Elgot.kcomp (m := m) (Isotope.Elgot.iter (m := m) g)
        (Isotope.Elgot.liftPure (m := m) Prod.snd) a := by
      rw [hu]
      simp [Isotope.Elgot.kcomp, Isotope.Elgot.liftPure, Function.comp_def]
    _ = Isotope.Elgot.kcomp (m := m)
        (Isotope.Elgot.kcomp (m := m) (Isotope.Elgot.iter (m := m) q)
          (Isotope.Elgot.liftPure (m := m) (Prod.mk r)))
        (Isotope.Elgot.liftPure (m := m) Prod.snd) a := by rw [hn]
    _ = Isotope.Elgot.iter (m := m) q a := by
      simp [Isotope.Elgot.kcomp, Isotope.Elgot.liftPure, Function.comp_def]
    _ = _ := rfl

end Isotope.LambdaIter.Semantics.Categorical
