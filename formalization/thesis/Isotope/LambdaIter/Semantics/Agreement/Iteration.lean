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

end Isotope.LambdaIter.Semantics.Categorical
