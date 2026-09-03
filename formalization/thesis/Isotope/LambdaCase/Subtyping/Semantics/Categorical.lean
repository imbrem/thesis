import Isotope.LambdaCase.Subtyping.Typing
import Isotope.LambdaIter.Subtyping.Semantics.Categorical

/-! # Distributive Freyd semantics of lambda-case -/

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Isotope.LambdaCase.Subtyping.Semantics.Categorical

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.PremonoidalCategory
open Isotope.LambdaIter.Subtyping.Semantics.Categorical
open scoped MonoidalCategory

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : Functor V C) [DistributiveFreydCategory J]
  {τ : Type u₃} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
  (M : TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type*} [LambdaIter.HasTy Φ τ] [InstructionModel J M Φ]

/-- Reassociate an environment extended by a pair into one extended by its components. -/
def envPairHom (Γ : Ctx ν τ) {n : Nat}
    (β : LocallyNameless.BoundCtx τ n) (A B : τ) :
    envObj M Γ β ⊗ (M.obj A ⊗ M.obj B) ⟶
      envObj M Γ (.snoc (.snoc β A) B) :=
  (α_ (ctxObj M Γ) (boundObj M β) (M.obj A ⊗ M.obj B)).hom ≫
    ctxObj M Γ ◁ (α_ (boundObj M β) (M.obj A) (M.obj B)).inv

/-- Lambda-case denotation in a distributive Freyd category.  In contrast to
lambda-iter, neither `Iteration` nor any Elgot law occurs in the assumptions. -/
noncomputable def denote : {Γ : Ctx ν τ} → {n : Nat} →
    {β : LocallyNameless.BoundCtx τ n} →
    {t : LocallyNameless.Tm ν Φ n} → {A : τ} →
    LocallyNameless.HasType Φ Γ β t A →
      (J.obj (envObj M Γ β) ⟶ J.obj (M.obj A))
  | _, _, _, _, _, .fv h => J.map (freeLookup M _ h)
  | _, _, _, _, _, .bv => J.map (boundVar M _)
  | _, _, _, _, _, .op ha => denote ha ≫ InstructionModel.denote _
  | Γ, _, β, _, _, .let₁ ha hb => bind J (denote ha) <|
      J.map (envSnocIso M Γ β _).hom ≫ denote hb
  | _, _, _, _, _, .unit =>
      J.map (CartesianMonoidalCategory.toUnit _ ≫ M.unitIso.inv)
  | _, _, _, _, _, .pair ha hb =>
      pair J (denote ha) (denote hb) ≫ J.map (M.tensorIso _ _).inv
  | Γ, _, β, _, _, .let₂ ha hc => bind J (denote ha) <|
      J.map ((𝟙 _) ⊗ₘ (M.tensorIso _ _).hom) ≫
        J.map (envPairHom M Γ β _ _) ≫ denote hc
  | _, _, _, _, _, .inl ha =>
      denote ha ≫ J.map (coprod.inl ≫ (M.coprodIso _ _).inv)
  | _, _, _, _, _, .inr hb =>
      denote hb ≫ J.map (coprod.inr ≫ (M.coprodIso _ _).inv)
  | Γ, _, β, _, _, .case he hl hr =>
      caseWithContext J (denote he ≫ J.map (M.coprodIso _ _).hom)
        (J.map (envSnocIso M Γ β _).hom ≫ denote hl)
        (J.map (envSnocIso M Γ β _).hom ≫ denote hr)
  | _, _, _, _, _, .abort ha => abort J M (denote ha)
  | _, _, _, _, _, .sub ha d => denote ha ≫ J.map (M.subty d)

end Isotope.LambdaCase.Subtyping.Semantics.Categorical

namespace Isotope.LambdaCase.Subtyping.Semantics.Categorical

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.PremonoidalCategory
open Isotope.LambdaIter.Subtyping.Semantics.Categorical
open scoped MonoidalCategory

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
  (M : TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type*} [LambdaIter.HasTy Φ τ] [InstructionModel J M Φ]

/-- The independently recursive lambda-case semantics agrees with the
canonical inclusion into proof-relevant lambda-iter.  In particular, the
subtyping case uses the very same witness on both sides. -/
private theorem denote_embed_heq
    {Γ : Ctx ν τ} {n : Nat} {β : LocallyNameless.BoundCtx τ n}
    {t : LocallyNameless.Tm ν Φ n} {A : τ}
    (h : LocallyNameless.HasType Φ Γ β t A) :
    HEq (LambdaIter.Subtyping.Semantics.Categorical.denote J M h.embed) (denote J M h) := by
  induction h with
  | fv | bv | unit =>
      simp only [Isotope.LambdaCase.Subtyping.LocallyNameless.HasType.embed]
      unfold LambdaIter.Subtyping.Semantics.Categorical.denote denote
      rfl
  | op ha ih =>
      simp only [Isotope.LambdaCase.Subtyping.LocallyNameless.HasType.embed]
      unfold LambdaIter.Subtyping.Semantics.Categorical.denote denote
      have ih := eq_of_heq ih
      congr 1
  | let₁ ha hb iha ihb =>
      simp only [Isotope.LambdaCase.Subtyping.LocallyNameless.HasType.embed]
      unfold LambdaIter.Subtyping.Semantics.Categorical.denote denote
      have iha := eq_of_heq iha
      have ihb := eq_of_heq ihb
      congr 1 <;> simp only [iha, ihb]
  | pair ha hb iha ihb =>
      simp only [Isotope.LambdaCase.Subtyping.LocallyNameless.HasType.embed]
      unfold LambdaIter.Subtyping.Semantics.Categorical.denote denote
      have iha := eq_of_heq iha
      have ihb := eq_of_heq ihb
      congr 1 <;> simp only [iha, ihb]
  | let₂ ha hc iha ihc =>
      simp only [Isotope.LambdaCase.Subtyping.LocallyNameless.HasType.embed]
      unfold LambdaIter.Subtyping.Semantics.Categorical.denote denote
      unfold LambdaIter.Subtyping.Semantics.Categorical.envPairHom envPairHom
      have iha := eq_of_heq iha
      have ihc := eq_of_heq ihc
      congr 1 <;> (try simp only [iha, ihc]) <;> congr 1
  | inl ha ih | inr ha ih | abort ha ih | sub ha _ ih =>
      simp only [Isotope.LambdaCase.Subtyping.LocallyNameless.HasType.embed]
      unfold LambdaIter.Subtyping.Semantics.Categorical.denote denote
      have ih := eq_of_heq ih
      congr 1 <;> simp only [ih]
  | case he hl hr ihe ihl ihr =>
      simp only [Isotope.LambdaCase.Subtyping.LocallyNameless.HasType.embed]
      unfold LambdaIter.Subtyping.Semantics.Categorical.denote denote
      have ihe := eq_of_heq ihe
      have ihl := eq_of_heq ihl
      have ihr := eq_of_heq ihr
      congr 1 <;> (try simp only [ihe, ihl, ihr]) <;> congr 1

/-- The independently recursive lambda-case semantics agrees with the
canonical inclusion into proof-relevant lambda-iter. -/
theorem denote_embed
    {Γ : Ctx ν τ} {n : Nat} {β : LocallyNameless.BoundCtx τ n}
    {t : LocallyNameless.Tm ν Φ n} {A : τ}
    (h : LocallyNameless.HasType Φ Γ β t A) :
    LambdaIter.Subtyping.Semantics.Categorical.denote J M h.embed = denote J M h :=
  eq_of_heq (denote_embed_heq J M h)

end Isotope.LambdaCase.Subtyping.Semantics.Categorical
