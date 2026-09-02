import Isotope.LambdaCase.Typing
import Isotope.LambdaIter.Semantics.Categorical

/-! # Distributive Freyd semantics of lambda-case -/

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Isotope.LambdaCase.Semantics.Categorical

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

/-- The comparison denotation obtained by choosing the typing witness produced
by the inclusion into exact lambda-iter.  This is kept separate from `denote`:
agreement with the independently recursive semantics is a coherence property,
not definitional equality for arbitrary proof-relevant type formers. -/
noncomputable def denoteChosen [Iteration C] [ElgotCategory C]
    [StrongElgotFreydCategory J]
    {Γ : Ctx ν τ} {n : Nat} {β : LocallyNameless.BoundCtx τ n}
    {t : LocallyNameless.Tm ν Φ n} {A : τ}
    (h : LocallyNameless.HasType Φ Γ β t A) :=
  LambdaIter.LocallyNameless.Categorical.denote J M h.embed

/-- Inclusion commutes with the chosen categorical denotation. -/
theorem denoteChosen_embed [Iteration C] [ElgotCategory C]
    [StrongElgotFreydCategory J]
    {Γ : Ctx ν τ} {n : Nat} {β : LocallyNameless.BoundCtx τ n}
    {t : LocallyNameless.Tm ν Φ n} {A : τ}
    (h : LocallyNameless.HasType Φ Γ β t A) :
    LambdaIter.LocallyNameless.Categorical.denote J M h.embed =
      denoteChosen J M h := rfl

/-- Under exact typing coherence, replacing the inclusion-produced witness by
any other exact lambda-iter typing witness for the embedded term is harmless. -/
theorem denoteChosen_independent [Iteration C] [ElgotCategory C]
    [StrongElgotFreydCategory J]
    [LambdaIter.LocallyNameless.Categorical.TypingCoherent (ν := ν) (Φ := Φ) J M]
    {Γ : Ctx ν τ} {n : Nat} {β : LocallyNameless.BoundCtx τ n}
    {t : LocallyNameless.Tm ν Φ n} {A : τ}
    (h : LocallyNameless.HasType Φ Γ β t A)
    (k : LambdaIter.LocallyNameless.HasType Φ Γ β t.embed A) :
    LambdaIter.LocallyNameless.Categorical.denote J M k =
      denoteChosen J M h :=
  LambdaIter.LocallyNameless.Categorical.TypingCoherent.denote_eq k h.embed

end Isotope.LambdaCase.Semantics.Categorical
