import Isotope.CategoryTheory.Freyd.Elgot
import Isotope.LambdaIter.LocallyNameless.Typing

/-!
# Categorical semantic core for lambda-iter

This file separates the categorical operations used by the semantics from the existing
`Type`/monad implementation.  The latter hard-codes types as Lean types and contexts as nested
pairs; the interfaces below are its category-independent replacement.
-/

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Isotope.LambdaIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory

/-- Interpretation of object-language types in the value category.  Type former preservation is
recorded by isomorphisms rather than forced to hold definitionally.  Subtyping remains
proof-relevant. -/
class TypeModel (τ : Type u₃) [TypeFormers τ] [Subtyping τ]
    (V : Type u₁) [Category.{v₁} V] [CartesianMonoidalCategory V]
    [HasFiniteCoproducts V] where
  obj : τ → V
  tensorIso (A B : τ) : obj (tensor A B) ≅ obj A ⊗ obj B
  unitIso : obj (unit : τ) ≅ 𝟙_ V
  coprodIso (A B : τ) : obj (coprod A B) ≅ obj A ⨿ obj B
  emptyIsInitial : IsInitial (obj (empty : τ))
  subty {A B : τ} : Subty A B → (obj A ⟶ obj B)

/-- Interpretation of primitive instructions as computation morphisms. -/
class InstructionModel [TypeFormers τ] [Subtyping τ]
    [Category.{v₁} V] [Category.{v₂} C] (J : Functor V C)
    [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
    (M : TypeModel τ V) (Φ : Type u₄) [HasTy Φ τ] where
  denote (f : Φ) : J.obj (M.obj (instrSrc f)) ⟶ J.obj (M.obj (instrTrg f))

section FreydCombinators

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  (J : Functor V C) [FreydCategory J]

/-- Duplicate a value-category context. -/
noncomputable def duplicate (R : V) : R ⟶ R ⊗ R :=
  CartesianMonoidalCategory.lift (𝟙 R) (𝟙 R)

/-- Evaluate `f` while retaining an unchanged copy of its input context.  The only tensor of
computation morphisms used here has an identity in one position; no arbitrary exchange law is
needed. -/
noncomputable def extend {R A : V} (f : J.obj R ⟶ J.obj A) :
    J.obj R ⟶ J.obj (R ⊗ A) :=
  J.map (duplicate R) ≫
    (Functor.StrongPremonoidal.tensorIso (J := J) R R).inv ≫
    leftTensor (𝟙 (J.obj R)) f ≫
    (Functor.StrongPremonoidal.tensorIso (J := J) R A).hom

/-- Categorical call-by-value `let`: evaluate `f`, retain its input context, and continue with
`g`. -/
noncomputable def bind {R A B : V} (f : J.obj R ⟶ J.obj A)
    (g : J.obj (R ⊗ A) ⟶ J.obj B) : J.obj R ⟶ J.obj B :=
  extend J f ≫ g

/-- Forget the newly produced value and recover the retained context. -/
noncomputable def retainedContext {R A : V} : J.obj (R ⊗ A) ⟶ J.obj R :=
  J.map (CartesianMonoidalCategory.fst R A)

/-- Sequential pairing.  `f` is run before `g`, matching the evaluation order of lambda-iter.
The final pure map discards the retained context and returns the two results. -/
noncomputable def pair {R A B : V} (f : J.obj R ⟶ J.obj A)
    (g : J.obj R ⟶ J.obj B) : J.obj R ⟶ J.obj (A ⊗ B) :=
  bind J f <| bind J (retainedContext J ≫ g) <|
    J.map (CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.fst (R ⊗ A) B ≫
        CartesianMonoidalCategory.snd R A)
      (CartesianMonoidalCategory.snd (R ⊗ A) B))

/-- Branch between two computation arrows using the computation category's coproduct. -/
noncomputable def branch [HasBinaryCoproducts C] {A B D : C}
    (f : A ⟶ D) (g : B ⟶ D) : A ⨿ B ⟶ D :=
  coprod.desc f g

/-- The categorical interpretation of a context-free `iter`: left exits, right recurs. -/
def loop [HasBinaryCoproducts C] [Iteration C] {X Y : C}
    (body : X ⟶ Y ⨿ X) : X ⟶ Y :=
  iterate body

end FreydCombinators

section StrongIteration

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]

/-- Thread a fixed context through a context-independent loop body.  This is the primitive
contextual iteration equation used when proving the full syntax interpretation sound. -/
noncomputable def threadLoop {X Y : C} (R : C) (body : X ⟶ Y ⨿ X) :
    R ⊗ X ⟶ R ⊗ Y :=
  iterate ((R ◁ body) ≫ DistributivePremonoidalCategory.leftInv R Y X)

theorem threadLoop_eq (J : Functor V C) [StrongElgotFreydCategory J]
    {X Y : C} (R : C) (body : X ⟶ Y ⨿ X) :
    threadLoop R body = R ◁ iterate body :=
  StrongElgotFreydCategory.strength J R body

end StrongIteration

end Isotope.LambdaIter.Semantics.Categorical
