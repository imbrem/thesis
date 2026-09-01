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

/-- Structural coherence laws for a categorical interpretation of subtyping.
This class deliberately does not identify arbitrary subtype derivations; that
stronger, optional condition is `SubtyProofIrrelevant`. -/
class LawfulTypeModel (τ : Type u₃) [TypeFormers τ] [Subtyping τ]
    (V : Type u₁) [Category.{v₁} V] [CartesianMonoidalCategory V]
    [HasFiniteCoproducts V] (M : TypeModel τ V) : Prop where
  subty_refl (A : τ) : M.subty (Subty.refl A) = 𝟙 (M.obj A)
  subty_trans {A B C : τ} (f : Subty A B) (g : Subty B C) :
    M.subty (Subty.trans f g) = M.subty f ≫ M.subty g
  subty_tensor {A A' B B' : τ} (f : Subty A A') (g : Subty B B') :
    M.subty (Subty.tensor f g) ≫ (M.tensorIso A' B').hom =
      (M.tensorIso A B).hom ≫ (M.subty f ⊗ₘ M.subty g)
  subty_coprod {A A' B B' : τ} (f : Subty A A') (g : Subty B B') :
    M.subty (Subty.coprod f g) ≫ (M.coprodIso A' B').hom =
      (M.coprodIso A B).hom ≫ coprod.map (M.subty f) (M.subty g)
  subty_empty (A : τ) : M.subty (Subty.empty A) = M.emptyIsInitial.to (M.obj A)
  subty_unit (A : τ) :
    M.subty (Subty.unit A) ≫ M.unitIso.hom =
      CartesianMonoidalCategory.toUnit (M.obj A)

/-- Optional semantic proof irrelevance for subtype derivations.  Keeping this
separate permits both proof-relevant refinement models and coherent ordinary
subtyping models to use the same weak `TypeModel` interface. -/
class SubtyProofIrrelevant (τ : Type u₃) [TypeFormers τ] [Subtyping τ]
    (V : Type u₁) [Category.{v₁} V] [CartesianMonoidalCategory V]
    [HasFiniteCoproducts V] (M : TypeModel τ V) : Prop where
  subty_eq {A B : τ} (f g : Subty A B) : M.subty f = M.subty g

section SubtypingCoherence

variable {τ : Type u₃} [TypeFormers τ] [Subtyping τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V]
  [HasFiniteCoproducts V] (M : TypeModel τ V)

theorem subty_comp_eq [LawfulTypeModel τ V M] [SubtyProofIrrelevant τ V M]
    {A B C : τ} (f : Subty A B) (g : Subty B C) (h : Subty A C) :
    M.subty f ≫ M.subty g = M.subty h := by
  rw [← LawfulTypeModel.subty_trans]
  exact SubtyProofIrrelevant.subty_eq _ _

end SubtypingCoherence

/-- Interpretation of primitive instructions as computation morphisms. -/
class InstructionModel [TypeFormers τ] [Subtyping τ]
    [Category.{v₁} V] [Category.{v₂} C] (J : Functor V C)
    [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
    (M : TypeModel τ V) (Φ : Type u₄) [HasTy Φ τ] where
  denote (f : Φ) : J.obj (M.obj (instrSrc f)) ⟶ J.obj (M.obj (instrTrg f))

section Contexts

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V]
  [HasFiniteCoproducts V]
  {τ : Type u₃} [TypeFormers τ] [Subtyping τ] (M : TypeModel τ V)

/-- Value-category interpretation of a free-variable context.  The newest slot is the right
tensor factor, exactly as in the existing nested-pair semantics. -/
def ctxObj : Ctx ν τ → V
  | .nil => 𝟙_ V
  | .snoc Γ _ A => ctxObj Γ ⊗ M.obj A

/-- Value-category interpretation of a length-indexed bound context. -/
def boundObj : {n : Nat} → LocallyNameless.BoundCtx τ n → V
  | 0, .nil => 𝟙_ V
  | _ + 1, .snoc β A => boundObj β ⊗ M.obj A

/-- The complete environment object. -/
def envObj (Γ : Ctx ν τ) {n : Nat} (β : LocallyNameless.BoundCtx τ n) : V :=
  ctxObj M Γ ⊗ boundObj M β

/-- Categorical lookup of a visible free name. -/
noncomputable def ctxLookup [DecidableEq ν] : {Γ : Ctx ν τ} →
    (x : ν) → {A : τ} → Γ.lookup x = some A → (ctxObj M Γ ⟶ (M.obj A : V))
  | .nil, _, _, h => by simp [Ctx.lookup] at h
  | .snoc Γ none B, x, A, h =>
      CartesianMonoidalCategory.fst _ _ ≫ ctxLookup x h
  | .snoc Γ (some y) B, x, A, h => by
      by_cases hxy : x = y
      · subst y
        simp [Ctx.lookup] at h
        cases h
        exact CartesianMonoidalCategory.snd _ _
      · exact CartesianMonoidalCategory.fst _ _ ≫
          ctxLookup x (by simpa [Ctx.lookup, hxy] using h)

/-- Free lookup from the complete environment discards the bound component first. -/
noncomputable def freeLookup [DecidableEq ν] {Γ : Ctx ν τ}
    {n : Nat} {β : LocallyNameless.BoundCtx τ n}
    (x : ν) {A : τ} (h : Γ.lookup x = some A) : envObj M Γ β ⟶ (M.obj A : V) :=
  CartesianMonoidalCategory.fst _ _ ≫ ctxLookup M x h

/-- Categorical lookup of a newest-first de Bruijn index. -/
noncomputable def boundLookup : {n : Nat} → {β : LocallyNameless.BoundCtx τ n} →
    (i : Fin n) → (boundObj M β ⟶ (M.obj (β.get i) : V))
  | _ + 1, .snoc β A, i => Fin.cases
      (CartesianMonoidalCategory.snd _ _)
      (fun j => CartesianMonoidalCategory.fst _ _ ≫ boundLookup j) i

/-- Bound lookup from the complete environment discards the free component first. -/
noncomputable def boundVar {Γ : Ctx ν τ}
    {n : Nat} {β : LocallyNameless.BoundCtx τ n} (i : Fin n) :
    envObj M Γ β ⟶ (M.obj (β.get i) : V) :=
  CartesianMonoidalCategory.snd _ _ ≫ boundLookup M i

/-- Extending the bound context corresponds, up to associativity, to pairing the old complete
environment with the new value. -/
def envSnocIso (Γ : Ctx ν τ) {n : Nat} (β : LocallyNameless.BoundCtx τ n) (A : τ) :
    envObj M Γ β ⊗ M.obj A ≅ envObj M Γ (.snoc β A) :=
  α_ (ctxObj M Γ) (boundObj M β) (M.obj A)

end Contexts

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

section DistributiveControl

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : Functor V C) [DistributiveFreydCategory J]

/-- Because `J` preserves finite coproducts, a computation whose source is the image of a value
coproduct can be split into a computation coproduct. -/
noncomputable def splitMapCoprod (A B : V) :
    J.obj (A ⨿ B) ⟶ J.obj A ⨿ J.obj B :=
  inv (coprodComparison J A B)

/-- Contextual case analysis.  The distributor sends the retained context into the selected
branch; the inverse coproduct comparison then exposes the computation coproduct consumed by
`coprod.desc`. -/
noncomputable def caseWithContext {R A B D : V}
    (scrutinee : J.obj R ⟶ J.obj (A ⨿ B))
    (left : J.obj (R ⊗ A) ⟶ J.obj D)
    (right : J.obj (R ⊗ B) ⟶ J.obj D) : J.obj R ⟶ J.obj D :=
  bind J scrutinee <|
    J.map (DistributiveTensor.leftIso R A B).inv ≫
      splitMapCoprod J (R ⊗ A) (R ⊗ B) ≫
        coprod.desc left right

/-- Elimination from an interpreted empty type is pure. -/
noncomputable def abort {τ : Type u₃} [TypeFormers τ] [Subtyping τ]
    (M : TypeModel τ V) {R : V} {A : τ}
    (emptyComputation : J.obj R ⟶ J.obj (M.obj (empty : τ))) :
    J.obj R ⟶ J.obj (M.obj A) :=
  emptyComputation ≫ J.map (M.emptyIsInitial.to (M.obj A))

end DistributiveControl

section StrongIteration

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]

/-- Run `f` on the right component while retaining the left value context. -/
noncomputable def retainLeft (J : Functor V C) [FreydCategory J]
    {R X Y : V} (f : J.obj X ⟶ J.obj Y) :
    J.obj (R ⊗ X) ⟶ J.obj (R ⊗ Y) :=
  (Functor.StrongPremonoidal.tensorIso (J := J) R X).inv ≫
    leftTensor (𝟙 (J.obj R)) f ≫
    (Functor.StrongPremonoidal.tensorIso (J := J) R Y).hom

/-- Turn a loop body depending on a read-only environment into an ordinary categorical
iteration body.  A pure diagonal preserves the environment, the inverse distributor routes it
into both branches, and the preserved environment is discarded after the loop exits. -/
noncomputable def contextualLoop (J : Functor V C) [StrongElgotFreydCategory J]
    {R A B : V} (body : J.obj (R ⊗ A) ⟶ J.obj (B ⨿ A)) :
    J.obj (R ⊗ A) ⟶ J.obj B :=
  iterate
    (J.map (CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst R A) (𝟙 (R ⊗ A))) ≫
      retainLeft J body ≫
      J.map (DistributiveTensor.leftIso R B A).inv ≫
      splitMapCoprod J (R ⊗ B) (R ⊗ A)) ≫
    J.map (CartesianMonoidalCategory.snd R B)

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

section Denotation

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] [Subtyping τ] (M : TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type*} [HasTy Φ τ] [InstructionModel J M Φ]

/-- Reassociate an environment extended by a pair into an environment extended by its two
components. -/
def envPairHom (Γ : Ctx ν τ) {n : Nat} (β : LocallyNameless.BoundCtx τ n) (A B : τ) :
    envObj M Γ β ⊗ (M.obj A ⊗ M.obj B) ⟶
      envObj M Γ (.snoc (.snoc β A) B) :=
  (α_ (ctxObj M Γ) (boundObj M β) (M.obj A ⊗ M.obj B)).hom ≫
    ctxObj M Γ ◁ (α_ (boundObj M β) (M.obj A) (M.obj B)).inv

/-- Denotation of an existing locally nameless typing derivation in a strong Elgot Freyd
category.  As in the monadic semantics, the derivation matters at `sub`. -/
noncomputable def denote : {Γ : Ctx ν τ} → {n : Nat} →
    {β : LocallyNameless.BoundCtx τ n} → {t : LocallyNameless.Tm ν Φ n} → {A : τ} →
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
  | Γ, _, β, _, _, .iter ha hb => bind J (denote ha) <|
      contextualLoop J
        (J.map (envSnocIso M Γ β _).hom ≫ denote hb ≫
          J.map (M.coprodIso _ _).hom)
  | _, _, _, _, _, .sub ha d => denote ha ≫ J.map (M.subty d)

end Denotation

end Isotope.LambdaIter.Semantics.Categorical
