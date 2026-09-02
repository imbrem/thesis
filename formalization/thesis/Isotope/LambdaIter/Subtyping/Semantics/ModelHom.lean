import Isotope.LambdaIter.Subtyping.Semantics.Models
import Mathlib.CategoryTheory.Category.Basic

/-!
# Morphisms of set-valued models

`Isotope/LambdaIter/Models/` organizes *algebras of the equational
presentation* into a category.  This file does the complementary, and much
more elementary, job for the **set-valued interfaces** that the concrete
models in `Models/{Free,Null,BitVec,Nat}.lean` actually inhabit: it says what
a map between two interpretations of the same type universe is, and what a map
between two interpretations of the same instruction signature is.

## What a morphism has to commute with

A `TypeModel` is a family of sets `interp A`, four structural equivalences
(`tensorEquiv`, `unitEquiv`, `coprodEquiv`, `emptyEquiv`), and an
interpretation `coe` of *proof-relevant* subtype derivations.  A morphism is a
family `app : interp_M A → interp_N A` commuting with all five.  Two of the
five laws are automatic and carry no information — the `unit` law is an
equation in `Unit` and the `empty` law has an uninhabited domain — so
`TypeModel.Hom.mk'` builds a morphism from the other three.  The `coe` law is
the substantive one, and it is the reason this is not simply a natural
transformation of `τ`-indexed families: it must hold *for every derivation*,
not merely for every pair of related types.

## Honest boundary

* This is a category of *type* models.  It says nothing about terms, `Eqv`, or
  initiality; the object of study there is `Alg` (see
  `Isotope/LambdaIter/Models/Alg.lean`), and the two notions are not connected
  anywhere in this repository.
* `InstructionModel.Hom` is a `Prop`: it asserts that a given monad
  transformation intertwines two instruction denotations.  It does not
  require the transformation to be a monad morphism, only `pure`-preservation
  where that is what is used.
* The only concrete examples are those in `Models/`, all of whose instructions
  are pure.  Nothing here exercises a genuinely effectful instruction model.
-/

namespace Isotope.LambdaIter.Subtyping.Semantics

open CategoryTheory

universe u v x

variable {τ : Type u} [TypeFormers τ] [Subtyping τ]

/-- A morphism of set-valued type models: a family of maps commuting with the
four structural equivalences and with every proof-relevant coercion. -/
structure TypeModel.Hom (M N : TypeModel.{u, v} τ) : Type (max u v) where
  /-- The underlying family of maps. -/
  app : ∀ {A : τ}, M.interp A → N.interp A
  /-- Compatibility with the tensor equivalence. -/
  app_tensor : ∀ (A B : τ) (p : M.interp (TypeFormers.tensor A B)),
    N.tensorEquiv A B (app p) =
      (app (M.tensorEquiv A B p).1, app (M.tensorEquiv A B p).2)
  /-- Compatibility with the unit equivalence.  Automatic: both sides live in
  `Unit`.  See `TypeModel.Hom.mk'`. -/
  app_unit : ∀ x : M.interp (TypeFormers.unit : τ),
    N.unitEquiv (app x) = M.unitEquiv x
  /-- Compatibility with the coproduct equivalence. -/
  app_coprod : ∀ (A B : τ) (s : M.interp (TypeFormers.coprod A B)),
    N.coprodEquiv A B (app s) =
      Sum.map (fun y : M.interp A => app y) (fun y : M.interp B => app y)
        (M.coprodEquiv A B s)
  /-- Compatibility with the empty equivalence.  Automatic: the domain is
  uninhabited.  See `TypeModel.Hom.mk'`. -/
  app_empty : ∀ z : M.interp (TypeFormers.empty : τ),
    N.emptyEquiv (app z) = M.emptyEquiv z
  /-- Compatibility with the interpretation of subtype derivations.  This is
  the substantive law: it quantifies over derivations, not over pairs of
  types, so a proof-relevant model must interpret *each* derivation
  compatibly. -/
  app_coe : ∀ {A B : τ} (d : Subty A B) (x : M.interp A),
    app (M.coe d x) = N.coe d (app x)

namespace TypeModel.Hom

variable {M N P : TypeModel.{u, v} τ}

/-- Two morphisms of type models agree as soon as their families of maps do. -/
@[ext] theorem ext {F G : Hom M N} (h : ∀ (A : τ) (x : M.interp A), F.app x = G.app x) :
    F = G := by
  cases F; cases G
  congr 1
  funext A x
  exact h A x

/-- Smart constructor: the `unit` and `empty` laws are automatic, so only the
tensor, coproduct and coercion laws must be supplied. -/
def mk' (app : ∀ {A : τ}, M.interp A → N.interp A)
    (app_tensor : ∀ (A B : τ) (p : M.interp (TypeFormers.tensor A B)),
      N.tensorEquiv A B (app p) =
        (app (M.tensorEquiv A B p).1, app (M.tensorEquiv A B p).2))
    (app_coprod : ∀ (A B : τ) (s : M.interp (TypeFormers.coprod A B)),
      N.coprodEquiv A B (app s) =
        Sum.map (fun y : M.interp A => app y) (fun y : M.interp B => app y)
          (M.coprodEquiv A B s))
    (app_coe : ∀ {A B : τ} (d : Subty A B) (x : M.interp A),
      app (M.coe d x) = N.coe d (app x)) : Hom M N where
  app := app
  app_tensor := app_tensor
  app_unit _ := Subsingleton.elim _ _
  app_coprod := app_coprod
  app_empty z := (M.emptyEquiv z).elim
  app_coe := app_coe

/-- The identity morphism of type models. -/
def id (M : TypeModel.{u, v} τ) : Hom M M where
  app x := x
  app_tensor _ _ _ := rfl
  app_unit _ := rfl
  app_coprod _ _ s := by cases M.coprodEquiv _ _ s <;> rfl
  app_empty _ := rfl
  app_coe _ _ := rfl

/-- Composition of morphisms of type models. -/
def comp (F : Hom M N) (G : Hom N P) : Hom M P where
  app x := G.app (F.app x)
  app_tensor A B p := by rw [G.app_tensor, F.app_tensor]
  app_unit x := by rw [G.app_unit, F.app_unit]
  app_coprod A B s := by
    rw [G.app_coprod, F.app_coprod]
    cases M.coprodEquiv A B s <;> rfl
  app_empty z := by rw [G.app_empty, F.app_empty]
  app_coe d x := by rw [F.app_coe, G.app_coe]

@[simp] theorem id_app (M : TypeModel.{u, v} τ) {A : τ} (x : M.interp A) :
    (Hom.id M).app x = x := rfl

@[simp] theorem comp_app (F : Hom M N) (G : Hom N P) {A : τ} (x : M.interp A) :
    (F.comp G).app x = G.app (F.app x) := rfl

end TypeModel.Hom

/-- Set-valued type models of a fixed universe form a category. -/
instance TypeModel.instCategory (τ : Type u) [TypeFormers τ] [Subtyping τ] :
    Category.{max u v, max u (v + 1)} (TypeModel.{u, v} τ) where
  Hom := TypeModel.Hom
  id := TypeModel.Hom.id
  comp := TypeModel.Hom.comp
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-! ### The free models, functorially in the base interpretation -/

namespace Free

variable {α : Type u} {β β' β'' : α → Type v}

/-- A map of base interpretations extends to a map of the freely generated
interpretations. -/
def map (η : ∀ a, β a → β' a) : (A : LambdaIter.Ty α) → interp β A → interp β' A
  | .base a => η a
  | .tensor A B => fun p => (map η A p.1, map η B p.2)
  | .unit => fun _ => PUnit.unit
  | .coprod A B => Sum.map (map η A) (map η B)
  | .empty => fun z => z.elim

@[simp] theorem map_base (η : ∀ a, β a → β' a) (a : α) : map η (.base a) = η a := rfl

theorem map_id (A : LambdaIter.Ty α) :
    map (fun a (x : β a) => x) A = _root_.id := by
  induction A with
  | base a => rfl
  | tensor A B ihA ihB => funext p; simp [map, ihA, ihB]
  | unit => rfl
  | coprod A B ihA ihB => funext s; cases s <;> simp [map, ihA, ihB]
  | empty => funext z; exact z.elim

theorem map_comp (η : ∀ a, β a → β' a) (η' : ∀ a, β' a → β'' a)
    (A : LambdaIter.Ty α) :
    map (fun a x => η' a (η a x)) A = fun x => map η' A (map η A x) := by
  induction A with
  | base a => rfl
  | tensor A B ihA ihB => funext p; simp [map, ihA, ihB]
  | unit => rfl
  | coprod A B ihA ihB => funext s; cases s <;> simp [map, ihA, ihB]
  | empty => funext z; exact z.elim

/-- The extension commutes with the interpretation of every proof-relevant
subtype derivation. -/
theorem map_coe (η : ∀ a, β a → β' a) :
    ∀ {A B : LambdaIter.Ty α} (d : LambdaIter.Ty.Subty A B) (x : interp β A),
      map η B (coe β d x) = coe β' d (map η A x)
  | _, _, .refl _, _ => rfl
  | _, _, .trans f g, x => by
      change map η _ (coe β g (coe β f x)) = coe β' g (coe β' f (map η _ x))
      rw [map_coe η g, map_coe η f]
  | _, _, .tensor f g, p => by
      change (map η _ (coe β f p.1), map η _ (coe β g p.2)) =
        (coe β' f (map η _ p.1), coe β' g (map η _ p.2))
      rw [map_coe η f, map_coe η g]
  | _, _, .coprod f g, s => by
      cases s with
      | inl a => change Sum.inl (map η _ (coe β f a)) = Sum.inl (coe β' f (map η _ a))
                 rw [map_coe η f]
      | inr b => change Sum.inr (map η _ (coe β g b)) = Sum.inr (coe β' g (map η _ b))
                 rw [map_coe η g]
  | _, _, .empty _, z => z.elim
  | _, _, .unit _, _ => rfl

/-- The morphism of type models induced by a map of base interpretations.
Not an identity in general: see `Semantics.bitVecComplement_ne_id`. -/
def hom (η : ∀ a, β a → β' a) : typeModel β ⟶ typeModel β' :=
  TypeModel.Hom.mk' (fun {A} x => map η A x) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun d x => map_coe η d x)

@[simp] theorem hom_app (η : ∀ a, β a → β' a) (A : LambdaIter.Ty α)
    (x : interp β A) : (hom η).app (A := A) x = map η A x := rfl

@[simp] theorem hom_id : hom (fun a (x : β a) => x) = 𝟙 (typeModel β) := by
  apply TypeModel.Hom.ext
  intro A x
  change map (fun a (y : β a) => y) A x = x
  rw [map_id]
  rfl

@[simp] theorem hom_comp (η : ∀ a, β a → β' a) (η' : ∀ a, β' a → β'' a) :
    hom (fun a x => η' a (η a x)) = hom η ≫ hom η' := by
  apply TypeModel.Hom.ext
  intro A x
  change map (fun a x => η' a (η a x)) A x = map η' A (map η A x)
  rw [map_comp]

end Free

/-- A worked non-identity morphism between concrete models: bitwise
complement of every base type of the bitvector model.  Here the source and
target models are literally the same object of the category, so this is a
non-identity endomorphism. -/
def bitVecComplement :
    BitVecModel.typeModel ⟶ BitVecModel.typeModel :=
  Free.hom (fun n (v : BitVec n) => ~~~v)

theorem bitVecComplement_ne_id :
    bitVecComplement ≠ 𝟙 BitVecModel.typeModel := by
  intro h
  have h' : (~~~(0 : BitVec 1)) = (0 : BitVec 1) :=
    congrArg (fun F : BitVecModel.typeModel ⟶ BitVecModel.typeModel =>
      F.app (A := .base 1) (0 : BitVec 1)) h
  exact absurd h' (by decide)

/-! ### Morphisms of instruction models -/

/-- A morphism of instruction models over a morphism `F` of the underlying
type models: a transformation `θ` of the two carrier monads intertwining the
two Kleisli denotations.

This is a `Prop`.  Nothing here forces `θ` to be a monad morphism; the
concrete instances below use only that it preserves `pure`. -/
structure InstructionModel.Hom {Φ : Type u} {ε : Type v}
    (M N : TypeModel.{u, x} τ) [LambdaIter.HasTy Φ τ] [LambdaIter.HasEff Φ ε]
    [Bot ε] {m m' : Type x → Type x} [Pure m] [Pure m'] [Functor m']
    (I : @InstructionModel Φ τ ε m _ _ M _ _ _ _)
    (J : @InstructionModel Φ τ ε m' _ _ N _ _ _ _)
    (F : M ⟶ N) (θ : ∀ X, m X → m' X) : Prop where
  /-- The transformation carries the source denotation to the target one. -/
  denote_map : ∀ (f : Φ) (a : M.interp (LambdaIter.instrSrc f)),
    (fun y => F.app y) <$> θ _ (I.denote f a) = J.denote f (F.app a)

namespace InstructionModel.Hom

/-- Along the identity of type models, a `pure`-preserving transformation is a
morphism between the denotations any two applicative functors give to a
signature whose instructions are all interpreted purely.  This is exactly the
situation of every concrete model in `Models/`. -/
theorem ofPure {Φ : Type u} {ε : Type v} (M : TypeModel.{u, x} τ)
    [LambdaIter.HasTy Φ τ] [LambdaIter.HasEff Φ ε] [Bot ε]
    {m m' : Type x → Type x} [Pure m] [Pure m'] [Functor m'] [LawfulFunctor m']
    (I : @InstructionModel Φ τ ε m _ _ M _ _ _ _)
    (J : @InstructionModel Φ τ ε m' _ _ M _ _ _ _)
    (θ : ∀ X, m X → m' X)
    (d : (f : Φ) → M.interp (LambdaIter.instrSrc f) → M.interp (LambdaIter.instrTrg f))
    (hI : ∀ f a, I.denote f a = pure (d f a))
    (hJ : ∀ f a, J.denote f a = pure (d f a))
    (hθ : ∀ (X : Type x) (y : X), θ X (pure y) = pure y) :
    InstructionModel.Hom M M I J (𝟙 M) θ where
  denote_map f a := by
    rw [hI, hθ, hJ]
    change (fun y => y) <$> (pure (d f a) : m' _) = pure (d f a)
    rw [id_map']

end InstructionModel.Hom

/-- Every `pure`-preserving transformation between two monads is a morphism
between the bitvector model's denotations in them.  This is the promised
"morphism induced by a monad morphism between two monadic models", and it is
not vacuous: the bitvector signature has five instructions. -/
theorem BitVecModel.instructionModelHom (m m' : Type → Type) [Monad m] [Monad m']
    [LawfulMonad m'] (θ : ∀ X, m X → m' X)
    (hθ : ∀ (X : Type) (y : X), θ X (pure y) = pure y) :
    InstructionModel.Hom BitVecModel.typeModel BitVecModel.typeModel
      (BitVecModel.instructionModel m) (BitVecModel.instructionModel m')
      (𝟙 _) θ :=
  InstructionModel.Hom.ofPure _ _ _ θ BitVecModel.denotePure
    (fun _ _ => rfl) (fun _ _ => rfl) hθ

/-- The same for the natural-number model. -/
theorem NatModel.instructionModelHom (m m' : Type → Type) [Monad m] [Monad m']
    [LawfulMonad m'] (θ : ∀ X, m X → m' X)
    (hθ : ∀ (X : Type) (y : X), θ X (pure y) = pure y) :
    InstructionModel.Hom NatModel.typeModel NatModel.typeModel
      (NatModel.instructionModel m) (NatModel.instructionModel m')
      (𝟙 _) θ :=
  InstructionModel.Hom.ofPure _ _ _ θ NatModel.denotePure
    (fun _ _ => rfl) (fun _ _ => rfl) hθ

/-- A concrete witness: `Id ⟶ Option`. -/
theorem bitVecIdToOption :
    InstructionModel.Hom BitVecModel.typeModel BitVecModel.typeModel
      (BitVecModel.instructionModel Id) (BitVecModel.instructionModel Option)
      (𝟙 _) (fun _ x => some x) :=
  BitVecModel.instructionModelHom Id Option _ (fun _ _ => rfl)

end Isotope.LambdaIter.Subtyping.Semantics
