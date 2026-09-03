import Isotope.Elgot.Basic

/-!
# Morphisms of monads and of complete Elgot monads

A *monad morphism* `m ⟶ n` is a family of maps `m A → n A` commuting with
`pure` and `>>=`; an *Elgot morphism* additionally commutes with `iter`.

## Why both notions, and why `iter` is a separate field

Preservation of `iter` does **not** follow from preservation of `pure` and
`>>=`.  Iteration is not definable from the monad structure — it is extra
algebraic data, and a monad may carry several inequivalent iteration
operators.  So a monad morphism only transports the *sequential* fragment of a
model; transporting a loop needs the extra law, and it is exactly this extra
law that fails for, say, a map that collapses divergence.

## What these are for

`Isotope/LambdaIter/Models/Monadic/Push.lean` turns an `ElgotHom m n` into a
morphism of *algebras* of the lambda-iter presentation: pushing a monadic
model along it gives another monadic model, and the induced map of carriers
commutes with all twelve term formers.  A `MonadHom` alone suffices for
lambda-seq and lambda-case, which have no iteration.
-/

namespace Isotope.Elgot

universe u

/-- A morphism of monads: a natural family commuting with `pure` and `bind`.

Naturality is not a field: it is a consequence of the two laws, since `Functor.map`
is `bind` after `pure` in any lawful monad (`MonadHom.app_map`). -/
structure MonadHom (m n : Type u → Type u) [Monad m] [Monad n] where
  /-- The underlying family of maps. -/
  app : {A : Type u} → m A → n A
  /-- Returned values are preserved. -/
  app_pure : ∀ {A : Type u} (a : A), app (pure a : m A) = pure a
  /-- Sequencing is preserved. -/
  app_bind : ∀ {A B : Type u} (x : m A) (f : A → m B),
    app (x >>= f) = app x >>= fun a => app (f a)

namespace MonadHom

variable {m n p : Type u → Type u} [Monad m] [Monad n] [Monad p]

/-- Two monad morphisms agree as soon as their underlying families do. -/
@[ext] theorem ext {φ ψ : MonadHom m n}
    (h : ∀ {A : Type u} (x : m A), φ.app x = ψ.app x) : φ = ψ := by
  cases φ; cases ψ; congr 1; funext A x; exact h x

/-- The identity monad morphism. -/
def id (m : Type u → Type u) [Monad m] : MonadHom m m where
  app x := x
  app_pure _ := rfl
  app_bind _ _ := rfl

/-- Composition of monad morphisms, in diagrammatic order. -/
def comp (φ : MonadHom m n) (ψ : MonadHom n p) : MonadHom m p where
  app x := ψ.app (φ.app x)
  app_pure a := by rw [φ.app_pure, ψ.app_pure]
  app_bind x f := by rw [φ.app_bind, ψ.app_bind]

@[simp] theorem id_app {A : Type u} (x : m A) : (MonadHom.id m).app x = x := rfl

@[simp] theorem comp_app (φ : MonadHom m n) (ψ : MonadHom n p) {A : Type u}
    (x : m A) : (φ.comp ψ).app x = ψ.app (φ.app x) := rfl

/-- A monad morphism commutes with Kleisli composition. -/
theorem app_kcomp (φ : MonadHom m n) {A B C : Type u} (f : A → m B) (g : B → m C)
    (a : A) : φ.app (kcomp f g a) = kcomp (fun a => φ.app (f a)) (fun b => φ.app (g b)) a :=
  φ.app_bind (f a) g

/-- A monad morphism fixes pure Kleisli arrows. -/
theorem app_liftPure (φ : MonadHom m n) {A B : Type u} (f : A → B) (a : A) :
    φ.app (liftPure (m := m) f a) = liftPure (m := n) f a := φ.app_pure (f a)

/-- A monad morphism is natural: it commutes with `Functor.map`. -/
theorem app_map [LawfulMonad m] [LawfulMonad n] (φ : MonadHom m n)
    {A B : Type u} (f : A → B) (x : m A) : φ.app (f <$> x) = f <$> φ.app x := by
  rw [← bind_pure_comp, φ.app_bind]
  rw [show (fun a => φ.app (pure (f a) : m B)) = (fun a => (pure (f a) : n B)) from
    funext fun a => φ.app_pure (f a)]
  rw [bind_pure_comp]

end MonadHom

/-- A morphism of complete Elgot monads: a monad morphism that additionally
commutes with the iteration operator.

The `iter` law is genuinely additional data-preservation: see the module
docstring. -/
structure ElgotHom (m n : Type u → Type u) [Monad m] [Monad n] [Iterate m]
    [Iterate n] extends MonadHom m n where
  /-- Iteration is preserved. -/
  app_iter : ∀ {A B : Type u} (f : A → m (B ⊕ A)) (a : A),
    app (iter f a) = iter (fun a => app (f a)) a

namespace ElgotHom

variable {m n p : Type u → Type u} [Monad m] [Monad n] [Monad p]
variable [Iterate m] [Iterate n] [Iterate p]

/-- Two Elgot morphisms agree as soon as their underlying families do. -/
@[ext] theorem ext {φ ψ : ElgotHom m n}
    (h : ∀ {A : Type u} (x : m A), φ.app x = ψ.app x) : φ = ψ := by
  cases φ; cases ψ
  congr 1
  exact MonadHom.ext h

/-- The identity Elgot morphism. -/
def id (m : Type u → Type u) [Monad m] [Iterate m] : ElgotHom m m where
  toMonadHom := MonadHom.id m
  app_iter _ _ := rfl

/-- Composition of Elgot morphisms, in diagrammatic order. -/
def comp (φ : ElgotHom m n) (ψ : ElgotHom n p) : ElgotHom m p where
  toMonadHom := φ.toMonadHom.comp ψ.toMonadHom
  app_iter f a := by
    show ψ.app (φ.app (iter f a)) = _
    rw [φ.app_iter, ψ.app_iter]
    rfl

@[simp] theorem id_app {A : Type u} (x : m A) : (ElgotHom.id m).app x = x := rfl

@[simp] theorem comp_app (φ : ElgotHom m n) (ψ : ElgotHom n p) {A : Type u}
    (x : m A) : (φ.comp ψ).app x = ψ.app (φ.app x) := rfl

end ElgotHom

end Isotope.Elgot
