import Isotope.Elgot.Basic

/-!
# The reader transformer preserves complete Elgot monads

`ReaderT R m A = R → m A`.  Iteration is defined **pointwise in the environment**: the environment
is read by every step of the loop but never changed, so `iter f a r = iter (fun a' ↦ f a' r) a`.

This is the baseline case: every structural operation of `Isotope.Elgot.Basic` commutes with
"evaluate at `r`" definitionally, and each of the four laws is a one-line transport of the
corresponding law of `m`.

Universes: with `m : Type u → Type u` and `R : Type u`, `ReaderT R m : Type u → Type u`, which is
exactly what `Iterate` requires.  No `ULift` is needed.
-/

namespace Isotope.Elgot.Transformer.Reader

universe u

variable {R : Type u} {m : Type u → Type u} {A B C : Type u}

section

variable [Iterate m]

/-- Iteration in `ReaderT R m`, pointwise in the environment. -/
instance instIterate : Iterate (ReaderT R m) where
  iter f a := fun r ↦ iter (m := m) (fun a' ↦ f a' r) a

end

section

variable [Monad m]

/-- Run a Reader-Kleisli arrow at a fixed environment. -/
abbrev at' (r : R) (f : A → ReaderT R m B) : A → m B := fun a ↦ f a r

omit [Monad m] in
/-- Reader-Kleisli arrows agreeing at every environment are equal. -/
theorem ext_at {F G : A → ReaderT R m B} (h : ∀ r, at' r F = at' r G) : F = G := by
  funext a r; exact congrFun (h r) a

omit [Monad m] in
/-- Evaluation at `r` commutes with `Sum.elim`. -/
theorem elim_at (p : B → ReaderT R m C) (q : A → ReaderT R m C) (r : R) (x : B ⊕ A) :
    (Sum.elim p q x : ReaderT R m C) r = Sum.elim (at' r p) (at' r q) x := by cases x <;> rfl

end

section

variable [Monad m] [Iterate m]

omit [Monad m] in
/-- Iteration is computed pointwise: this is the definition. -/
theorem iter_at (f : A → ReaderT R m (B ⊕ A)) (r : R) :
    at' r (iter f) = iter (m := m) (at' r f) := rfl

end

section

variable [Monad m]

/-- Evaluation at `r` is a homomorphism for Kleisli composition. -/
theorem kcomp_at (f : A → ReaderT R m B) (g : B → ReaderT R m C) (r : R) :
    at' r (kcomp f g) = kcomp (at' r f) (at' r g) := rfl

/-- Evaluation at `r` fixes pure Kleisli arrows. -/
theorem liftPure_at (h : A → B) (r : R) :
    at' r (liftPure (m := ReaderT R m) h) = liftPure (m := m) h := rfl

/-- Evaluation at `r` is a homomorphism for `mapReturn`. -/
theorem mapReturn_at (f : A → ReaderT R m (B ⊕ A)) (g : B → ReaderT R m C) (r : R) :
    at' r (mapReturn f g) = mapReturn (at' r f) (at' r g) := by
  funext a
  change f a r >>= (fun x ↦ (Sum.elim _ _ x : ReaderT R m (C ⊕ A)) r) = _
  exact bind_congr fun x ↦ elim_at _ _ r x

/-- Evaluation at `r` is a homomorphism for `flattenBody`. -/
theorem flattenBody_at (f : A → ReaderT R m ((B ⊕ A) ⊕ A)) (r : R) :
    at' r (flattenBody f) = flattenBody (at' r f) := rfl

end

section

variable [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

/-- The Elgot fixpoint law, pointwise from `m`. -/
theorem fixpoint (f : A → ReaderT R m (B ⊕ A)) :
    iter f = fun a ↦ f a >>= Sum.elim pure (iter f) := by
  refine ext_at fun r ↦ ?_
  rw [iter_at, LawfulElgotMonad.fixpoint (m := m) (at' r f)]
  funext a
  exact (bind_congr fun x ↦ elim_at (m := m) pure (iter f) r x).symm

/-- Naturality, pointwise from `m`. -/
theorem naturality (f : A → ReaderT R m (B ⊕ A)) (g : B → ReaderT R m C) :
    kcomp (iter f) g = iter (mapReturn f g) := by
  refine ext_at fun r ↦ ?_
  rw [kcomp_at, iter_at, iter_at, mapReturn_at, LawfulElgotMonad.naturality (m := m)]

/-- The codiagonal law, pointwise from `m`. -/
theorem codiagonal (f : A → ReaderT R m ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f) := by
  refine ext_at fun r ↦ ?_
  rw [iter_at, iter_at, iter_at, flattenBody_at, LawfulElgotMonad.codiagonal (m := m)]

/-- Pure uniformity, pointwise from `m`.  The comparison map `h` is unchanged. -/
theorem uniformity (f : A → ReaderT R m (B ⊕ A)) (g : C → ReaderT R m (B ⊕ C))
    (h : A → C) (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g) :
    iter f = kcomp (liftPure h) (iter g) := by
  refine ext_at fun r ↦ ?_
  rw [iter_at, kcomp_at, liftPure_at, iter_at]
  refine LawfulElgotMonad.uniformity (m := m) (at' r f) (at' r g) h ?_
  have := congrArg (at' r) comm
  rwa [kcomp_at, kcomp_at, liftPure_at, liftPure_at] at this

/-- `ReaderT R m` is a complete Elgot monad whenever `m` is. -/
instance instLawfulElgotMonad : LawfulElgotMonad (ReaderT R m) where
  fixpoint := fixpoint
  naturality := naturality
  codiagonal := codiagonal
  uniformity := uniformity

end

end Isotope.Elgot.Transformer.Reader
