import Isotope.Elgot.Basic
import Mathlib.Control.Monad.Writer

/-!
# The writer transformer preserves complete Elgot monads (discard-on-divergence)

`WriterT W m A = m (A × W)` (Mathlib's `WriterT`).  Iteration threads the accumulated output
through the recursive argument and seeds it at `1`:

  `iter f a = WriterT.mk (iter (stepW f) (a, 1))`

where `stepW f : A × W → m ((B × W) ⊕ (A × W))` runs one step of the body and multiplies the
log so far on the left.  Equivalently, this is the `StateT W m` iteration restricted along the
embedding `WriterT W m ↪ StateT W m` and evaluated at `1`.

## What this semantics does with divergence

The output of a run that never returns is **discarded together with the run**: `iter` only ever
multiplies the finitely many `W`s of a terminating unfolding, and a nonterminating unfolding
contributes whatever the base monad's `iter` contributes (`Part.none`, `∅` for `Set`).  This is
forced, not chosen: see `Isotope.Elgot.Transformer.Writer.Divergence` for three theorems showing
that no iteration operator on any `WriterT W m` can retain infinite output.

## Minimal structure on `W`

`Monoid W` is **exactly** the hypothesis, and it cannot be weakened.  Mathlib's
`LawfulMonad (WriterT W m)` — a prerequisite of `LawfulElgotMonad` — already consumes `one_mul`
(for `pure_bind`), `mul_one` (for `bind_pure_comp`) and `mul_assoc` (for `bind_assoc`), so there
is no per-law refinement to `Mul` or `MulOneClass` that a user could exploit.  What the individual
laws consume is recorded per theorem below:

| law | axioms of `W` | laws of `m` |
| --- | --- | --- |
| `fixpoint` | `one_mul`, `mul_one`, `mul_assoc` | fixpoint, naturality, uniformity |
| `naturality` | `mul_assoc`, `mul_one` | naturality |
| `codiagonal` | `mul_one`, `mul_assoc` | codiagonal, naturality, uniformity |
| `uniformity` | `one_mul`, `mul_one` | uniformity |

(`mul_assoc` enters `fixpoint` and `codiagonal` only through `iter_shift`, and naturality and
uniformity of `m` likewise.)

## Instance hazard

Mathlib declares `Monad (WriterT ω M)` twice: once from `[Monoid ω]` and once from
`[EmptyCollection ω] [Append ω]`.  For `ω = List E` only the *second* fires, since Mathlib has no
`Monoid (List α)`, so the `[Monoid W]`-keyed instances here silently fail to apply.  Use
`FreeMonoid E` in examples: it is a `CancelMonoid` with `FreeMonoid.length`, and has no competing
instance.
-/

namespace Isotope.Elgot.Transformer.Writer

universe u

variable {W : Type u} {m : Type u → Type u} {A B C : Type u}

section

variable [Monoid W] [Monad m]

/-- Left-multiply the accumulated output component. -/
def shift (w : W) : A × W → A × W := fun p ↦ (p.1, w * p.2)

/-- Distribute the accumulated output over the return/recurse coproduct. -/
def distr : (B ⊕ A) × W → (B × W) ⊕ (A × W) :=
  fun p ↦ Sum.elim (fun b ↦ Sum.inl (b, p.2)) (fun a ↦ Sum.inr (a, p.2)) p.1

/-- One step of the loop, with the log so far threaded through the recursive argument. -/
def stepW (f : A → WriterT W m (B ⊕ A)) : A × W → m ((B × W) ⊕ (A × W)) :=
  fun p ↦ WriterT.run (f p.1) >>= fun q ↦ pure (distr (q.1, p.2 * q.2))

/-- Running a writer `pure` emits the empty log. -/
theorem run_pure (a : A) : WriterT.run (pure a : WriterT W m A) = pure (a, 1) := rfl

/-- Running a writer bind concatenates the two logs, left to right. -/
theorem run_bind (x : WriterT W m A) (f : A → WriterT W m B) :
    WriterT.run (x >>= f)
      = WriterT.run x >>= fun p ↦ (fun q : B × W ↦ (q.1, p.2 * q.2)) <$> WriterT.run (f p.1) :=
  rfl

/-- Running a pure Kleisli arrow emits the empty log. -/
theorem run_liftPure (φ : A → B) (a : A) :
    WriterT.run (liftPure φ a : WriterT W m B) = pure (φ a, 1) := rfl

/-- Running a Kleisli composite. -/
theorem run_kcomp (x : A → WriterT W m B) (k : B → WriterT W m C) (a : A) :
    WriterT.run (kcomp x k a)
      = WriterT.run (x a) >>= fun p ↦ (fun q : C × W ↦ (q.1, p.2 * q.2)) <$> WriterT.run (k p.1) :=
  rfl

/-- Postcomposition by a writer arrow, transported to the enlarged state. -/
def postW (g : B → WriterT W m C) : B × W → m (C × W) :=
  fun p ↦ (fun q : C × W ↦ (q.1, p.2 * q.2)) <$> WriterT.run (g p.1)

end

section

variable [Monoid W] [Monad m] [LawfulMonad m]

/-- Binding a pure postprocessor leaves the log alone. -/
theorem run_bind_pure (x : WriterT W m A) (φ : A → B) :
    WriterT.run (x >>= (Pure.pure ∘ φ : A → WriterT W m B))
      = WriterT.run x >>= fun p ↦ pure (φ p.1, p.2) := by
  rw [run_bind]
  simp only [Function.comp_apply, run_pure, map_pure, mul_one]

/-- `mapReturn` along a pure arrow is a Kleisli postcomposition. -/
theorem mapReturn_liftPure (g : A → m (B ⊕ A)) (φ : B → C) :
    mapReturn g (liftPure φ) = kcomp g (liftPure (Sum.map φ (id : A → A))) := by
  funext a
  simp only [mapReturn, kcomp, liftPure, Function.comp_apply, pure_bind]
  congr 1
  funext s
  cases s <;> rfl

/-- `stepW f` is left-equivariant for the shift action of `W`: this is the only place
`mul_assoc` is used. -/
theorem stepW_shift (f : A → WriterT W m (B ⊕ A)) (w : W) :
    kcomp (liftPure (shift w)) (stepW f)
      = kcomp (stepW f) (liftPure (Sum.map (shift (A := B) w) (shift (A := A) w))) := by
  funext p
  simp only [kcomp, liftPure, Function.comp_apply, pure_bind, stepW, bind_assoc]
  congr 1
  funext q
  obtain ⟨s, w'⟩ := q
  cases s <;> simp [distr, shift, Sum.map, mul_assoc]

/-- Transporting `mapReturn` through `stepW`. -/
theorem stepW_mapReturn (f : A → WriterT W m (B ⊕ A)) (g : B → WriterT W m C) :
    stepW (mapReturn f g) = mapReturn (stepW f) (postW g) := by
  funext p
  simp only [stepW, mapReturn, postW, run_bind, bind_assoc, map_eq_pure_bind, pure_bind,
    Function.comp_apply]
  congr 1
  funext q
  obtain ⟨s, w'⟩ := q
  cases s with
  | inl b =>
      simp only [distr, Sum.elim_inl, run_bind_pure, bind_assoc, pure_bind, mul_assoc]
  | inr a' => simp [distr, run_pure, mul_one]

omit [Monoid W] in
/-- The purely combinatorial identity behind codiagonality: `distr` commutes with `flatten`. -/
theorem distr_flatten (x : (B ⊕ A) ⊕ A) (u : W) :
    flatten (Sum.map (distr (B := B) (A := A) (W := W)) (id : A × W → A × W) (distr (x, u)))
      = distr (flatten x, u) := by
  cases x with
  | inl s => cases s <;> rfl
  | inr a => rfl

/-- `flattenBody` commutes with the transport, once the outer `distr` has been absorbed. -/
theorem flattenBody_stepW (f : A → WriterT W m ((B ⊕ A) ⊕ A)) :
    flattenBody (kcomp (stepW f) (liftPure (Sum.map (distr (B := B) (A := A) (W := W)) id)))
      = stepW (flattenBody f) := by
  funext p
  obtain ⟨a, v⟩ := p
  simp only [flattenBody, kcomp, liftPure, Function.comp_apply, stepW, bind_assoc, pure_bind,
    run_bind_pure]
  congr 1
  funext q
  exact congrArg pure (distr_flatten q.1 (v * q.2))

end

section

variable [Monoid W] [Monad m] [Iterate m]

/-- Iteration in `WriterT W m`, threading the accumulated output through the recursive argument
and seeding it at `1`. -/
instance instIterate : Iterate (WriterT W m) where
  iter f a := WriterT.mk (iter (stepW f) (a, 1))

/-- Unfolding of `iter` at the level of `m`: this is the definition. -/
theorem run_iter (f : A → WriterT W m (B ⊕ A)) (a : A) :
    WriterT.run (iter f a) = iter (stepW f) (a, 1) := rfl

end

section

variable [Monoid W] [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

/-- **Equivariance.** Iteration of a left-equivariant body is left-equivariant: starting from an
enlarged state prefixed by `w` is the same as starting without it and shifting the result.

`Isotope.Elgot.LawfulElgotMonad.uniformity` only lets a pure map act on the *state*; the writer
needs a shift on the *result* as well.  Composing naturality (result side) with uniformity (state
side) supplies it.  This is the same recipe as
`Isotope.CategoryTheory.Monad.Elgot.iter_threaded`. -/
theorem iter_shift (g : A × W → m ((B × W) ⊕ (A × W)))
    (hg : ∀ w : W, kcomp (liftPure (shift w)) g
              = kcomp g (liftPure (Sum.map (shift (A := B) w) (shift (A := A) w))))
    (w v : W) (a : A) :
    iter g (a, w * v) = shift w <$> iter g (a, v) := by
  have hnat := LawfulElgotMonad.naturality (m := m) g (liftPure (shift (A := B) w))
  have huni := LawfulElgotMonad.uniformity (m := m)
    (mapReturn g (liftPure (shift (A := B) w))) g (shift (A := A) w) ?comm
  · have h1 := congrFun huni (a, v)
    have h2 := congrFun hnat.symm (a, v)
    rw [h1] at h2
    simp only [kcomp, liftPure, Function.comp_apply, pure_bind] at h2
    rw [show ((a, w * v) : A × W) = shift w (a, v) from rfl, h2]
    exact bind_pure_comp _ _
  case comm =>
    funext p
    simp only [kcomp, mapReturn, liftPure, Function.comp_apply, bind_assoc, pure_bind]
    have hp := congrFun (hg w) p
    simp only [kcomp, liftPure, Function.comp_apply, pure_bind] at hp
    rw [hp]
    congr 1
    funext s
    cases s <;> simp [shift, Sum.map, Function.comp_def]

/-- Equivariance, specialised to the seeded loop: restarting the loop with log `w` already
accumulated shifts the result by `w`. -/
theorem iter_shift' (f : A → WriterT W m (B ⊕ A)) (w : W) (a : A) :
    iter (stepW f) (a, w) = shift w <$> WriterT.run (iter f a) := by
  have h := iter_shift (stepW f) (stepW_shift f) w 1 a
  rw [mul_one] at h
  rw [run_iter]
  exact h

/-- The Elgot fixpoint law for `WriterT W m`. -/
theorem fixpoint (f : A → WriterT W m (B ⊕ A)) :
    iter f = fun a ↦ f a >>= Sum.elim pure (iter f) := by
  funext a
  apply WriterT.ext
  rw [run_iter, run_bind]
  rw [congrFun (LawfulElgotMonad.fixpoint (m := m) (stepW f)) (a, 1)]
  simp only [stepW, bind_assoc, pure_bind]
  congr 1
  funext q
  obtain ⟨s, w'⟩ := q
  cases s with
  | inl b => simp [distr, run_pure, one_mul, mul_one]
  | inr a' =>
      simp only [distr, Sum.elim_inr, one_mul]
      rw [iter_shift' f w' a']
      rfl

/-- Naturality for `WriterT W m`.  Needs no equivariance: `mul_assoc` reconciles the two
bracketings of the accumulated log. -/
theorem naturality (f : A → WriterT W m (B ⊕ A)) (g : B → WriterT W m C) :
    kcomp (iter f) g = iter (mapReturn f g) := by
  funext a
  apply WriterT.ext
  rw [run_iter, stepW_mapReturn, ← LawfulElgotMonad.naturality (m := m)]
  simp only [kcomp, run_iter, run_bind]
  rfl

/-- The outer step of an iterated iteration factors through the inner iteration, by
equivariance. -/
theorem stepW_iter (f : A → WriterT W m ((B ⊕ A) ⊕ A)) :
    stepW (iter f) = kcomp (iter (stepW f)) (liftPure (distr (B := B) (A := A) (W := W))) := by
  funext p
  obtain ⟨a, v⟩ := p
  simp only [kcomp, liftPure, stepW, iter_shift' f v a, map_eq_pure_bind, bind_assoc, pure_bind,
    Function.comp_apply, shift]

/-- The codiagonal law for `WriterT W m`. -/
theorem codiagonal (f : A → WriterT W m ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f) := by
  funext a
  apply WriterT.ext
  rw [run_iter, run_iter, stepW_iter, ← flattenBody_stepW,
    ← LawfulElgotMonad.codiagonal (m := m), ← mapReturn_liftPure,
    ← LawfulElgotMonad.naturality (m := m)]

/-- Pure uniformity for `WriterT W m`: the comparison map `h : A → C` enlarges purely to
`Prod.map h id`.  No equivariance and no extra structure on `W` are needed — the log is *produced*
by the body and never *consumed* by it, so both sides of the square prepend the same prefix. -/
theorem uniformity (f : A → WriterT W m (B ⊕ A)) (g : C → WriterT W m (B ⊕ C)) (h : A → C)
    (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g) :
    iter f = kcomp (liftPure h) (iter g) := by
  have hcomm : ∀ a : A, WriterT.run (g (h a))
      = WriterT.run (f a) >>= fun p ↦ pure (Sum.map id h p.1, p.2) := by
    intro a
    have hx : WriterT.run (kcomp f (liftPure (Sum.map id h)) a)
        = WriterT.run (kcomp (liftPure h) g a) := by rw [comm]
    rw [run_kcomp, run_kcomp, run_liftPure] at hx
    simp only [run_liftPure, map_pure, pure_bind, mul_one, one_mul] at hx
    rw [show (fun q : (B ⊕ C) × W ↦ (q.1, q.2)) = id from rfl, id_map] at hx
    exact hx.symm
  have hsq : kcomp (stepW f) (liftPure (Sum.map (id : B × W → B × W) (Prod.map h (id : W → W))))
      = kcomp (liftPure (Prod.map h (id : W → W))) (stepW g) := by
    funext p
    obtain ⟨a, v⟩ := p
    simp only [kcomp, liftPure, Function.comp_apply, pure_bind, stepW, Prod.map, id_eq]
    rw [hcomm a]
    simp only [bind_assoc, pure_bind]
    congr 1
    funext q
    obtain ⟨s, w'⟩ := q
    cases s <;> simp [distr, Sum.map, Prod.map]
  funext a
  apply WriterT.ext
  have h2 := congrFun (LawfulElgotMonad.uniformity (m := m) (stepW f) (stepW g)
    (Prod.map h (id : W → W)) hsq) (a, 1)
  simp only [kcomp, liftPure, Function.comp_apply, pure_bind, Prod.map, id_eq] at h2
  rw [run_iter, h2, ← run_iter, run_kcomp, run_liftPure]
  simp only [pure_bind, one_mul, id_map']

/-- `WriterT W m` is a complete Elgot monad whenever `m` is, for **every** monoid `W`. -/
instance instLawfulElgotMonad : LawfulElgotMonad (WriterT W m) where
  fixpoint := fixpoint
  naturality := naturality
  codiagonal := codiagonal
  uniformity := uniformity

/-! ### Comparison with the base monad -/

/-- Erase the accumulated output. -/
def forget (c : WriterT W m A) : m A := Prod.fst <$> WriterT.run c

/-- Erasing the output is a morphism of Elgot monads: `forget` commutes with iteration.  So the
writer transformer is a conservative extension — the value component of a writer loop is exactly
the corresponding loop in `m`. -/
theorem forget_iter (f : A → WriterT W m (B ⊕ A)) (a : A) :
    forget (iter f a) = iter (fun a ↦ forget (f a)) a := by
  have hnat := LawfulElgotMonad.naturality (m := m) (stepW f)
    (liftPure (Prod.fst : B × W → B))
  rw [mapReturn_liftPure] at hnat
  have huni := LawfulElgotMonad.uniformity (m := m)
    (kcomp (stepW f) (liftPure (Sum.map (Prod.fst : B × W → B) (id : A × W → A × W))))
    (fun a ↦ forget (f a)) (Prod.fst : A × W → A) ?comm
  · have h1 := congrFun huni (a, 1)
    have h2 := congrFun hnat (a, 1)
    simp only [kcomp, liftPure, Function.comp_apply, pure_bind] at h1 h2
    rw [forget, run_iter, ← bind_pure_comp, ← Function.comp_def]
    exact h2.trans h1
  case comm =>
    funext p
    obtain ⟨a', v⟩ := p
    simp only [kcomp, liftPure, Function.comp_apply, pure_bind, stepW, bind_assoc, forget,
      map_eq_pure_bind]
    congr 1
    funext q
    obtain ⟨s, w'⟩ := q
    cases s <;> simp [distr, Sum.map]

end

end Isotope.Elgot.Transformer.Writer
