import Isotope.Elgot.Transformer.Writer
import Isotope.Elgot.Nondet
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Why no monoid can retain infinite output

`Isotope.Elgot.Transformer.Writer` iterates `WriterT W m` by discarding the output of a run that
never returns.  This file proves that this is *forced*: no iteration operator on `WriterT W m`
retains the output of a divergent loop, for **any** monoid `W` — including one already containing
"infinite words".

Three independent obstructions, in increasing order of specificity.  Each takes the iteration
operator and the single law it needs as **explicit arguments**, following
`Isotope.Elgot.Nondet.no_finite_lax_iteration`, so nothing here competes with the instances
declared in `Writer.lean`.

1. **Carrier** (`subsingleton_writerT_part`, `subsingleton_writerT_set`).  A writer computation
   `WriterT W m B = m (B × W)` delivers the log only paired with a returned value, so at an empty
   result type there is nowhere to put it.  Any two iteration operators agree there, for every `W`.
2. **Naturality** (`noReturn_shift`, and its `Part`/`Set` instantiations).  A body that is
   *parametric in the result type* and never returns is fixed by `mapReturn`, so naturality alone
   forces its denotation to be stable under `Nat.succ` on the result component, hence bottom.  This
   needs no hypothesis on `W` at all, so no completion of `W` can rescue it.
3. **Fixpoint** (`tellLoop_shift`, `no_left_fixed`, and instantiations).  The loop "emit `w`,
   recurse" is forced by the fixpoint law to satisfy `w * u = u` for every value `(b, u)` it
   denotes: the infinite product `w^ω` would have to be an actual element of `W` absorbed by `w`.
   In a length-graded monoid there is none.

The design lesson is (2): it is *naturality*, not the absence of infinite elements in `W`, that
does the killing.  On a trace carrier `m ((B × W) ⊕ W∞)` the argument fails, because `mapReturn`
leaves the `W∞` summand alone.  See `Isotope.Elgot.Transformer.Writer.Infinite`.
-/

namespace Isotope.Elgot.Transformer.Writer

universe u

variable {W : Type u} [Monoid W] {m : Type u → Type u} [Monad m] [LawfulMonad m] {A B C : Type u}

/-! ### 1. The carrier obstruction -/

/-- At an empty result type a writer computation carries no information, so every iteration
operator on `WriterT W Part` agrees on bodies returning `PEmpty`. -/
instance subsingleton_writerT_part : Subsingleton (WriterT W _root_.Part (PEmpty.{u + 1})) :=
  ⟨fun _ _ ↦ _root_.Part.ext fun x ↦ x.1.elim⟩

section

attribute [local instance] Set.monad

/-- The same, for unbounded nondeterminism. -/
instance subsingleton_writerT_set : Subsingleton (WriterT W Set.{u} (PEmpty.{u + 1})) :=
  ⟨fun _ _ ↦ funext fun x ↦ x.1.elim⟩

end

/-! ### 2. The naturality obstruction -/

/-- A body that runs `f0` and always recurses: productive, and parametric in the result type. -/
def noReturn (f0 : A → WriterT W m A) (B : Type u) : A → WriterT W m (B ⊕ A) :=
  fun a ↦ f0 a >>= (Pure.pure ∘ Sum.inr)

/-- `mapReturn` cannot touch a body that never returns. -/
theorem mapReturn_noReturn (f0 : A → WriterT W m A) (g : B → WriterT W m C) :
    mapReturn (noReturn f0 B) g = noReturn f0 C := by
  funext a
  apply WriterT.ext
  simp only [mapReturn, noReturn, run_bind, Function.comp_apply, run_pure, map_pure, bind_assoc,
    pure_bind, mul_one, Sum.elim_inr]

/-- Naturality alone forces the denotation of a return-free body to be stable under `Nat.succ` on
its result component.  No hypothesis on `W` is used. -/
theorem noReturn_shift
    (it : ∀ {A B : Type u}, (A → WriterT W m (B ⊕ A)) → A → WriterT W m B)
    (hnat : ∀ {A B C : Type u} (f : A → WriterT W m (B ⊕ A)) (g : B → WriterT W m C),
        kcomp (it f) g = it (mapReturn f g))
    (f0 : A → WriterT W m A) (a : A) :
    WriterT.run (it (noReturn f0 (ULift.{u, 0} ℕ)) a)
        >>= (fun p ↦ pure (ULift.up (p.1.down + 1), p.2))
      = WriterT.run (it (noReturn f0 (ULift.{u, 0} ℕ)) a) := by
  have h := congrFun (hnat (noReturn f0 (ULift.{u, 0} ℕ))
    (liftPure (fun n : ULift.{u, 0} ℕ ↦ ULift.up (n.down + 1)))) a
  rw [mapReturn_noReturn] at h
  have h2 := congrArg WriterT.run h
  simp only [kcomp, run_bind, liftPure, Function.comp_apply, run_pure, map_pure, mul_one] at h2
  exact h2

/-- A partial value stable under `Nat.succ` on its first component is undefined. -/
theorem part_bot_of_succ_stable {V : Type} (x : _root_.Part (ℕ × V))
    (h : x >>= (fun p ↦ pure (p.1 + 1, p.2)) = x) : x = _root_.Part.none := by
  rw [_root_.Part.eq_none_iff]
  rintro ⟨n, v⟩
  induction n using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    intro hmem
    rw [← h, _root_.Part.bind_eq_bind, _root_.Part.mem_bind_iff] at hmem
    obtain ⟨⟨k, u0⟩, hk, he⟩ := hmem
    rw [show (pure ((k, u0).1 + 1, (k, u0).2) : _root_.Part (ℕ × V)) = _root_.Part.some (k + 1, u0)
      from rfl, _root_.Part.mem_some_iff] at he
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ih k (by omega) _ hk

section

attribute [local instance] Set.monad

/-- A set of pairs stable under `Nat.succ` on the first component is empty: every member would
need a member of strictly smaller index. -/
theorem set_bot_of_succ_stable {V : Type} (S : Set (ℕ × V))
    (h : S >>= (fun p ↦ pure (p.1 + 1, p.2)) = S) : S = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  obtain ⟨n, v⟩ := p
  induction n using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    intro hmem
    rw [← h, Isotope.Elgot.Nondet.mem_bind_iff] at hmem
    obtain ⟨⟨k, u0⟩, hk, he⟩ := hmem
    rw [Isotope.Elgot.Nondet.mem_pure_iff] at he
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ih k (by omega) _ hk

end

/-! ### 3. The fixpoint obstruction -/

/-- The loop that emits `w` and recurses, forever. -/
def tellLoop (w : W) (B : Type u) : PUnit.{u + 1} → WriterT W m (B ⊕ PUnit.{u + 1}) :=
  fun _ ↦ (WriterT.mk (pure (Sum.inr PUnit.unit, w)) : WriterT W m (B ⊕ PUnit.{u + 1}))

/-- The fixpoint law alone forces the denotation of `tellLoop w` to be stable under multiplying
its output component by `w` on the left. -/
theorem tellLoop_shift
    (it : ∀ {A B : Type u}, (A → WriterT W m (B ⊕ A)) → A → WriterT W m B)
    (hfix : ∀ {A B : Type u} (f : A → WriterT W m (B ⊕ A)),
        it f = fun a ↦ f a >>= Sum.elim pure (it f))
    (w : W) (B : Type u) :
    WriterT.run (it (tellLoop w B) PUnit.unit)
      = (fun q : B × W ↦ (q.1, w * q.2)) <$> WriterT.run (it (tellLoop w B) PUnit.unit) := by
  conv_lhs => rw [hfix (tellLoop w B)]
  exact pure_bind _ _

/-- In a monoid graded by a length homomorphism, no element is fixed by left multiplication by an
element of positive length: the "infinite product `w^ω`" is not an element of `W`. -/
theorem no_left_fixed (len : W → ℕ) (hlen : ∀ a b : W, len (a * b) = len a + len b)
    (w : W) (hw : 0 < len w) (u : W) : w * u ≠ u := by
  intro h
  have := congrArg len h
  rw [hlen] at this
  omega

/-- A free monoid has no left fixed point of a generator. -/
theorem freeMonoid_no_left_fixed {E : Type u} (e : E) (u : FreeMonoid E) :
    FreeMonoid.of e * u ≠ u :=
  no_left_fixed FreeMonoid.length (fun a b ↦ FreeMonoid.length_mul a b) _
    (by simp [FreeMonoid.length_of]) u

/-- **Divergent output is not representable over `Part`.**  Any fixpoint-lawful iteration operator
sends the productive loop `tellLoop w` to the undefined computation, as soon as `w` has no left
fixed point.  In particular the log `w * w * ⋯` is never delivered. -/
theorem part_tellLoop_none {V : Type} [Monoid V] (w : V) (hw : ∀ u : V, w * u ≠ u)
    (it : ∀ {A B : Type}, (A → WriterT V _root_.Part (B ⊕ A)) → A → WriterT V _root_.Part B)
    (hfix : ∀ {A B : Type} (f : A → WriterT V _root_.Part (B ⊕ A)),
        it f = fun a ↦ f a >>= Sum.elim pure (it f))
    (B : Type) :
    WriterT.run (it (tellLoop w B) PUnit.unit) = _root_.Part.none := by
  have h := tellLoop_shift it hfix w B
  rw [_root_.Part.eq_none_iff]
  rintro ⟨b, u⟩ hmem
  have h2 : ((b, w * u) : B × V) ∈ WriterT.run (it (tellLoop w B) PUnit.unit) := by
    rw [h]
    exact _root_.Part.mem_map _ hmem
  have h3 := _root_.Part.mem_unique h2 hmem
  simp only [Prod.mk.injEq] at h3
  exact hw u h3.2

section

attribute [local instance] Set.monad

/-- **Divergent output is not representable over `Set` either.**  Here the ℕ-grading is genuinely
needed rather than just `∀ u, w * u ≠ u`: the argument descends along a chain of members of
strictly decreasing length, and in the two-element group `{1, w}` the weaker hypothesis holds
while `w ^ 2 * u = u`.  The weaker hypothesis is insufficient *for this proof*; nothing here says
the theorem fails without it. -/
theorem set_tellLoop_empty {V : Type} [Monoid V] (w : V)
    (len : V → ℕ) (hlen : ∀ a b : V, len (a * b) = len a + len b) (hw : 0 < len w)
    (it : ∀ {A B : Type}, (A → WriterT V Set (B ⊕ A)) → A → WriterT V Set B)
    (hfix : ∀ {A B : Type} (f : A → WriterT V Set (B ⊕ A)),
        it f = fun a ↦ f a >>= Sum.elim pure (it f))
    (B : Type) : WriterT.run (it (tellLoop w B) PUnit.unit) = ∅ := by
  have h := tellLoop_shift it hfix w B
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  obtain ⟨b, u⟩ := p
  generalize hn : len u = n
  induction n using Nat.strong_induction_on generalizing u b with
  | _ n ih =>
    intro hmem
    rw [h] at hmem
    obtain ⟨⟨b', u'⟩, hb', he⟩ := hmem
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ih (len u') (by rw [← hn, hlen]; omega) _ _ rfl hb'

end

/-! ### 4. Information loss, made precise

Every finite approximant of a productive loop is distinguished by its log; the loop itself is not.
Stated at `Type 0`, since the countdown loop is indexed by `ℕ`. -/

section Loss

variable {V : Type} [Monoid V] {n : Type → Type} [Monad n] [LawfulMonad n]

/-- A loop that emits `w` on each of its `k` remaining steps, then returns. -/
def countdown (w : V) : ℕ → WriterT V n (Unit ⊕ ℕ)
  | 0 => WriterT.mk (pure (Sum.inl (), 1))
  | k + 1 => WriterT.mk (pure (Sum.inr k, w))

/-- A length homomorphism is multiplicative on powers. -/
theorem len_pow (len : V → ℕ) (h1 : len 1 = 0) (hlen : ∀ a b : V, len (a * b) = len a + len b)
    (w : V) : ∀ k : ℕ, len (w ^ k) = k * len w
  | 0 => by rw [pow_zero, h1, Nat.zero_mul]
  | k + 1 => by rw [pow_succ, hlen, len_pow len h1 hlen w k, Nat.succ_mul]

omit [LawfulMonad n] in
/-- Running one step of the countdown at zero. -/
theorem run_countdown_zero (w : V) :
    WriterT.run (countdown (n := n) w 0) = pure (Sum.inl (), 1) := rfl

omit [LawfulMonad n] in
/-- Running one step of the countdown at a successor. -/
theorem run_countdown_succ (w : V) (k : ℕ) :
    WriterT.run (countdown (n := n) w (k + 1)) = pure (Sum.inr k, w) := rfl

variable [Iterate n] [LawfulElgotMonad n]

/-- The countdown loop terminates and accumulates exactly `w ^ k`. -/
theorem countdown_run (w : V) : ∀ k : ℕ,
    WriterT.run (iter (countdown (n := n) w) k) = pure ((), w ^ k)
  | 0 => by
      rw [congrFun (fixpoint (countdown (n := n) w)) 0, run_bind, run_countdown_zero, pure_bind]
      simp only [Sum.elim_inl, run_pure, map_pure, one_mul, pow_zero]
  | k + 1 => by
      rw [congrFun (fixpoint (countdown (n := n) w)) (k + 1), run_bind, run_countdown_succ,
        pure_bind]
      simp only [Sum.elim_inr]
      rw [countdown_run w k]
      simp only [map_pure]
      rw [pow_succ']

/-- **Finite approximants are distinguished by their logs.**  Over `Part`, if `w` and `w'` differ
in length then the two countdown loops differ at every positive depth. -/
theorem countdown_distinguishes (len : V → ℕ) (h1 : len 1 = 0)
    (hlen : ∀ a b : V, len (a * b) = len a + len b) (w w' : V) (hne : len w ≠ len w')
    {k : ℕ} (hk : 0 < k) :
    iter (countdown (n := _root_.Part) w) k ≠ iter (countdown (n := _root_.Part) w') k := by
  intro h
  have hr := congrArg WriterT.run h
  rw [countdown_run, countdown_run] at hr
  have hx : ((), w ^ k) = ((), w' ^ k) := _root_.Part.some_inj.mp hr
  have := congrArg (fun p : Unit × V ↦ len p.2) hx
  simp only [len_pow len h1 hlen] at this
  exact hne (Nat.eq_of_mul_eq_mul_left hk this)

/-- **The limits are not distinguished.**  Over `Part`, every productive loop in a free monoid
denotes the undefined computation, whatever it emits — so the information separating the finite
approximants above is irrecoverably lost. -/
theorem tellLoop_indistinguishable {E : Type} (e e' : E) (B : Type) :
    iter (tellLoop (m := _root_.Part) (FreeMonoid.of e) B)
      = iter (tellLoop (m := _root_.Part) (FreeMonoid.of e') B) := by
  funext x
  apply WriterT.ext
  cases x
  rw [part_tellLoop_none _ (freeMonoid_no_left_fixed e) _ (fun f ↦ fixpoint f) B,
    part_tellLoop_none _ (freeMonoid_no_left_fixed e') _ (fun f ↦ fixpoint f) B]

end Loss

end Isotope.Elgot.Transformer.Writer
