import Isotope.Elgot.Basic
import Mathlib.Data.Set.Functor
import Mathlib.Data.Set.Lattice
import Mathlib.Order.FixedPoints
import Mathlib.Logic.Relation

/-!
# The powerset monad as a complete Elgot monad

Unbounded nondeterminism, modelled by `Set`, with iteration given by *reachability*: `iter f a`
is the set of values produced by some finite successful unfolding of the body `f`.

`Set` is not a global `Monad` in Mathlib (`Set.monad` is a `protected def`), so the whole
development lives in an `attribute [local instance] Set.monad` section, exactly as Mathlib's own
`Set.instLawfulMonad` does.  The instances declared here are nonetheless global.

## Semantic caveat

This is the *angelic* (partial-correctness) powerset model: divergence is identified with failure.
`iter (fun a ↦ {Sum.inr a}) a = ∅`, and `iter (fun a ↦ {Sum.inl b, Sum.inr a}) a = {b}`, so
"returns `b`, or diverges" is denoted exactly as "returns `b`".  All four Elgot laws hold; the model
is simply not divergence-sensitive.  Distinguishing divergence needs a different carrier.
-/

namespace Isotope.Elgot.Nondet

universe u

variable {A B C : Type u}

section

attribute [local instance] Set.monad

/-! ### Membership lemmas for the `Set` monad -/

/-- Membership in a `pure`. -/
@[simp] theorem mem_pure_iff (a b : A) : b ∈ (pure a : Set A) ↔ b = a := Iff.rfl

/-- Membership in a monadic bind. -/
@[simp] theorem mem_bind_iff (s : Set A) (f : A → Set B) (b : B) :
    b ∈ (s >>= f) ↔ ∃ a ∈ s, b ∈ f a := by
  simp [Set.bind_def]

/-- Membership in a Kleisli composite. -/
theorem mem_kcomp_iff (f : A → Set B) (g : B → Set C) (a : A) (c : C) :
    c ∈ kcomp f g a ↔ ∃ b, b ∈ f a ∧ c ∈ g b := by
  simp [kcomp]

/-- Membership in a pure Kleisli arrow. -/
theorem mem_liftPure_iff (h : A → B) (a : A) (b : B) :
    b ∈ (liftPure h a : Set B) ↔ b = h a := Iff.rfl

/-- Membership in `mapReturn f g`: either a returned value postprocessed by `g`, or a
recursive call passed through unchanged. -/
theorem mem_mapReturn_iff (f : A → Set (B ⊕ A)) (g : B → Set C) (a : A) (s : C ⊕ A) :
    s ∈ mapReturn f g a ↔
      (∃ b c, Sum.inl b ∈ f a ∧ c ∈ g b ∧ s = Sum.inl c) ∨
      (∃ a', Sum.inr a' ∈ f a ∧ s = Sum.inr a') := by
  change s ∈ kcomp f (Sum.elim (fun b ↦ kcomp g (pure ∘ Sum.inl) b) (pure ∘ Sum.inr)) a ↔ _
  rw [mem_kcomp_iff]
  constructor
  · rintro ⟨x, hx, hs⟩
    cases x with
    | inl b =>
        change s ∈ kcomp g (pure ∘ Sum.inl) b at hs
        rw [mem_kcomp_iff] at hs
        rcases hs with ⟨c, hc, hs⟩
        exact Or.inl ⟨b, c, hx, hc, hs⟩
    | inr a' => exact Or.inr ⟨a', hx, hs⟩
  · rintro (⟨b, c, hb, hc, rfl⟩ | ⟨a', ha, rfl⟩)
    · refine ⟨Sum.inl b, hb, ?_⟩
      change Sum.inl c ∈ kcomp g (pure ∘ Sum.inl) b
      rw [mem_kcomp_iff]
      exact ⟨c, hc, rfl⟩
    · exact ⟨Sum.inr a', ha, rfl⟩

/-- Membership in `flattenBody f`: the image of `f a` under `flatten`. -/
theorem mem_flattenBody_iff (f : A → Set ((B ⊕ A) ⊕ A)) (a : A) (s : B ⊕ A) :
    s ∈ flattenBody f a ↔ ∃ x, x ∈ f a ∧ flatten x = s := by
  rw [show flattenBody f = kcomp f (liftPure flatten) by rfl, mem_kcomp_iff]
  constructor <;> rintro ⟨x, hx, hs⟩
  · exact ⟨x, hx, hs.symm⟩
  · exact ⟨x, hx, hs.symm⟩

/-! ### Iteration by reachability -/

/-- A finite successful execution of a nondeterministic iteration body. -/
inductive Runs {A B : Type u} (f : A → Set (B ⊕ A)) : A → B → Prop
  | done {a b} : Sum.inl b ∈ f a → Runs f a b
  | more {a a' b} : Sum.inr a' ∈ f a → Runs f a' b → Runs f a b

/-- Iteration on the powerset monad: the set of values reachable by a finite successful run. -/
instance instIterateSet : Iterate.{u} Set where
  iter f a := {b | Runs f a b}

/-- `iter` is reachability, by definition. -/
@[simp] theorem mem_iter_iff (f : A → Set (B ⊕ A)) (a : A) (b : B) :
    b ∈ iter f a ↔ Runs f a b := Iff.rfl

/-! ### The Elgot laws -/

/-- Unrolling the loop once. -/
theorem fixpoint (f : A → Set (B ⊕ A)) :
    iter f = fun a ↦ f a >>= Sum.elim pure (iter f) := by
  funext a
  apply Set.ext
  intro b
  rw [mem_iter_iff]
  constructor
  · intro h
    cases h with
    | done hs =>
        change b ∈ kcomp f (Sum.elim pure (iter f)) a
        rw [mem_kcomp_iff]
        exact ⟨Sum.inl b, hs, rfl⟩
    | more hs hr =>
        change b ∈ kcomp f (Sum.elim pure (iter f)) a
        rw [mem_kcomp_iff]
        exact ⟨Sum.inr _, hs, (mem_iter_iff _ _ _).2 hr⟩
  · change b ∈ kcomp f (Sum.elim pure (iter f)) a → _
    rw [mem_kcomp_iff]
    rintro ⟨s, hs, hb⟩
    cases s with
    | inl b' =>
        have : b = b' := hb
        subst this
        exact .done hs
    | inr a' => exact .more hs ((mem_iter_iff _ _ _).1 hb)

/-- Runs of `mapReturn f g` are runs of `f` followed by one `g`-step. -/
theorem runs_mapReturn_iff (f : A → Set (B ⊕ A)) (g : B → Set C) (a : A) (c : C) :
    Runs (mapReturn f g) a c ↔ ∃ b, Runs f a b ∧ c ∈ g b := by
  constructor
  · intro h
    induction h with
    | done hdone =>
        rw [mem_mapReturn_iff] at hdone
        rcases hdone with (⟨b, c', hs, hc', heq⟩ | ⟨a', _, heq⟩)
        · have hcEq : _ = c' := Sum.inl.inj heq
          subst c'
          exact ⟨b, .done hs, hc'⟩
        · cases heq
    | more hmore hr ih =>
        rw [mem_mapReturn_iff] at hmore
        rcases hmore with (⟨b, c', _, _, heq⟩ | ⟨a', hs, heq⟩)
        · cases heq
        · have ha : _ = a' := Sum.inr.inj heq
          subst a'
          rcases ih with ⟨b, hb, hc⟩
          exact ⟨b, .more hs hb, hc⟩
  · rintro ⟨b, hr, hc⟩
    revert hc
    induction hr with
    | done hs =>
      intro hc
      apply Runs.done
      rw [mem_mapReturn_iff]
      exact Or.inl ⟨_, c, hs, hc, rfl⟩
    | more hs hr ih =>
      intro hc
      apply Runs.more
      · rw [mem_mapReturn_iff]
        exact Or.inr ⟨_, hs, rfl⟩
      · exact ih hc

/-- Postcomposition commutes with iteration. -/
theorem naturality (f : A → Set (B ⊕ A)) (g : B → Set C) :
    kcomp (iter f) g = iter (mapReturn f g) := by
  funext a
  apply Set.ext
  intro c
  rw [mem_iter_iff, runs_mapReturn_iff, mem_kcomp_iff]
  constructor <;> rintro ⟨b, hb, hc⟩
  · exact ⟨b, (mem_iter_iff _ _ _).1 hb, hc⟩
  · exact ⟨b, (mem_iter_iff _ _ _).2 hb, hc⟩

/-- The two ways a run of a nested body can be flattened. -/
theorem runs_flatten_cases (f : A → Set ((B ⊕ A) ⊕ A))
    {a : A} {s : B ⊕ A} (h : Runs f a s) :
    (∀ b, s = Sum.inl b → Runs (flattenBody f) a b) ∧
    (∀ a' b, s = Sum.inr a' → Runs (flattenBody f) a' b →
      Runs (flattenBody f) a b) := by
  induction h with
  | done hs =>
      constructor
      · intro b heq
        cases heq
        apply Runs.done
        rw [mem_flattenBody_iff]
        exact ⟨Sum.inl (Sum.inl _), hs, rfl⟩
      · intro a' b heq
        cases heq
        intro tail
        apply Runs.more
        · rw [mem_flattenBody_iff]
          exact ⟨Sum.inl (Sum.inr _), hs, rfl⟩
        · exact tail
  | more hs hr ih =>
      constructor
      · intro b heq
        apply Runs.more
        · rw [mem_flattenBody_iff]
          exact ⟨Sum.inr _, hs, rfl⟩
        · exact ih.1 b heq
      · intro a' b heq tail
        apply Runs.more
        · rw [mem_flattenBody_iff]
          exact ⟨Sum.inr _, hs, rfl⟩
        · exact ih.2 a' b heq tail

/-- A run of the nested body returning a value is a run of the flattened body. -/
theorem runs_flatten_of_left (f : A → Set ((B ⊕ A) ⊕ A))
    {a : A} {b : B} (h : Runs f a (Sum.inl b)) : Runs (flattenBody f) a b :=
  (runs_flatten_cases f h).1 b rfl

/-- Runs of the flattened body compose along an outer recursive call. -/
theorem runs_flatten_append (f : A → Set ((B ⊕ A) ⊕ A))
    {a a' : A} {b : B} (h : Runs f a (Sum.inr a'))
    (tail : Runs (flattenBody f) a' b) : Runs (flattenBody f) a b :=
  (runs_flatten_cases f h).2 a' b rfl tail

/-- Nested iteration refines flattened iteration. -/
theorem runs_flatten_of_nested (f : A → Set ((B ⊕ A) ⊕ A))
    {a : A} {b : B} (h : Runs (iter f) a b) : Runs (flattenBody f) a b := by
  induction h with
  | done hs => exact runs_flatten_of_left f ((mem_iter_iff _ _ _).1 hs)
  | more hs hr ih => exact runs_flatten_append f ((mem_iter_iff _ _ _).1 hs) ih

/-- Flattened iteration refines nested iteration. -/
theorem runs_nested_of_flatten (f : A → Set ((B ⊕ A) ⊕ A))
    {a : A} {b : B} (h : Runs (flattenBody f) a b) : Runs (iter f) a b := by
  induction h with
  | done hs =>
      rw [mem_flattenBody_iff] at hs
      rcases hs with ⟨x, hx, heq⟩
      cases x with
      | inl s =>
          cases s with
          | inl b' =>
              have hb : b' = _ := Sum.inl.inj heq
              subst b'
              exact .done ((mem_iter_iff _ _ _).2 (.done hx))
          | inr a' => cases heq
      | inr a' => cases heq
  | more hs hr ih =>
      rw [mem_flattenBody_iff] at hs
      rcases hs with ⟨x, hx, heq⟩
      cases x with
      | inl s =>
          cases s with
          | inl b' => cases heq
          | inr a' =>
              have ha : a' = _ := Sum.inr.inj heq
              subst a'
              exact .more ((mem_iter_iff _ _ _).2 (.done hx)) ih
      | inr a' =>
          have ha : a' = _ := Sum.inr.inj heq
          subst a'
          cases ih with
          | done hi =>
              apply Runs.done
              rw [mem_iter_iff] at hi ⊢
              exact .more hx hi
          | more hi ht =>
              apply Runs.more
              · rw [mem_iter_iff] at hi ⊢
                exact .more hx hi
              · exact ht

/-- Iterating an iteration is iterating the flattened body. -/
theorem codiagonal (f : A → Set ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f) := by
  funext a
  apply Set.ext
  intro b
  rw [mem_iter_iff, mem_iter_iff]
  exact ⟨runs_flatten_of_nested f, runs_nested_of_flatten f⟩

/-- The uniformity square, read pointwise: `g (h a)` is exactly the `h`-pushforward of `f a`. -/
theorem uniform_step (f : A → Set (B ⊕ A)) (g : C → Set (B ⊕ C))
    (h : A → C)
    (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g)
    (a : A) (t : B ⊕ C) :
    t ∈ g (h a) ↔ ∃ s, s ∈ f a ∧ Sum.map id h s = t := by
  have square := congrFun comm a
  constructor
  · intro ht
    have hr : t ∈ kcomp (liftPure h) g a := by
      rw [mem_kcomp_iff]
      exact ⟨h a, rfl, ht⟩
    rw [← square, mem_kcomp_iff] at hr
    rcases hr with ⟨s, hs, ht⟩
    exact ⟨s, hs, ht.symm⟩
  · rintro ⟨s, hs, rfl⟩
    have hl : Sum.map id h s ∈ kcomp f (liftPure (Sum.map id h)) a := by
      rw [mem_kcomp_iff]
      exact ⟨s, hs, rfl⟩
    rw [square, mem_kcomp_iff] at hl
    rcases hl with ⟨c, hc, ht⟩
    have hcEq : c = h a := hc
    subst c
    exact ht

/-- Runs transport forwards along a uniformity square. -/
theorem runs_uniform_forward (f : A → Set (B ⊕ A))
    (g : C → Set (B ⊕ C)) (h : A → C)
    (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g)
    {a : A} {b : B} (hr : Runs f a b) : Runs g (h a) b := by
  induction hr with
  | done hs =>
      apply Runs.done
      rw [uniform_step f g h comm]
      exact ⟨Sum.inl _, hs, rfl⟩
  | more hs hr ih =>
      apply Runs.more
      · rw [uniform_step f g h comm]
        exact ⟨Sum.inr _, hs, rfl⟩
      · exact ih

/-- Runs transport backwards along a uniformity square.  Determinism is never used: the square
is an *equality* of sets, so every `g`-step out of `h a` has an `f`-preimage out of `a`. -/
theorem runs_uniform_reverse (f : A → Set (B ⊕ A))
    (g : C → Set (B ⊕ C)) (h : A → C)
    (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g)
    {c : C} {b : B} (hr : Runs g c b) : ∀ a, c = h a → Runs f a b := by
  induction hr with
  | done ht =>
      intro a ha
      rw [ha] at ht
      rw [uniform_step f g h comm] at ht
      rcases ht with ⟨s, hs, heq⟩
      cases s with
      | inl b' =>
          have hb : b' = _ := Sum.inl.inj heq
          subst b'
          exact .done hs
      | inr a' => cases heq
  | more ht hr ih =>
      intro a ha
      rw [ha] at ht
      rw [uniform_step f g h comm] at ht
      rcases ht with ⟨s, hs, heq⟩
      cases s with
      | inl b' => cases heq
      | inr a' =>
          have hc : h a' = _ := Sum.inr.inj heq
          exact .more hs (ih a' hc.symm)

/-- Iteration is uniform along pure maps. -/
theorem uniformity (f : A → Set (B ⊕ A)) (g : C → Set (B ⊕ C))
    (h : A → C)
    (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g) :
    iter f = kcomp (liftPure h) (iter g) := by
  funext a
  apply Set.ext
  intro b
  rw [mem_iter_iff, mem_kcomp_iff]
  constructor
  · intro hr
    exact ⟨h a, rfl, (mem_iter_iff _ _ _).2 (runs_uniform_forward f g h comm hr)⟩
  · rintro ⟨c, hc, hb⟩
    have hcEq : c = h a := hc
    exact runs_uniform_reverse f g h comm ((mem_iter_iff _ _ _).1 hb) a hcEq

/-- **The powerset monad is a complete Elgot monad.** -/
instance instLawfulElgotMonadSet : LawfulElgotMonad.{u} Set where
  fixpoint := fixpoint
  naturality := naturality
  codiagonal := codiagonal
  uniformity := uniformity

/-! ### Reachability is the least fixpoint

The issue asks that we connect `iter` to Mathlib's closure infrastructure.  We do so twice: once
via `OrderHom.lfp` on the complete lattice `A → Set B`, and once via `Relation.ReflTransGen`.
Neither presentation is used in the proofs above; the inductive `Runs` is the working definition
because its recursor is exactly what the bisimulation arguments need.
-/

/-- One unfolding of the loop, as a monotone endomap of `A → Set B`. -/
def step (f : A → Set (B ⊕ A)) : (A → Set B) →o (A → Set B) where
  toFun k a := (Sum.inl ⁻¹' f a) ∪ ⋃ a' ∈ (Sum.inr ⁻¹' f a), k a'
  monotone' _k _k' hk _a :=
    Set.union_subset_union_right _ (Set.iUnion₂_mono fun a' _ ↦ hk a')

/-- Reachability is the least fixpoint of one loop unfolding. -/
theorem iter_eq_lfp (f : A → Set (B ⊕ A)) : iter f = (step f).lfp := by
  apply le_antisymm
  · refine OrderHom.le_lfp _ ?_
    intro k hk a b hb
    induction hb with
    | done hs => exact hk _ (Or.inl hs)
    | more hs _ ih => exact hk _ (Or.inr (Set.mem_biUnion hs ih))
  · refine OrderHom.lfp_le _ ?_
    intro a b hb
    rcases hb with hb | hb
    · exact .done hb
    · rcases Set.mem_iUnion₂.mp hb with ⟨a', ha', hb⟩
      exact .more ha' hb

/-- The one-step recursive-call relation of an iteration body. -/
def stepRel (f : A → Set (B ⊕ A)) (a a' : A) : Prop := Sum.inr a' ∈ f a

/-- Reachability, spelled with Mathlib's reflexive-transitive closure. -/
theorem iter_eq_reflTransGen (f : A → Set (B ⊕ A)) (a : A) :
    iter f a = {b | ∃ a', Relation.ReflTransGen (stepRel f) a a' ∧ Sum.inl b ∈ f a'} := by
  apply Set.ext
  intro b
  constructor
  · intro hb
    induction hb with
    | done hs => exact ⟨_, .refl, hs⟩
    | more hs _ ih =>
        rcases ih with ⟨a'', hp, hs''⟩
        exact ⟨a'', hp.head hs, hs''⟩
  · rintro ⟨a', hp, hs⟩
    induction hp using Relation.ReflTransGen.head_induction_on with
    | refl => exact .done hs
    | head h' _ ih => exact .more h' ih

/-! ### Examples -/

/-- A body that immediately returns. -/
theorem iter_immediate (a : A) (b : B) :
    iter (fun _ : A ↦ ({Sum.inl b} : Set (B ⊕ A))) a = ({b} : Set B) := by
  apply Set.ext
  intro b'
  rw [mem_iter_iff]
  constructor
  · intro hr
    cases hr with
    | done hs => exact Sum.inl.inj hs
    | more hs _ => cases hs
  · rintro rfl
    exact .done rfl

/-- A body that always recurses diverges, and divergence is denoted by the empty set. -/
theorem iter_forever (a : A) :
    iter (B := B) (fun a : A ↦ ({Sum.inr a} : Set (B ⊕ A))) a = (∅ : Set B) := by
  apply Set.ext
  intro b
  rw [mem_iter_iff]
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hr
  induction hr with
  | done hs => cases hs
  | more _ _ ih => exact ih

/-- Binary branching: a body returning two values returns both. -/
theorem iter_coin (b₀ b₁ : B) (a : A) :
    iter (fun _ : A ↦ ({Sum.inl b₀, Sum.inl b₁} : Set (B ⊕ A))) a = ({b₀, b₁} : Set B) := by
  apply Set.ext
  intro b
  rw [mem_iter_iff]
  constructor
  · intro hr
    cases hr with
    | done hs =>
        rcases hs with hs | hs
        · exact Or.inl (Sum.inl.inj hs)
        · exact Or.inr (Sum.inl.inj hs)
    | more hs _ => rcases hs with hs | hs <;> cases hs
  · rintro (rfl | rfl)
    · exact .done (Or.inl rfl)
    · exact .done (Or.inr rfl)

/-- Divergence collapses: "return `b`, or loop forever" is denoted exactly as "return `b`". -/
theorem iter_diverge_or_return (a : A) (b : B) :
    iter (fun a : A ↦ ({Sum.inl b, Sum.inr a} : Set (B ⊕ A))) a = ({b} : Set B) := by
  apply Set.ext
  intro b'
  rw [mem_iter_iff]
  constructor
  · intro hr
    induction hr with
    | done hs =>
        rcases hs with hs | hs
        · exact Sum.inl.inj hs
        · cases hs
    | more hs _ ih =>
        rcases hs with hs | hs
        · cases hs
        · cases hs
          exact ih
  · rintro rfl
    exact .done (Or.inl rfl)

/-- The unbounded-nondeterminism body: from `n`, return `n` or loop with `n + 1`. -/
def countUp (n : ℕ) : Set (ℕ ⊕ ℕ) := {Sum.inl n, Sum.inr (n + 1)}

/-- Every value at or above the starting point is reachable. -/
theorem runs_countUp (n d : ℕ) : Runs countUp n (n + d) := by
  induction d generalizing n with
  | zero => exact .done (Or.inl rfl)
  | succ d ih =>
      refine .more (a' := n + 1) (Or.inr rfl) ?_
      have h := ih (n + 1)
      rwa [show n + 1 + d = n + (d + 1) by omega] at h

/-- A finitely-branching loop with infinitely many results: `countUp` accumulates all of `ℕ`. -/
theorem iter_countUp : iter countUp 0 = (Set.univ : Set ℕ) := by
  apply Set.eq_univ_of_forall
  intro k
  have := runs_countUp 0 k
  simpa using this

end

/-! ### Re-export on `SetM`

`SetM` is Mathlib's wrapper carrying a global `Monad` instance, so downstream users need no
`attribute [local instance]`.
-/

/-- Iteration on `SetM`. -/
instance instIterateSetM : Iterate.{u} SetM := instIterateSet

/-- **`SetM` is a complete Elgot monad.** -/
instance instLawfulElgotMonadSetM : LawfulElgotMonad.{u} SetM := instLawfulElgotMonadSet

end Isotope.Elgot.Nondet
