import Mathlib.Data.Part

/-!
# Complete Elgot monads on types

We use the convention that `Sum.inl` is a returned value and `Sum.inr` is a
recursive call.  Thus `iter f` is the dagger of the Kleisli arrow
`f : A → m (B ⊕ A)`.

Uniformity is deliberately restricted to maps `h : A → C` in **Type**, embedded
in the Kleisli category by `pure`.  It is not asserted for arbitrary effectful
Kleisli arrows.
-/

namespace Isotope.Elgot

universe u

/-- An iteration operator on a monad. -/
class Iterate (m : Type u → Type u) where
  iter {A B : Type u} : (A → m (B ⊕ A)) → A → m B

export Iterate (iter)

/-- Kleisli composition, in diagrammatic order. -/
def kcomp {m : Type u → Type u} [Monad m] {A B C : Type u}
    (f : A → m B) (g : B → m C) : A → m C :=
  fun a ↦ f a >>= g

infixr:55 " ≫ₖ " => kcomp

/-- Embed an ordinary function as a pure Kleisli arrow. -/
def liftPure {m : Type u → Type u} [Monad m] {A B : Type u} (f : A → B) : A → m B :=
  pure ∘ f

/-- Act on the returned (left) summand of an iteration body. -/
def mapReturn {m : Type u → Type u} [Monad m] {A B C : Type u}
    (f : A → m (B ⊕ A)) (g : B → m C) : A → m (C ⊕ A) :=
  fun a ↦ f a >>= Sum.elim (fun b ↦ g b >>= pure ∘ Sum.inl) (pure ∘ Sum.inr)

/-- Merge two successive recursive summands. -/
def flatten {A B : Type u} : (B ⊕ A) ⊕ A → B ⊕ A :=
  Sum.elim id Sum.inr

/-- Apply `flatten` to the result of an effectful iteration body. -/
def flattenBody {m : Type u → Type u} [Monad m] {A B : Type u}
    (f : A → m ((B ⊕ A) ⊕ A)) : A → m (B ⊕ A) :=
  kcomp f (liftPure flatten)

/-- The Conway/complete-Elgot equations, with pure uniformity. -/
class LawfulElgotMonad (m : Type u → Type u) [Monad m] [LawfulMonad m] [Iterate m] : Prop where
  fixpoint {A B : Type u} (f : A → m (B ⊕ A)) :
    iter f = fun a ↦ f a >>= Sum.elim pure (iter f)
  naturality {A B C : Type u} (f : A → m (B ⊕ A)) (g : B → m C) :
    kcomp (iter f) g = iter (mapReturn f g)
  codiagonal {A B : Type u} (f : A → m ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f)
  uniformity {A B C : Type u} (f : A → m (B ⊕ A)) (g : C → m (B ⊕ C))
      (h : A → C)
      (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g) :
    iter f = kcomp (liftPure h) (iter g)

namespace Part

variable {A B C : Type u}

/-- A finite successful execution of an iteration body. -/
inductive Runs {A B : Type u} (f : A → _root_.Part (B ⊕ A)) : A → B → Prop
  | done {a b} : Sum.inl b ∈ f a → Runs f a b
  | more {a a' b} : Sum.inr a' ∈ f a → Runs f a' b → Runs f a b

theorem Runs.unique {A B : Type u} {f : A → _root_.Part (B ⊕ A)}
    {a : A} {b c : B} (hb : Runs f a b) (hc : Runs f a c) : b = c := by
  induction hb generalizing c with
  | done h =>
      cases hc with
      | done h' => exact Sum.inl.inj (_root_.Part.mem_unique h h')
      | more h' _ => cases _root_.Part.mem_unique h h'
  | more h hr ih =>
      cases hc with
      | done h' => cases _root_.Part.mem_unique h h'
      | more h' hc =>
          have := Sum.inr.inj (_root_.Part.mem_unique h h')
          subst this
          exact ih hc

/-- The partial value returned by the unique finite successful run, if one exists. -/
noncomputable def run {A B : Type u} (f : A → _root_.Part (B ⊕ A)) (a : A) : _root_.Part B where
  Dom := ∃ b, Runs f a b
  get h := Classical.choose h

theorem mem_run_iff {A B : Type u} (f : A → _root_.Part (B ⊕ A)) (a : A) (b : B) :
    b ∈ run f a ↔ Runs f a b := by
  constructor
  · rintro ⟨h, rfl⟩
    exact Classical.choose_spec h
  · intro hb
    refine ⟨⟨b, hb⟩, ?_⟩
    exact Runs.unique (Classical.choose_spec ⟨b, hb⟩) hb

noncomputable instance : Iterate _root_.Part where
  iter := run

theorem mem_iter_iff {A B : Type u} (f : A → _root_.Part (B ⊕ A)) (a : A) (b : B) :
    b ∈ iter f a ↔ Runs f a b := mem_run_iff f a b

theorem mem_kcomp_iff (f : A → _root_.Part B) (g : B → _root_.Part C) (a : A) (c : C) :
    c ∈ kcomp f g a ↔ ∃ b, b ∈ f a ∧ c ∈ g b := by
  simpa only [kcomp, _root_.Part.bind_eq_bind] using
    (_root_.Part.mem_bind_iff (f := f a) (g := g) (b := c))

theorem mem_mapReturn_iff (f : A → _root_.Part (B ⊕ A)) (g : B → _root_.Part C)
    (a : A) (s : C ⊕ A) :
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
        exact Or.inl ⟨b, c, hx, hc, _root_.Part.mem_some_iff.mp hs⟩
    | inr a' => exact Or.inr ⟨a', hx, _root_.Part.mem_some_iff.mp hs⟩
  · rintro (⟨b, c, hb, hc, rfl⟩ | ⟨a', ha, rfl⟩)
    · refine ⟨Sum.inl b, hb, ?_⟩
      change Sum.inl c ∈ kcomp g (pure ∘ Sum.inl) b
      rw [mem_kcomp_iff]
      exact ⟨c, hc, _root_.Part.mem_some _⟩
    · exact ⟨Sum.inr a', ha, _root_.Part.mem_some _⟩

theorem fixpoint (f : A → _root_.Part (B ⊕ A)) :
    iter f = fun a ↦ f a >>= Sum.elim pure (iter f) := by
  funext a
  apply _root_.Part.ext
  intro b
  rw [mem_iter_iff]
  constructor
  · intro h
    cases h with
    | done hs =>
        change b ∈ kcomp f (Sum.elim pure (iter f)) a
        rw [mem_kcomp_iff]
        exact ⟨Sum.inl b, hs, _root_.Part.mem_some b⟩
    | more hs hr =>
        change b ∈ kcomp f (Sum.elim pure (iter f)) a
        rw [mem_kcomp_iff]
        exact ⟨Sum.inr _, hs, (mem_iter_iff _ _ _).2 hr⟩
  · change b ∈ kcomp f (Sum.elim pure (iter f)) a → _
    rw [mem_kcomp_iff]
    rintro ⟨s, hs, hb⟩
    cases s with
    | inl b' =>
        have : b = b' := (_root_.Part.mem_some_iff.mp hb)
        subst this
        exact .done hs
    | inr a' => exact .more hs ((mem_iter_iff _ _ _).1 hb)

theorem runs_mapReturn_iff (f : A → _root_.Part (B ⊕ A)) (g : B → _root_.Part C) (a : A) (c : C) :
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

theorem naturality (f : A → _root_.Part (B ⊕ A)) (g : B → _root_.Part C) :
    kcomp (iter f) g = iter (mapReturn f g) := by
  funext a
  apply _root_.Part.ext
  intro c
  rw [mem_iter_iff, runs_mapReturn_iff, mem_kcomp_iff]
  constructor <;> rintro ⟨b, hb, hc⟩
  · exact ⟨b, (mem_iter_iff _ _ _).1 hb, hc⟩
  · exact ⟨b, (mem_iter_iff _ _ _).2 hb, hc⟩

theorem mem_flattenBody_iff (f : A → _root_.Part ((B ⊕ A) ⊕ A)) (a : A) (s : B ⊕ A) :
    s ∈ flattenBody f a ↔ ∃ x, x ∈ f a ∧ flatten x = s := by
  rw [show flattenBody f = kcomp f (liftPure flatten) by rfl, mem_kcomp_iff]
  constructor <;> rintro ⟨x, hx, hs⟩
  · exact ⟨x, hx, (_root_.Part.mem_some_iff.mp hs).symm⟩
  · exact ⟨x, hx, _root_.Part.mem_some_iff.mpr hs.symm⟩

theorem runs_flatten_cases (f : A → _root_.Part ((B ⊕ A) ⊕ A))
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

theorem runs_flatten_of_left (f : A → _root_.Part ((B ⊕ A) ⊕ A))
    {a : A} {b : B} (h : Runs f a (Sum.inl b)) : Runs (flattenBody f) a b :=
  (runs_flatten_cases f h).1 b rfl

theorem runs_flatten_append (f : A → _root_.Part ((B ⊕ A) ⊕ A))
    {a a' : A} {b : B} (h : Runs f a (Sum.inr a'))
    (tail : Runs (flattenBody f) a' b) : Runs (flattenBody f) a b :=
  (runs_flatten_cases f h).2 a' b rfl tail

theorem runs_flatten_of_nested (f : A → _root_.Part ((B ⊕ A) ⊕ A))
    {a : A} {b : B} (h : Runs (iter f) a b) : Runs (flattenBody f) a b := by
  induction h with
  | done hs => exact runs_flatten_of_left f ((mem_iter_iff _ _ _).1 hs)
  | more hs hr ih => exact runs_flatten_append f ((mem_iter_iff _ _ _).1 hs) ih

theorem runs_nested_of_flatten (f : A → _root_.Part ((B ⊕ A) ⊕ A))
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

theorem codiagonal (f : A → _root_.Part ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f) := by
  funext a
  apply _root_.Part.ext
  intro b
  rw [mem_iter_iff, mem_iter_iff]
  exact ⟨runs_flatten_of_nested f, runs_nested_of_flatten f⟩

theorem uniform_step (f : A → _root_.Part (B ⊕ A)) (g : C → _root_.Part (B ⊕ C))
    (h : A → C)
    (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g)
    (a : A) (t : B ⊕ C) :
    t ∈ g (h a) ↔ ∃ s, s ∈ f a ∧ Sum.map id h s = t := by
  have square := congrFun comm a
  constructor
  · intro ht
    have hr : t ∈ kcomp (liftPure h) g a := by
      rw [mem_kcomp_iff]
      exact ⟨h a, _root_.Part.mem_some _, ht⟩
    rw [← square, mem_kcomp_iff] at hr
    rcases hr with ⟨s, hs, ht⟩
    exact ⟨s, hs, (_root_.Part.mem_some_iff.mp ht).symm⟩
  · rintro ⟨s, hs, rfl⟩
    have hl : Sum.map id h s ∈ kcomp f (liftPure (Sum.map id h)) a := by
      rw [mem_kcomp_iff]
      exact ⟨s, hs, _root_.Part.mem_some _⟩
    rw [square, mem_kcomp_iff] at hl
    rcases hl with ⟨c, hc, ht⟩
    have hcEq : c = h a := _root_.Part.mem_some_iff.mp hc
    subst c
    exact ht

theorem runs_uniform_forward (f : A → _root_.Part (B ⊕ A))
    (g : C → _root_.Part (B ⊕ C)) (h : A → C)
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

theorem runs_uniform_reverse (f : A → _root_.Part (B ⊕ A))
    (g : C → _root_.Part (B ⊕ C)) (h : A → C)
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

theorem uniformity (f : A → _root_.Part (B ⊕ A)) (g : C → _root_.Part (B ⊕ C))
    (h : A → C)
    (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g) :
    iter f = kcomp (liftPure h) (iter g) := by
  funext a
  apply _root_.Part.ext
  intro b
  rw [mem_iter_iff, mem_kcomp_iff]
  constructor
  · intro hr
    exact ⟨h a, _root_.Part.mem_some _, (mem_iter_iff _ _ _).2 (runs_uniform_forward f g h comm hr)⟩
  · rintro ⟨c, hc, hb⟩
    have hcEq : c = h a := _root_.Part.mem_some_iff.mp hc
    exact runs_uniform_reverse f g h comm ((mem_iter_iff _ _ _).1 hb) a hcEq

noncomputable instance : LawfulElgotMonad _root_.Part where
  fixpoint := fixpoint
  naturality := naturality
  codiagonal := codiagonal
  uniformity := uniformity

section Examples

@[simp] theorem iter_immediate (a : A) (b : B) :
    iter (fun _ : A ↦ _root_.Part.some (Sum.inl b)) a = _root_.Part.some b := by
  apply _root_.Part.ext
  intro b'
  rw [mem_iter_iff, _root_.Part.mem_some_iff]
  constructor
  · intro hr
    cases hr with
    | done hs => exact Sum.inl.inj (_root_.Part.mem_some_iff.mp hs)
    | more hs _ => cases _root_.Part.mem_some_iff.mp hs
  · intro hb
    subst b'
    exact .done (_root_.Part.mem_some _)

@[simp] theorem iter_forever (a : A) :
    iter (B := B) (fun a : A ↦ _root_.Part.some (Sum.inr a)) a =
      (_root_.Part.none : _root_.Part B) := by
  apply _root_.Part.ext
  intro b
  rw [mem_iter_iff]
  constructor
  · intro hr
    induction hr with
    | done hs => cases _root_.Part.mem_some_iff.mp hs
    | more _ _ ih => exact ih
  · exact (_root_.Part.notMem_none b).elim

end Examples

end Part

end Isotope.Elgot
