import Isotope.Elgot.Basic
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# A finite-trace partiality monad

`FiniteTrace Σ A` is an opaque presentation of `Part (A × FreeMonoid Σ)`.
A terminating computation returns a value together with its finite trace, while
divergence has no observable trace.
This is the deterministic, finite-observation fragment of the older Discretion
trace-set model.  In particular it does not retain a productive infinite trace;
that richer construction requires a coinductive trace carrier (or trace sets).

Iteration concatenates the trace of every finite unfolding.  Uniformity is the
pure uniformity required by `LawfulElgotMonad`.
-/

namespace Isotope.Elgot

universe u

/-- Partial computations that record a finite list of events on termination. -/
structure FiniteTrace (Sigma : Type u) (A : Type u) where
  /-- The optional returned value paired with its complete finite trace. -/
  toPart : _root_.Part (A × FreeMonoid Sigma)

namespace FiniteTrace

variable {Sigma A B C : Type u}

@[ext] theorem ext (x y : FiniteTrace Sigma A) (h : x.toPart = y.toPart) : x = y := by
  cases x
  cases y
  cases h
  rfl

instance : Membership (A × FreeMonoid Sigma) (FiniteTrace Sigma A) :=
  ⟨fun x p ↦ p ∈ x.toPart⟩

instance : Monad (FiniteTrace Sigma) where
  pure a := ⟨_root_.Part.some (a, 1)⟩
  bind x f := ⟨x.toPart >>= fun (a, head) ↦
    (fun (b, tail) ↦ (b, head * tail)) <$> (f a).toPart⟩

instance : LawfulMonad (FiniteTrace Sigma) := LawfulMonad.mk'
  (id_map := by
    intro A x
    apply ext
    simpa [Functor.map] using (bind_pure x.toPart))
  (pure_bind := by
    intro A B a f
    apply ext
    simpa [Bind.bind, Pure.pure] using (id_map (f a).toPart))
  (bind_assoc := by
    intro A B C x f g
    apply ext
    simp only [Bind.bind, _root_.Part.bind_assoc]
    apply congrArg (_root_.Part.bind x.toPart)
    funext p
    rcases p with ⟨a, head⟩
    change (_root_.Part.map (fun p : B × FreeMonoid Sigma ↦ (p.1, head * p.2))
        (f a).toPart).bind _ =
      _root_.Part.map (fun p : C × FreeMonoid Sigma ↦ (p.1, head * p.2))
        ((f a).toPart.bind _)
    rw [_root_.Part.bind_map, _root_.Part.map_bind]
    apply congrArg (_root_.Part.bind (f a).toPart)
    funext p
    rcases p with ⟨b, middle⟩
    change _root_.Part.map _ (g b).toPart =
      _root_.Part.map _ (_root_.Part.map _ (g b).toPart)
    rw [_root_.Part.map_map]
    apply congrArg (_root_.Part.map · (g b).toPart)
    funext p
    rcases p with ⟨c, tail⟩
    simp [mul_assoc])
  (bind_pure_comp := by
    intro A B f x
    apply ext
    apply _root_.Part.ext
    intro p
    simp [_root_.Part.mem_bind_iff, Bind.bind, Pure.pure, Functor.map])

/-- A terminating trace computation. -/
def done (events : FreeMonoid Sigma) (a : A) : FiniteTrace Sigma A :=
  ⟨_root_.Part.some (a, events)⟩

/-- A divergent trace computation.  No infinite trace is retained. -/
def diverge : FiniteTrace Sigma A := ⟨_root_.Part.none⟩

/-- Emit one event and return unit. -/
def emit (event : Sigma) : FiniteTrace Sigma PUnit := done (FreeMonoid.of event) ⟨⟩

@[simp] theorem mem_done_iff (p : A × FreeMonoid Sigma) (events : FreeMonoid Sigma) (a : A) :
    p ∈ done events a ↔ p = (a, events) :=
  _root_.Part.mem_some_iff

@[simp] theorem not_mem_diverge (p : A × FreeMonoid Sigma) : p ∉ (diverge : FiniteTrace Sigma A) :=
  _root_.Part.notMem_none p

/-- A finite successful execution, recording the concatenated event trace. -/
inductive Runs (f : A → FiniteTrace Sigma (B ⊕ A)) : A → B → FreeMonoid Sigma → Prop
  | done {a b events} : (Sum.inl b, events) ∈ f a → Runs f a b events
  | more {a a' b head tail} : (Sum.inr a', head) ∈ f a →
      Runs f a' b tail → Runs f a b (head * tail)

theorem Runs.unique {f : A → FiniteTrace Sigma (B ⊕ A)} {a : A} {b c : B}
    {events events' : FreeMonoid Sigma} (hb : Runs f a b events) (hc : Runs f a c events') :
    b = c ∧ events = events' := by
  induction hb generalizing c events' with
  | done h =>
      cases hc with
      | done h' =>
          have hp := _root_.Part.mem_unique h h'
          cases hp
          exact ⟨rfl, rfl⟩
      | more h' _ =>
          have hp := _root_.Part.mem_unique h h'
          cases hp
  | more h hr ih =>
      cases hc with
      | done h' =>
          have hp := _root_.Part.mem_unique h h'
          cases hp
      | more h' hc =>
          have hp := _root_.Part.mem_unique h h'
          cases hp
          rcases ih hc with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl⟩

/-- The partial result and finite trace of the unique successful run. -/
noncomputable def run (f : A → FiniteTrace Sigma (B ⊕ A)) (a : A) : FiniteTrace Sigma B where
  toPart := {
    Dom := ∃ p : B × FreeMonoid Sigma, Runs f a p.1 p.2
    get := fun h ↦ Classical.choose h
  }

theorem mem_run_iff (f : A → FiniteTrace Sigma (B ⊕ A)) (a : A) (b : B)
    (events : FreeMonoid Sigma) :
    (b, events) ∈ run f a ↔ Runs f a b events := by
  constructor
  · rintro ⟨h, hp⟩
    have hs := Classical.choose_spec h
    change Runs f a ((run f a).toPart.get h).1 ((run f a).toPart.get h).2 at hs
    rw [hp] at hs
    exact hs
  · intro hr
    let hdom : ∃ p : B × FreeMonoid Sigma, Runs f a p.1 p.2 := ⟨(b, events), hr⟩
    refine ⟨hdom, ?_⟩
    have hs := Classical.choose_spec hdom
    rcases Runs.unique hs hr with ⟨hb, he⟩
    change Classical.choose hdom = (b, events)
    exact Prod.ext hb he

noncomputable instance : Iterate (FiniteTrace Sigma) where
  iter := run

@[simp] theorem mem_iter_iff (f : A → FiniteTrace Sigma (B ⊕ A)) (a : A) (b : B)
    (events : FreeMonoid Sigma) : (b, events) ∈ iter f a ↔ Runs f a b events :=
  mem_run_iff f a b events

theorem mem_bind_iff (x : FiniteTrace Sigma A) (g : A → FiniteTrace Sigma B) (b : B)
    (events : FreeMonoid Sigma) :
    (b, events) ∈ (x >>= g) ↔
      ∃ a head tail, (a, head) ∈ x ∧ (b, tail) ∈ g a ∧ events = head * tail := by
  change (b, events) ∈
      (_root_.Part.bind x.toPart (fun p : A × FreeMonoid Sigma ↦
        _root_.Part.map (fun q : B × FreeMonoid Sigma ↦ (q.1, p.2 * q.2))
          (g p.1).toPart)) ↔ _
  rw [_root_.Part.mem_bind_iff]
  constructor
  · rintro ⟨⟨a, head⟩, ha, hb⟩
    rw [_root_.Part.mem_map_iff] at hb
    rcases hb with ⟨⟨b', tail⟩, ht, hp⟩
    cases hp
    exact ⟨a, head, tail, ha, ht, rfl⟩
  · rintro ⟨a, head, tail, ha, ht, rfl⟩
    exact ⟨(a, head), ha,
      (_root_.Part.mem_map_iff (fun q : B × FreeMonoid Sigma ↦ (q.1, head * q.2))).2
        ⟨(b, tail), ht, rfl⟩⟩

theorem mem_kcomp_iff (f : A → FiniteTrace Sigma B) (g : B → FiniteTrace Sigma C) (a : A)
    (c : C) (events : FreeMonoid Sigma) :
    (c, events) ∈ kcomp f g a ↔
      ∃ b head tail, (b, head) ∈ f a ∧ (c, tail) ∈ g b ∧ events = head * tail := by
  exact mem_bind_iff (f a) g c events

theorem mem_pure_iff (a : A) (p : A × FreeMonoid Sigma) :
    p ∈ (pure a : FiniteTrace Sigma A) ↔ p = (a, 1) := by
  exact _root_.Part.mem_some_iff

theorem fixpoint (f : A → FiniteTrace Sigma (B ⊕ A)) :
    iter f = fun a ↦ f a >>= Sum.elim pure (iter f) := by
  funext a
  apply FiniteTrace.ext
  apply _root_.Part.ext
  rintro ⟨b, events⟩
  change ((b, events) ∈ iter f a) ↔
    ((b, events) ∈ f a >>= Sum.elim pure (iter f))
  rw [mem_iter_iff, mem_bind_iff]
  constructor
  · intro hr
    cases hr with
    | done hs => exact ⟨Sum.inl _, events, 1, hs, mem_pure_iff _ _ |>.2 rfl, by simp⟩
    | more hs hr =>
        exact ⟨Sum.inr _, _, _, hs, (mem_iter_iff _ _ _ _).2 hr, rfl⟩
  · rintro ⟨s, head, tail, hs, ht, he⟩
    cases s with
    | inl b' =>
        change (b, tail) ∈ (pure b' : FiniteTrace Sigma B) at ht
        rw [mem_pure_iff] at ht
        cases ht
        simp only [mul_one] at he
        exact he ▸ Runs.done hs
    | inr a' =>
        change (b, tail) ∈ iter f a' at ht
        exact he ▸ Runs.more hs ((mem_iter_iff _ _ _ _).1 ht)

theorem mem_mapReturn_iff (f : A → FiniteTrace Sigma (B ⊕ A)) (g : B → FiniteTrace Sigma C)
    (a : A) (s : C ⊕ A) (events : FreeMonoid Sigma) :
    (s, events) ∈ mapReturn f g a ↔
      (∃ b c head tail, (Sum.inl b, head) ∈ f a ∧ (c, tail) ∈ g b ∧
        s = Sum.inl c ∧ events = head * tail) ∨
      (∃ a' head, (Sum.inr a', head) ∈ f a ∧ s = Sum.inr a' ∧ events = head) := by
  change (s, events) ∈
    (f a >>= Sum.elim (fun b ↦ g b >>= pure ∘ Sum.inl) (pure ∘ Sum.inr)) ↔ _
  rw [mem_bind_iff]
  constructor
  · rintro ⟨x, head, rest, hx, hr, he⟩
    cases x with
    | inl b =>
        change (s, rest) ∈ g b >>= (pure ∘ Sum.inl) at hr
        rw [mem_bind_iff] at hr
        rcases hr with ⟨c, tail, unit, hc, hp, hrest⟩
        change (s, unit) ∈ (pure (Sum.inl c) : FiniteTrace Sigma (C ⊕ A)) at hp
        rw [mem_pure_iff] at hp
        cases hp
        simp only [mul_one] at hrest
        subst rest
        exact Or.inl ⟨b, c, head, tail, hx, hc, rfl, he⟩
    | inr a' =>
        change (s, rest) ∈ (pure (Sum.inr a') : FiniteTrace Sigma (C ⊕ A)) at hr
        rw [mem_pure_iff] at hr
        cases hr
        simp only [mul_one] at he
        exact Or.inr ⟨a', head, hx, rfl, he⟩
  · rintro ( ⟨b, c, head, tail, hb, hc, hs, he⟩ | ⟨a', head, ha, hs, he⟩ )
    · subst s
      refine ⟨Sum.inl b, head, tail, hb, ?_, he⟩
      change (Sum.inl c, tail) ∈ g b >>= (pure ∘ Sum.inl)
      rw [mem_bind_iff]
      exact ⟨c, tail, 1, hc, (mem_pure_iff _ _).2 rfl, by simp⟩
    · subst s
      exact ⟨Sum.inr a', head, 1, ha, (mem_pure_iff _ _).2 rfl, by simp [he]⟩

theorem runs_mapReturn_iff (f : A → FiniteTrace Sigma (B ⊕ A)) (g : B → FiniteTrace Sigma C)
    (a : A) (c : C) (events : FreeMonoid Sigma) :
    Runs (mapReturn f g) a c events ↔
      ∃ b head tail, Runs f a b head ∧ (c, tail) ∈ g b ∧ events = head * tail := by
  constructor
  · intro hr
    induction hr with
    | done hs =>
        rw [mem_mapReturn_iff] at hs
        rcases hs with (⟨b, c', head, tail, hb, hc, hec, he⟩ | ⟨a', _, _, hec, _⟩)
        · cases hec
          exact ⟨b, head, tail, .done hb, hc, he⟩
        · cases hec
    | more hs hr ih =>
        rw [mem_mapReturn_iff] at hs
        rcases hs with (⟨b, c', _, _, _, _, hec, _⟩ | ⟨a', first, ha, hea, he⟩)
        · cases hec
        · cases hea
          rcases ih with ⟨b, head, tail, hb, hc, hout⟩
          exact ⟨b, first * head, tail, .more ha hb, hc, by simp [he, hout, mul_assoc]⟩
  · rintro ⟨b, head, tail, hr, hc, he⟩
    revert tail events
    induction hr with
    | done hs =>
        intro tail events hc he
        subst tail
        apply Runs.done
        rw [mem_mapReturn_iff]
        exact Or.inl ⟨_, c, _, _, hs, hc, rfl, rfl⟩
    | more hs hr ih =>
        rename_i start next result first rest
        intro final events hc he
        subst final
        have hstep : (Sum.inr next, first) ∈ mapReturn f g start := by
          rw [mem_mapReturn_iff]
          exact Or.inr ⟨_, _, hs, rfl, rfl⟩
        have htail : Runs (mapReturn f g) next c (rest * events) :=
          ih (rest * events) events hc rfl
        simpa only [mul_assoc] using Runs.more hstep htail

theorem naturality (f : A → FiniteTrace Sigma (B ⊕ A)) (g : B → FiniteTrace Sigma C) :
    kcomp (iter f) g = iter (mapReturn f g) := by
  funext a
  apply ext
  apply _root_.Part.ext
  rintro ⟨c, events⟩
  change ((c, events) ∈ kcomp (iter f) g a) ↔
    ((c, events) ∈ iter (mapReturn f g) a)
  rw [mem_kcomp_iff, mem_iter_iff, runs_mapReturn_iff]
  constructor <;> rintro ⟨b, head, tail, hb, hc, he⟩
  · exact ⟨b, head, tail, (mem_iter_iff _ _ _ _).1 hb, hc, he⟩
  · exact ⟨b, head, tail, (mem_iter_iff _ _ _ _).2 hb, hc, he⟩

theorem mem_flattenBody_iff (f : A → FiniteTrace Sigma ((B ⊕ A) ⊕ A)) (a : A)
    (s : B ⊕ A) (events : FreeMonoid Sigma) :
    (s, events) ∈ flattenBody f a ↔ ∃ x, (x, events) ∈ f a ∧ flatten x = s := by
  change (s, events) ∈ kcomp f (liftPure flatten) a ↔ _
  rw [mem_kcomp_iff]
  constructor
  · rintro ⟨x, head, tail, hx, hs, he⟩
    change (s, tail) ∈ (pure (flatten x) : FiniteTrace Sigma (B ⊕ A)) at hs
    rw [mem_pure_iff] at hs
    cases hs
    simp only [mul_one] at he
    subst events
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, h⟩
    subst s
    exact ⟨x, events, 1, hx, (mem_pure_iff _ _).2 rfl, by simp⟩

theorem runs_flatten_cases (f : A → FiniteTrace Sigma ((B ⊕ A) ⊕ A))
    {a : A} {s : B ⊕ A} {events : FreeMonoid Sigma} (h : Runs f a s events) :
    (∀ b, s = Sum.inl b → Runs (flattenBody f) a b events) ∧
    (∀ a' b tail, s = Sum.inr a' → Runs (flattenBody f) a' b tail →
      Runs (flattenBody f) a b (events * tail)) := by
  induction h with
  | done hs =>
      constructor
      · intro b heq
        cases heq
        apply Runs.done
        rw [mem_flattenBody_iff]
        exact ⟨Sum.inl (Sum.inl _), hs, rfl⟩
      · intro a' b tail heq htail
        cases heq
        apply Runs.more
        · rw [mem_flattenBody_iff]
          exact ⟨Sum.inl (Sum.inr _), hs, rfl⟩
        · exact htail
  | more hs hr ih =>
      rename_i start next result first rest
      constructor
      · intro b heq
        apply Runs.more
        · rw [mem_flattenBody_iff]
          exact ⟨Sum.inr _, hs, rfl⟩
        · exact ih.1 b heq
      · intro a' b tail heq htail
        have hrest := ih.2 a' b tail heq htail
        have hstep : (Sum.inr next, first) ∈ flattenBody f start := by
          rw [mem_flattenBody_iff]
          exact ⟨Sum.inr _, hs, rfl⟩
        simpa only [mul_assoc] using Runs.more hstep hrest

theorem runs_flatten_of_left (f : A → FiniteTrace Sigma ((B ⊕ A) ⊕ A))
    {a : A} {b : B} {events : FreeMonoid Sigma} (h : Runs f a (Sum.inl b) events) :
    Runs (flattenBody f) a b events :=
  (runs_flatten_cases f h).1 b rfl

theorem runs_flatten_append (f : A → FiniteTrace Sigma ((B ⊕ A) ⊕ A))
    {a a' : A} {b : B} {head tail : FreeMonoid Sigma}
    (h : Runs f a (Sum.inr a') head) (htail : Runs (flattenBody f) a' b tail) :
    Runs (flattenBody f) a b (head * tail) :=
  (runs_flatten_cases f h).2 a' b tail rfl htail

theorem runs_flatten_of_nested (f : A → FiniteTrace Sigma ((B ⊕ A) ⊕ A))
    {a : A} {b : B} {events : FreeMonoid Sigma} (h : Runs (iter f) a b events) :
    Runs (flattenBody f) a b events := by
  induction h with
  | done hs => exact runs_flatten_of_left f ((mem_iter_iff _ _ _ _).1 hs)
  | more hs hr ih => exact runs_flatten_append f ((mem_iter_iff _ _ _ _).1 hs) ih

theorem runs_nested_of_flatten (f : A → FiniteTrace Sigma ((B ⊕ A) ⊕ A))
    {a : A} {b : B} {events : FreeMonoid Sigma} (h : Runs (flattenBody f) a b events) :
    Runs (iter f) a b events := by
  induction h with
  | done hs =>
      rw [mem_flattenBody_iff] at hs
      rcases hs with ⟨x, hx, heq⟩
      cases x with
      | inl s =>
          cases s with
          | inl b' =>
              cases heq
              exact .done ((mem_iter_iff _ _ _ _).2 (.done hx))
          | inr a' => cases heq
      | inr a' => cases heq
  | more hs hr ih =>
      rename_i start next result first rest
      rw [mem_flattenBody_iff] at hs
      rcases hs with ⟨x, hx, heq⟩
      cases x with
      | inl s =>
          cases s with
          | inl b' => cases heq
          | inr a' =>
              cases heq
              exact .more ((mem_iter_iff _ _ _ _).2 (.done hx)) ih
      | inr a' =>
          cases heq
          cases ih with
          | done hi =>
              apply Runs.done
              rw [mem_iter_iff] at hi ⊢
              exact .more hx hi
          | more hi ht =>
              rename_i next' middle rest'
              have hinner : Runs f start (Sum.inr next') (first * middle) := by
                rw [mem_iter_iff] at hi
                exact .more hx hi
              have houter : Runs (iter f) start result ((first * middle) * rest') :=
                .more ((mem_iter_iff _ _ _ _).2 hinner) ht
              simpa only [mul_assoc] using houter

theorem codiagonal (f : A → FiniteTrace Sigma ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f) := by
  funext a
  apply ext
  apply _root_.Part.ext
  rintro ⟨b, events⟩
  change ((b, events) ∈ iter (iter f) a) ↔
    ((b, events) ∈ iter (flattenBody f) a)
  rw [mem_iter_iff, mem_iter_iff]
  exact ⟨runs_flatten_of_nested f, runs_nested_of_flatten f⟩

theorem uniform_step (f : A → FiniteTrace Sigma (B ⊕ A)) (g : C → FiniteTrace Sigma (B ⊕ C))
    (h : A → C)
    (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g)
    (a : A) (t : B ⊕ C) (events : FreeMonoid Sigma) :
    (t, events) ∈ g (h a) ↔
      ∃ s, (s, events) ∈ f a ∧ Sum.map id h s = t := by
  have square := congrFun comm a
  constructor
  · intro ht
    have hr : (t, events) ∈ kcomp (liftPure h) g a := by
      rw [mem_kcomp_iff]
      exact ⟨h a, 1, events, (mem_pure_iff _ _).2 rfl, ht, by simp⟩
    rw [← square, mem_kcomp_iff] at hr
    rcases hr with ⟨s, head, tail, hs, hp, he⟩
    change (t, tail) ∈ (pure (Sum.map id h s) : FiniteTrace Sigma (B ⊕ C)) at hp
    rw [mem_pure_iff] at hp
    cases hp
    simp only [mul_one] at he
    subst events
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    have hl : (Sum.map id h s, events) ∈ kcomp f (liftPure (Sum.map id h)) a := by
      rw [mem_kcomp_iff]
      exact ⟨s, events, 1, hs, (mem_pure_iff _ _).2 rfl, by simp⟩
    rw [square, mem_kcomp_iff] at hl
    rcases hl with ⟨c, head, tail, hc, ht, he⟩
    change (c, head) ∈ (pure (h a) : FiniteTrace Sigma C) at hc
    rw [mem_pure_iff] at hc
    cases hc
    simp only [one_mul] at he
    subst events
    exact ht

theorem runs_uniform_forward (f : A → FiniteTrace Sigma (B ⊕ A))
    (g : C → FiniteTrace Sigma (B ⊕ C)) (h : A → C)
    (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g)
    {a : A} {b : B} {events : FreeMonoid Sigma} (hr : Runs f a b events) :
    Runs g (h a) b events := by
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

theorem runs_uniform_reverse (f : A → FiniteTrace Sigma (B ⊕ A))
    (g : C → FiniteTrace Sigma (B ⊕ C)) (h : A → C)
    (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g)
    {c : C} {b : B} {events : FreeMonoid Sigma} (hr : Runs g c b events) :
    ∀ a, c = h a → Runs f a b events := by
  induction hr with
  | done ht =>
      intro a ha
      rw [ha] at ht
      rw [uniform_step f g h comm] at ht
      rcases ht with ⟨s, hs, heq⟩
      cases s with
      | inl b' =>
          cases heq
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

theorem uniformity (f : A → FiniteTrace Sigma (B ⊕ A)) (g : C → FiniteTrace Sigma (B ⊕ C))
    (h : A → C)
    (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g) :
    iter f = kcomp (liftPure h) (iter g) := by
  funext a
  apply ext
  apply _root_.Part.ext
  rintro ⟨b, events⟩
  change ((b, events) ∈ iter f a) ↔
    ((b, events) ∈ kcomp (liftPure h) (iter g) a)
  rw [mem_iter_iff, mem_kcomp_iff]
  constructor
  · intro hr
    exact ⟨h a, 1, events, (mem_pure_iff _ _).2 rfl,
      (mem_iter_iff _ _ _ _).2 (runs_uniform_forward f g h comm hr), by simp⟩
  · rintro ⟨c, head, tail, hc, hb, he⟩
    change (c, head) ∈ (pure (h a) : FiniteTrace Sigma C) at hc
    rw [mem_pure_iff] at hc
    cases hc
    simp only [one_mul] at he
    subst events
    exact runs_uniform_reverse f g h comm ((mem_iter_iff _ _ _ _).1 hb) a rfl

noncomputable instance : LawfulElgotMonad (FiniteTrace Sigma) where
  fixpoint := fixpoint
  naturality := naturality
  codiagonal := codiagonal
  uniformity := uniformity

section Examples

@[simp] theorem iter_immediate (a : A) (b : B) (events : FreeMonoid Sigma) :
    iter (fun _ : A ↦ done events (Sum.inl b)) a = done events b := by
  apply ext
  apply _root_.Part.ext
  rintro ⟨b', output⟩
  change ((b', output) ∈ iter (fun _ : A ↦ done events (Sum.inl b)) a) ↔
    ((b', output) ∈ done events b)
  rw [mem_iter_iff, mem_done_iff]
  constructor
  · intro hr
    cases hr with
    | done hs =>
        rw [mem_done_iff] at hs
        cases hs
        rfl
    | more hs _ =>
        rw [mem_done_iff] at hs
        cases hs
  · intro hp
    rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
    exact .done ((mem_done_iff _ _ _).2 rfl)

@[simp] theorem iter_two_steps (b : B) (first second : FreeMonoid Sigma) :
    iter (B := B) (fun
      | Sum.inl _ => done first (Sum.inr (Sum.inr b))
      | Sum.inr _ => done second (Sum.inl b)) (Sum.inl b) =
      done (first * second) b := by
  apply ext
  apply _root_.Part.ext
  rintro ⟨b', output⟩
  change ((b', output) ∈ iter (fun
      | Sum.inl _ => done first (Sum.inr (Sum.inr b))
      | Sum.inr _ => done second (Sum.inl b)) (Sum.inl b)) ↔
    ((b', output) ∈ done (first * second) b)
  rw [mem_iter_iff, mem_done_iff]
  constructor
  · intro hr
    cases hr with
    | done hs =>
        rw [mem_done_iff] at hs
        cases hs
    | more hs hr =>
        rw [mem_done_iff] at hs
        cases hs
        cases hr with
        | done hs =>
            rw [mem_done_iff] at hs
            cases hs
            rfl
        | more hs _ =>
            rw [mem_done_iff] at hs
            cases hs
  · intro hp
    rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
    exact .more ((mem_done_iff _ _ _).2 rfl) (.done ((mem_done_iff _ _ _).2 rfl))

@[simp] theorem iter_forever (a : A) (events : FreeMonoid Sigma) :
    iter (B := B) (fun a : A ↦ done events (Sum.inr a)) a =
      (diverge : FiniteTrace Sigma B) := by
  apply ext
  apply _root_.Part.ext
  rintro ⟨b, output⟩
  change ((b, output) ∈ iter (fun a : A ↦ done events (Sum.inr a)) a) ↔
    ((b, output) ∈ (diverge : FiniteTrace Sigma B))
  rw [mem_iter_iff]
  constructor
  · intro hr
    induction hr with
    | done hs =>
        rw [mem_done_iff] at hs
        cases hs
    | more _ _ ih => exact (not_mem_diverge _ ih).elim
  · exact (not_mem_diverge (b, output)).elim

@[simp] theorem iter_divergent_body (a : A) :
    iter (B := B) (fun _ : A ↦ (diverge : FiniteTrace Sigma (B ⊕ A))) a =
      (diverge : FiniteTrace Sigma B) := by
  apply ext
  apply _root_.Part.ext
  rintro ⟨b, output⟩
  change ((b, output) ∈ iter (fun _ : A ↦ (diverge : FiniteTrace Sigma (B ⊕ A))) a) ↔
    ((b, output) ∈ (diverge : FiniteTrace Sigma B))
  rw [mem_iter_iff]
  constructor
  · intro hr
    cases hr with
    | done hs => exact (not_mem_diverge _ hs).elim
    | more hs _ => exact (not_mem_diverge _ hs).elim
  · exact (not_mem_diverge (b, output)).elim

end Examples

end FiniteTrace

end Isotope.Elgot
