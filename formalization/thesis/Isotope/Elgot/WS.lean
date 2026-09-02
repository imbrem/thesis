import Isotope.Elgot.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Basic

/-!
# The nondeterministic state-and-effect Elgot monad

`WS S M A` is the monad of computations that read and write a state `S`, emit an effect
drawn from a monoid `M`, and may behave nondeterministically: it is `StateT S (TraceT M Set)`
presented directly, with one `Exec` record per terminating execution.

The construction is deliberately generic in the effect monoid, so that both the pomset-valued
SPARC TSO instantiation (`Isotope.Elgot.TSO`) and any trace-valued variant can reuse it.

## Honest boundary

**Partial correctness only.**  `iter` collects the *finite* unfoldings `Runs`; a body that
always recurses denotes the empty set of executions.  This is the `𝒫` variant of the paper's
trace monads, not the `𝒫⁺` variant it uses for PO/TSO, and there is no `f^∞` divergence
branch.  Nonemptiness must **not** be added as a carrier field: a body that always recurses
has no finite run, so such a field would make `Iterate` unfillable.  This is a theorem-level
constraint, not a stylistic preference.

Paper erratum (`denotational-semantics-of-ssa.tex` L4823-4825): the paper writes
`TSO = StateT Buf (Trace Σ)`, but `Trace Σ = TraceT Σ Id` is deterministic and cannot carry
the set-valued denotations of L4845/L4853 or the hom-sets `Set_TSO(A,B)` of L4854.  It must
read `Traces Σ`.  `WS` is the (partial-correctness) set-valued monad the rest of the section
actually uses.
-/

universe u

namespace Isotope.Elgot

/-- One terminating execution: the returned value, the residual state, and the emitted
effect. -/
structure Exec (S M A : Type u) : Type u where
  /-- The returned value. -/
  value : A
  /-- The residual state. -/
  state : S
  /-- The emitted effect. -/
  effect : M

/-- Nondeterministic state-and-effect monad: `StateT S (TraceT M Set)` presented directly.
With `S = Buf` and `M = Pom 𝒜_TSO` this is the paper's `Set_TSO`. -/
structure WS (S M : Type u) (A : Type u) : Type u where
  /-- The set of terminating executions from a given initial state. -/
  runs : S → Set (Exec S M A)

namespace WS

variable {S M : Type u} [Monoid M] {A B C : Type u}

omit [Monoid M] in
@[ext] theorem ext {x y : WS S M A} (h : ∀ s, x.runs s = y.runs s) : x = y := by
  cases x; cases y; simp only [WS.mk.injEq]; funext s; exact h s

instance instMonad : Monad (WS S M) where
  pure a := ⟨fun s => {⟨a, s, 1⟩}⟩
  bind x f := ⟨fun s => {r | ∃ r₁ ∈ x.runs s, ∃ r₂ ∈ (f r₁.value).runs r₁.state,
    r = ⟨r₂.value, r₂.state, r₁.effect * r₂.effect⟩}⟩

theorem mem_bind_iff (x : WS S M A) (f : A → WS S M B) (s : S) (r : Exec S M B) :
    r ∈ (x >>= f).runs s ↔ ∃ r₁ ∈ x.runs s, ∃ r₂ ∈ (f r₁.value).runs r₁.state,
      r = ⟨r₂.value, r₂.state, r₁.effect * r₂.effect⟩ := Iff.rfl

theorem mem_pure_iff (a : A) (s : S) (r : Exec S M A) :
    r ∈ (pure a : WS S M A).runs s ↔ r = ⟨a, s, 1⟩ := Iff.rfl

instance instLawfulMonad : LawfulMonad (WS S M) := LawfulMonad.mk'
  (id_map := by
    intro A x
    ext s r
    simp only [Functor.map]
    constructor
    · rintro ⟨r₁, h₁, r₂, h₂, rfl⟩
      have h₂' : r₂ = ⟨r₁.value, r₁.state, (1 : M)⟩ := h₂
      subst h₂'
      simpa using h₁
    · intro h
      exact ⟨r, h, ⟨r.value, r.state, 1⟩, rfl, by cases r; simp⟩)
  (pure_bind := by
    intro A B a f
    ext s r
    simp only [mem_bind_iff]
    constructor
    · rintro ⟨r₁, h₁, r₂, h₂, rfl⟩
      have h₁' : r₁ = ⟨a, s, (1 : M)⟩ := h₁
      subst h₁'
      simpa using h₂
    · intro h
      exact ⟨⟨a, s, 1⟩, rfl, r, h, by cases r; simp⟩)
  (bind_assoc := by
    intro A B C x f g
    ext s r
    simp only [mem_bind_iff]
    constructor
    · rintro ⟨r₁, h₁, r₂, h₂, rfl⟩
      obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := h₁
      exact ⟨p₁, hp₁, ⟨r₂.value, r₂.state, p₂.effect * r₂.effect⟩,
        ⟨p₂, hp₂, r₂, h₂, rfl⟩, by simp [mul_assoc]⟩
    · rintro ⟨r₁, h₁, r₂, h₂, rfl⟩
      obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := h₂
      exact ⟨⟨p₁.value, p₁.state, r₁.effect * p₁.effect⟩, ⟨r₁, h₁, p₁, hp₁, rfl⟩,
        p₂, hp₂, by simp [mul_assoc]⟩)

/-- A finite successful unfolding of an iteration body: from state `s` and seed `a`, the loop
returns `b` in state `s'` emitting effect `w`.

Indexed by the *components* of an execution rather than by a computed `Exec` record:
with the record form, `cases` on a destructured run fails dependent elimination and the
codiagonal and naturality arguments become unworkable. -/
inductive Runs (f : A → WS S M (B ⊕ A)) : S → A → B → S → M → Prop
  | done {s a b s' w} :
      (⟨Sum.inl b, s', w⟩ : Exec S M (B ⊕ A)) ∈ (f a).runs s → Runs f s a b s' w
  | more {s a a' t w b s' w'} :
      (⟨Sum.inr a', t, w⟩ : Exec S M (B ⊕ A)) ∈ (f a).runs s →
      Runs f t a' b s' w' → Runs f s a b s' (w * w')

instance instIterate : Iterate (WS S M) where
  iter f a := ⟨fun s => {r | Runs f s a r.value r.state r.effect}⟩

theorem mem_iter_iff (f : A → WS S M (B ⊕ A)) (a : A) (s : S) (r : Exec S M B) :
    r ∈ (iter f a).runs s ↔ Runs f s a r.value r.state r.effect := Iff.rfl

theorem mem_kcomp_iff {a : A} (f : A → WS S M B) (g : B → WS S M C) (s : S) (r : Exec S M C) :
    r ∈ (kcomp f g a).runs s ↔ ∃ r₁ ∈ (f a).runs s, ∃ r₂ ∈ (g r₁.value).runs r₁.state,
      r = ⟨r₂.value, r₂.state, r₁.effect * r₂.effect⟩ := Iff.rfl

theorem fixpoint (f : A → WS S M (B ⊕ A)) :
    iter f = fun a ↦ f a >>= Sum.elim pure (iter f) := by
  funext a
  ext s r
  obtain ⟨b, s2, w⟩ := r
  rw [mem_iter_iff, mem_bind_iff]
  constructor
  · intro h
    cases h with
    | done hs => exact ⟨⟨Sum.inl b, s2, w⟩, hs, ⟨b, s2, 1⟩, rfl, by simp⟩
    | more hs hr =>
        rename_i a2 t w1 w2
        exact ⟨⟨Sum.inr a2, t, w1⟩, hs, ⟨b, s2, w2⟩, hr, rfl⟩
  · rintro ⟨r₁, h₁, r₂, h₂, heq⟩
    obtain ⟨v, t, u⟩ := r₁
    cases v with
    | inl b3 =>
        have h₂' : r₂ = ⟨b3, t, (1 : M)⟩ := h₂
        subst h₂'
        simp only [Exec.mk.injEq, mul_one] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        exact Runs.done h₁
    | inr a2 =>
        obtain ⟨v2, s4, w4⟩ := r₂
        simp only [Exec.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        exact Runs.more h₁ h₂

theorem mem_flattenBody_iff (f : A → WS S M ((B ⊕ A) ⊕ A)) (a : A) (s : S)
    (r : Exec S M (B ⊕ A)) :
    r ∈ (flattenBody f a).runs s ↔
      ∃ x t w, (⟨x, t, w⟩ : Exec S M ((B ⊕ A) ⊕ A)) ∈ (f a).runs s ∧
        r = ⟨flatten x, t, w⟩ := by
  rw [show flattenBody f = kcomp f (liftPure flatten) from rfl, mem_kcomp_iff]
  constructor
  · rintro ⟨r₁, h₁, r₂, h₂, rfl⟩
    have h₂' : r₂ = ⟨flatten r₁.value, r₁.state, (1 : M)⟩ := h₂
    subst h₂'
    exact ⟨r₁.value, r₁.state, r₁.effect, by cases r₁; exact h₁, by simp⟩
  · rintro ⟨x, t, w, hx, rfl⟩
    exact ⟨⟨x, t, w⟩, hx, ⟨flatten x, t, 1⟩, rfl, by simp⟩

theorem runs_flatten_cases (f : A → WS S M ((B ⊕ A) ⊕ A)) {s : S} {a : A}
    {x : B ⊕ A} {t : S} {w : M} (h : Runs f s a x t w) :
    (∀ b, x = Sum.inl b → Runs (flattenBody f) s a b t w) ∧
    (∀ a', x = Sum.inr a' → ∀ b s' w', Runs (flattenBody f) t a' b s' w' →
      Runs (flattenBody f) s a b s' (w * w')) := by
  induction h with
  | @done s a x t w hs =>
      refine ⟨?_, ?_⟩
      · rintro b rfl
        exact .done ((mem_flattenBody_iff _ _ _ _).2 ⟨Sum.inl (Sum.inl b), t, w, hs, rfl⟩)
      · rintro a' rfl b s' w' tail
        exact .more ((mem_flattenBody_iff _ _ _ _).2 ⟨Sum.inl (Sum.inr a'), t, w, hs, rfl⟩) tail
  | @more s a a' t w x s' w' hs _ ih =>
      refine ⟨?_, ?_⟩
      · rintro b rfl
        exact .more ((mem_flattenBody_iff _ _ _ _).2 ⟨Sum.inr a', t, w, hs, rfl⟩) (ih.1 b rfl)
      · rintro a'' rfl b s'' w'' tail
        rw [mul_assoc]
        exact .more ((mem_flattenBody_iff _ _ _ _).2 ⟨Sum.inr a', t, w, hs, rfl⟩)
          (ih.2 a'' rfl b s'' w'' tail)

theorem runs_flatten_of_nested (f : A → WS S M ((B ⊕ A) ⊕ A)) {s : S} {a : A}
    {b : B} {s' : S} {w : M} (h : Runs (iter f) s a b s' w) :
    Runs (flattenBody f) s a b s' w := by
  induction h with
  | done hs => exact (runs_flatten_cases f ((mem_iter_iff _ _ _ _).1 hs)).1 _ rfl
  | more hs _ ih => exact (runs_flatten_cases f ((mem_iter_iff _ _ _ _).1 hs)).2 _ rfl _ _ _ ih

theorem runs_nested_of_flatten (f : A → WS S M ((B ⊕ A) ⊕ A)) {s : S} {a : A}
    {b : B} {s' : S} {w : M} (h : Runs (flattenBody f) s a b s' w) :
    Runs (iter f) s a b s' w := by
  induction h with
  | @done s a b s' w hs =>
      rw [mem_flattenBody_iff] at hs
      obtain ⟨x, t, v, hx, heq⟩ := hs
      cases x with
      | inl y =>
          cases y with
          | inl b' =>
              cases heq
              exact .done ((mem_iter_iff _ _ _ _).2 (.done hx))
          | inr a' => cases heq
      | inr a' => cases heq
  | @more s a a' t v b s' w hs _ ih =>
      rw [mem_flattenBody_iff] at hs
      obtain ⟨x, t', v', hx, heq⟩ := hs
      cases x with
      | inl y =>
          cases y with
          | inl b' => cases heq
          | inr a'' =>
              cases heq
              exact .more ((mem_iter_iff _ _ _ _).2 (.done hx)) ih
      | inr a'' =>
          cases heq
          cases ih with
          | @done _ _ _ _ _ hi =>
              exact .done ((mem_iter_iff _ _ _ _).2 (.more hx ((mem_iter_iff _ _ _ _).1 hi)))
          | @more _ _ a₃ t₃ w₃ _ _ w₄ hi ht =>
              rw [← mul_assoc]
              exact .more ((mem_iter_iff _ _ _ _).2
                (.more hx ((mem_iter_iff _ _ _ _).1 hi))) ht

theorem codiagonal (f : A → WS S M ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f) := by
  funext a
  ext s r
  rw [mem_iter_iff, mem_iter_iff]
  exact ⟨runs_flatten_of_nested f, runs_nested_of_flatten f⟩

theorem mem_mapReturn_iff (f : A → WS S M (B ⊕ A)) (g : B → WS S M C) (a : A) (s : S)
    (r : Exec S M (C ⊕ A)) :
    r ∈ (mapReturn f g a).runs s ↔
      (∃ b t w c s' w', (⟨Sum.inl b, t, w⟩ : Exec S M (B ⊕ A)) ∈ (f a).runs s ∧
          (⟨c, s', w'⟩ : Exec S M C) ∈ (g b).runs t ∧ r = ⟨Sum.inl c, s', w * w'⟩) ∨
      (∃ a' t w, (⟨Sum.inr a', t, w⟩ : Exec S M (B ⊕ A)) ∈ (f a).runs s ∧
          r = ⟨Sum.inr a', t, w⟩) := by
  rw [show mapReturn f g = fun a ↦ f a >>= Sum.elim (fun b ↦ g b >>= pure ∘ Sum.inl)
      (pure ∘ Sum.inr) from rfl]
  rw [mem_bind_iff]
  constructor
  · rintro ⟨r₁, h₁, r₂, h₂, rfl⟩
    obtain ⟨v, t, w⟩ := r₁
    cases v with
    | inl b =>
        rw [show (Sum.elim (fun b ↦ g b >>= pure ∘ Sum.inl) (pure ∘ Sum.inr)
          (Exec.value ⟨Sum.inl b, t, w⟩)) = (g b >>= pure ∘ Sum.inl) from rfl,
          mem_bind_iff] at h₂
        obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := h₂
        have hp₂' : p₂ = ⟨Sum.inl p₁.value, p₁.state, (1 : M)⟩ := hp₂
        subst hp₂'
        exact Or.inl ⟨b, t, w, p₁.value, p₁.state, p₁.effect, h₁, by cases p₁; exact hp₁,
          by simp⟩
    | inr a' =>
        have h₂' : r₂ = ⟨Sum.inr a', t, (1 : M)⟩ := h₂
        subst h₂'
        exact Or.inr ⟨a', t, w, h₁, by simp⟩
  · rintro (⟨b, t, w, c, s', w', hb, hc, rfl⟩ | ⟨a', t, w, ha, rfl⟩)
    · exact ⟨⟨Sum.inl b, t, w⟩, hb, ⟨Sum.inl c, s', w'⟩,
        ⟨⟨c, s', w'⟩, hc, ⟨Sum.inl c, s', 1⟩, rfl, by simp⟩, rfl⟩
    · exact ⟨⟨Sum.inr a', t, w⟩, ha, ⟨Sum.inr a', t, 1⟩, rfl, by simp⟩

theorem runs_mapReturn_iff (f : A → WS S M (B ⊕ A)) (g : B → WS S M C) (a : A) (s : S)
    (c : C) (s' : S) (w : M) :
    Runs (mapReturn f g) s a c s' w ↔
      ∃ b t v v', Runs f s a b t v ∧ (⟨c, s', v'⟩ : Exec S M C) ∈ (g b).runs t ∧
        w = v * v' := by
  constructor
  · intro h
    induction h with
    | @done s a c s' w hd =>
        rw [mem_mapReturn_iff] at hd
        rcases hd with (⟨b, t, v, c2, s2, vv, hb, hc, heq⟩ | ⟨a2, t, v, _, heq⟩)
        · simp only [Exec.mk.injEq, Sum.inl.injEq] at heq
          obtain ⟨rfl, rfl, hw⟩ := heq
          exact ⟨b, t, v, vv, .done hb, hc, hw⟩
        · cases heq
    | @more s a a2 t v c s' w hm _ ih =>
        rw [mem_mapReturn_iff] at hm
        rcases hm with (⟨b, t2, w2, c2, s2, w3, _, _, heq⟩ | ⟨a3, t2, w2, hs, heq⟩)
        · cases heq
        · simp only [Exec.mk.injEq, Sum.inr.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          obtain ⟨b3, t3, u, u2, hb, hc, hw⟩ := ih
          exact ⟨b3, t3, v * u, u2, .more hs hb, hc, by rw [hw, mul_assoc]⟩
  · rintro ⟨b, t, v, v2, hr, hc, rfl⟩
    revert hc
    induction hr with
    | @done s a b t v hd =>
        intro hc
        exact .done ((mem_mapReturn_iff _ _ _ _ _).2
          (Or.inl ⟨b, t, v, c, s', v2, hd, hc, rfl⟩))
    | @more s a a2 t u b t2 u2 hs _ ih =>
        intro hc
        rw [mul_assoc]
        exact .more ((mem_mapReturn_iff _ _ _ _ _).2 (Or.inr ⟨a2, t, u, hs, rfl⟩)) (ih hc)

theorem naturality (f : A → WS S M (B ⊕ A)) (g : B → WS S M C) :
    kcomp (iter f) g = iter (mapReturn f g) := by
  funext a
  ext s r
  rw [mem_iter_iff, runs_mapReturn_iff, mem_kcomp_iff]
  constructor
  · rintro ⟨r₁, h₁, r₂, h₂, rfl⟩
    exact ⟨r₁.value, r₁.state, r₁.effect, r₂.effect, (mem_iter_iff _ _ _ _).1 h₁,
      by cases r₂; exact h₂, rfl⟩
  · rintro ⟨b, t, v, v2, hr, hc, hw⟩
    refine ⟨⟨b, t, v⟩, (mem_iter_iff _ _ _ _).2 hr, ⟨r.value, r.state, v2⟩, hc, ?_⟩
    cases r
    simp_all

theorem uniform_step (f : A → WS S M (B ⊕ A)) (g : C → WS S M (B ⊕ C)) (h : A → C)
    (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g)
    (a : A) (s : S) (t : Exec S M (B ⊕ C)) :
    t ∈ (g (h a)).runs s ↔ ∃ x, (⟨x, t.state, t.effect⟩ : Exec S M (B ⊕ A)) ∈ (f a).runs s ∧
      Sum.map id h x = t.value := by
  have square := congrFun comm a
  constructor
  · intro ht
    have hr : t ∈ (kcomp (liftPure h) g a).runs s :=
      ⟨⟨h a, s, 1⟩, rfl, t, ht, by cases t; simp⟩
    rw [← square] at hr
    obtain ⟨r₁, h₁, r₂, h₂, rfl⟩ := hr
    have h₂' : r₂ = ⟨Sum.map id h r₁.value, r₁.state, (1 : M)⟩ := h₂
    subst h₂'
    exact ⟨r₁.value, by cases r₁; simpa using h₁, rfl⟩
  · rintro ⟨x, hx, hv⟩
    obtain ⟨tv, ts, tw⟩ := t
    simp only at hv hx
    subst hv
    have hl : (⟨Sum.map id h x, ts, tw⟩ : Exec S M (B ⊕ C)) ∈
        (kcomp f (liftPure (Sum.map id h)) a).runs s :=
      ⟨⟨x, ts, tw⟩, hx, ⟨Sum.map id h x, ts, 1⟩, rfl, by simp⟩
    rw [square] at hl
    obtain ⟨r₁, h₁, r₂, h₂, heq⟩ := hl
    have h₁' : r₁ = ⟨h a, s, (1 : M)⟩ := h₁
    subst h₁'
    simp only [Exec.mk.injEq, one_mul] at heq
    obtain ⟨hv2, hs2, hw2⟩ := heq
    cases r₂
    simp_all

theorem runs_uniform_forward (f : A → WS S M (B ⊕ A)) (g : C → WS S M (B ⊕ C)) (h : A → C)
    (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g)
    {s : S} {a : A} {b : B} {s' : S} {w : M} (hr : Runs f s a b s' w) :
    Runs g s (h a) b s' w := by
  induction hr with
  | @done s a b s' w hs =>
      exact .done ((uniform_step f g h comm a s ⟨Sum.inl b, s', w⟩).2 ⟨Sum.inl b, hs, rfl⟩)
  | @more s a a2 t v b s' w hs _ ih =>
      exact .more ((uniform_step f g h comm a s ⟨Sum.inr (h a2), t, v⟩).2
        ⟨Sum.inr a2, hs, rfl⟩) ih

theorem runs_uniform_reverse (f : A → WS S M (B ⊕ A)) (g : C → WS S M (B ⊕ C)) (h : A → C)
    (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g)
    {s : S} {c : C} {b : B} {s' : S} {w : M} (hr : Runs g s c b s' w) :
    ∀ a, c = h a → Runs f s a b s' w := by
  induction hr with
  | @done s c b s' w ht =>
      rintro a rfl
      rw [uniform_step f g h comm a s ⟨Sum.inl b, s', w⟩] at ht
      obtain ⟨x, hx, heq⟩ := ht
      cases x with
      | inl b2 => cases heq; exact .done hx
      | inr a2 => cases heq
  | @more s c c2 t v b s' w ht _ ih =>
      rintro a rfl
      rw [uniform_step f g h comm a s ⟨Sum.inr c2, t, v⟩] at ht
      obtain ⟨x, hx, heq⟩ := ht
      cases x with
      | inl b2 => cases heq
      | inr a2 =>
          simp only [Sum.map_inr, Sum.inr.injEq] at heq
          exact .more hx (ih a2 heq.symm)

theorem uniformity (f : A → WS S M (B ⊕ A)) (g : C → WS S M (B ⊕ C)) (h : A → C)
    (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g) :
    iter f = kcomp (liftPure h) (iter g) := by
  funext a
  ext s r
  rw [mem_iter_iff, mem_kcomp_iff]
  constructor
  · intro hr
    exact ⟨⟨h a, s, 1⟩, rfl, r, (mem_iter_iff _ _ _ _).2
      (runs_uniform_forward f g h comm hr), by cases r; simp⟩
  · rintro ⟨r₁, h₁, r₂, h₂, rfl⟩
    have h₁' : r₁ = ⟨h a, s, (1 : M)⟩ := h₁
    subst h₁'
    simpa using runs_uniform_reverse f g h comm ((mem_iter_iff _ _ _ _).1 h₂) a rfl

/-- `WS S M` is a complete Elgot monad. -/
instance instLawfulElgotMonad : LawfulElgotMonad (WS S M) where
  fixpoint := fixpoint
  naturality := naturality
  codiagonal := codiagonal
  uniformity := uniformity

end WS

end Isotope.Elgot
