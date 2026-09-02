import Isotope.Elgot.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Set.Lattice

/-!
# Traces and nondeterministic trace sets

A `Trace E T A` is a single observation of a computation: either termination
with a value and an accumulated finite effect drawn from `E`, or divergence
carrying an infinite observation drawn from `T`.  A `TraceSet E T A` is a set of
such observations, i.e. the nondeterministic trace model.

This file supplies only the monad structure: the effect action on traces, the
`Monad`/`LawfulMonad` instances, and the membership calculus (`mem_bind_iff`,
`mem_map_iff`, …) that every later proof is phrased in.  Iteration lives in
`Isotope.Elgot.TraceSet.Iteration`.

Typeclass assumptions are kept as weak as each statement allows: `Mul E` and
`SMul E T` for prepending effects, `One E` in addition for `pure`, and
`Monoid E` with `MulAction E T` for the monad laws.
-/

namespace Isotope.Elgot

universe u

/-- A single observation of a computation: termination with an accumulated
finite effect, or divergence with an infinite observation. -/
inductive Trace (E T : Type u) (A : Type u) : Type u
  /-- Terminate with `value`, having accumulated `effect`. -/
  | done (value : A) (effect : E)
  /-- Diverge, producing the infinite observation `observation`. -/
  | inf (observation : T)

namespace Trace

variable {E T A B C : Type u}

/-- Relabel the returned value of a trace. -/
def map (h : A → B) : Trace E T A → Trace E T B
  | done a e => done (h a) e
  | inf t => inf t

@[simp] theorem map_done (h : A → B) (a : A) (e : E) :
    map (T := T) h (done a e) = done (h a) e := rfl

@[simp] theorem map_inf (h : A → B) (t : T) :
    map (E := E) (A := A) h (inf t) = inf t := rfl

@[simp] theorem map_id (x : Trace E T A) : map id x = x := by cases x <;> rfl

theorem map_map (h : A → B) (k : B → C) (x : Trace E T A) :
    map k (map h x) = map (k ∘ h) x := by cases x <;> rfl

/-- Prepend an effect to a trace. -/
instance instSMul [Mul E] [SMul E T] : SMul E (Trace E T A) where
  smul e x := match x with
    | done a e' => done a (e * e')
    | inf t => inf (e • t)

@[simp] theorem smul_done [Mul E] [SMul E T] (e : E) (a : A) (e' : E) :
    e • (done a e' : Trace E T A) = done a (e * e') := rfl

@[simp] theorem smul_inf [Mul E] [SMul E T] (e : E) (t : T) :
    e • (inf t : Trace E T A) = inf (e • t) := rfl

theorem smul_map [Mul E] [SMul E T] (e : E) (h : A → B) (x : Trace E T A) :
    e • map h x = map h (e • x) := by cases x <;> rfl

theorem smul_eq_done_iff [Mul E] [SMul E T] {e : E} {x : Trace E T A} {a : A} {e' : E} :
    e • x = done a e' ↔ ∃ e₂, x = done a e₂ ∧ e' = e * e₂ := by
  cases x with
  | done a₂ e₂ =>
      constructor
      · intro h
        rw [smul_done] at h
        cases h
        exact ⟨e₂, rfl, rfl⟩
      · rintro ⟨e₃, h, rfl⟩
        cases h
        rfl
  | inf t => simp

theorem smul_eq_inf_iff [Mul E] [SMul E T] {e : E} {x : Trace E T A} {t : T} :
    e • x = inf t ↔ ∃ t₂, x = inf t₂ ∧ t = e • t₂ := by
  cases x with
  | done a₂ e₂ => simp
  | inf t₂ =>
      constructor
      · intro h
        rw [smul_inf] at h
        cases h
        exact ⟨t₂, rfl, rfl⟩
      · rintro ⟨t₃, h, rfl⟩
        cases h
        rfl

theorem map_eq_done_iff (h : A → B) {x : Trace E T A} {b : B} {e : E} :
    map (T := T) h x = done b e ↔ ∃ a, x = done a e ∧ b = h a := by
  cases x with
  | done a₂ e₂ =>
      constructor
      · intro hx
        rw [map_done] at hx
        cases hx
        exact ⟨a₂, rfl, rfl⟩
      · rintro ⟨a₃, hx, rfl⟩
        cases hx
        rfl
  | inf t => simp

theorem map_eq_inf_iff (h : A → B) {x : Trace E T A} {t : T} :
    map (T := T) h x = inf t ↔ x = inf t := by
  cases x with
  | done a e => simp
  | inf t₂ => simp

instance instMulAction [Monoid E] [MulAction E T] : MulAction E (Trace E T A) where
  one_smul x := by cases x <;> simp
  mul_smul e e' x := by cases x <;> simp [mul_assoc, mul_smul]

@[simp] theorem one_smul_trace [Monoid E] [MulAction E T] (x : Trace E T A) :
    (1 : E) • x = x := by cases x <;> simp

theorem smul_smul_trace [Monoid E] [MulAction E T] (e e' : E) (x : Trace E T A) :
    (e * e') • x = e • e' • x := by cases x <;> simp [mul_smul]

end Trace

/-- A nondeterministic set of traces. -/
structure TraceSet (E T : Type u) (A : Type u) : Type u where
  /-- The underlying set of observations. -/
  toSet : Set (Trace E T A)

namespace TraceSet

variable {E T A B C : Type u}

instance instMembership : Membership (Trace E T A) (TraceSet E T A) :=
  ⟨fun x u ↦ u ∈ x.toSet⟩

theorem mem_def {x : TraceSet E T A} {u : Trace E T A} : u ∈ x ↔ u ∈ x.toSet := Iff.rfl

@[simp] theorem mem_mk {s : Set (Trace E T A)} {u : Trace E T A} :
    u ∈ (⟨s⟩ : TraceSet E T A) ↔ u ∈ s := Iff.rfl

theorem ext {x y : TraceSet E T A} (h : ∀ u, u ∈ x ↔ u ∈ y) : x = y := by
  cases x
  cases y
  exact congrArg _ (Set.ext h)

theorem toSet_injective : Function.Injective (TraceSet.toSet (E := E) (T := T) (A := A)) := by
  rintro ⟨x⟩ ⟨y⟩ h
  exact congrArg _ h

instance instEmptyCollection : EmptyCollection (TraceSet E T A) := ⟨⟨∅⟩⟩

instance instUnion : Union (TraceSet E T A) := ⟨fun x y ↦ ⟨x.toSet ∪ y.toSet⟩⟩

instance instSingleton : Singleton (Trace E T A) (TraceSet E T A) := ⟨fun u ↦ ⟨{u}⟩⟩

instance instInsert : Insert (Trace E T A) (TraceSet E T A) :=
  ⟨fun u x ↦ ⟨insert u x.toSet⟩⟩

instance instHasSubset : HasSubset (TraceSet E T A) := ⟨fun x y ↦ ∀ u, u ∈ x → u ∈ y⟩

@[simp] theorem not_mem_empty (u : Trace E T A) : u ∉ (∅ : TraceSet E T A) := id

@[simp] theorem mem_union {x y : TraceSet E T A} {u : Trace E T A} :
    u ∈ x ∪ y ↔ u ∈ x ∨ u ∈ y := Iff.rfl

@[simp] theorem mem_singleton_iff {v u : Trace E T A} :
    u ∈ ({v} : TraceSet E T A) ↔ u = v := Iff.rfl

@[simp] theorem mem_insert_iff {v : Trace E T A} {x : TraceSet E T A} {u : Trace E T A} :
    u ∈ (insert v x : TraceSet E T A) ↔ u = v ∨ u ∈ x := Iff.rfl

theorem subset_def {x y : TraceSet E T A} : x ⊆ y ↔ ∀ u, u ∈ x → u ∈ y := Iff.rfl

/-- The union of an indexed family of trace sets. -/
def iUnion {ι : Type u} (x : ι → TraceSet E T A) : TraceSet E T A := ⟨⋃ i, (x i).toSet⟩

@[simp] theorem mem_iUnion {ι : Type u} {x : ι → TraceSet E T A} {u : Trace E T A} :
    u ∈ iUnion x ↔ ∃ i, u ∈ x i := Set.mem_iUnion

/-- Prepend an effect to every trace in a set. -/
instance instSMul [Mul E] [SMul E T] : SMul E (TraceSet E T A) :=
  ⟨fun e x ↦ ⟨(e • ·) '' x.toSet⟩⟩

@[simp] theorem mem_smul [Mul E] [SMul E T] {e : E} {x : TraceSet E T A} {u : Trace E T A} :
    u ∈ e • x ↔ ∃ v, v ∈ x ∧ u = e • v := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩

@[simp] theorem smul_singleton [Mul E] [SMul E T] (e : E) (u : Trace E T A) :
    e • ({u} : TraceSet E T A) = {e • u} := by
  apply ext
  intro v
  rw [mem_smul]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact congrArg _ hw
  · rintro rfl
    exact ⟨u, rfl, rfl⟩

/-- Sequence a single trace with a continuation: a terminating trace shifts the
continuation by its accumulated effect, a divergent trace absorbs it. -/
def bindTrace [Mul E] [SMul E T] (x : Trace E T A) (f : A → TraceSet E T B) : TraceSet E T B :=
  match x with
  | Trace.done a e => e • f a
  | Trace.inf t => {Trace.inf t}

@[simp] theorem bindTrace_done [Mul E] [SMul E T] (a : A) (e : E) (f : A → TraceSet E T B) :
    bindTrace (Trace.done a e) f = e • f a := rfl

@[simp] theorem bindTrace_inf [Mul E] [SMul E T] (t : T) (f : A → TraceSet E T B) :
    bindTrace (E := E) (Trace.inf t) f = {Trace.inf t} := rfl

instance instMonad [One E] [Mul E] [SMul E T] : Monad (TraceSet E T) where
  pure a := ⟨{Trace.done a 1}⟩
  bind x f := ⟨{u | (∃ a e v, Trace.done a e ∈ x ∧ v ∈ f a ∧ u = e • v) ∨
    (∃ t, Trace.inf t ∈ x ∧ u = Trace.inf t)}⟩

section

variable [One E] [Mul E] [SMul E T]

@[simp] theorem mem_pure_iff (a : A) (u : Trace E T A) :
    u ∈ (pure a : TraceSet E T A) ↔ u = Trace.done a 1 := Iff.rfl

theorem mem_bind_iff (x : TraceSet E T A) (f : A → TraceSet E T B) (u : Trace E T B) :
    u ∈ (x >>= f) ↔
      (∃ a e v, Trace.done a e ∈ x ∧ v ∈ f a ∧ u = e • v) ∨
      (∃ t, Trace.inf t ∈ x ∧ u = Trace.inf t) := Iff.rfl

theorem mem_kcomp_iff (f : A → TraceSet E T B) (g : B → TraceSet E T C) (a : A)
    (u : Trace E T C) :
    u ∈ kcomp f g a ↔
      (∃ b e v, Trace.done b e ∈ f a ∧ v ∈ g b ∧ u = e • v) ∨
      (∃ t, Trace.inf t ∈ f a ∧ u = Trace.inf t) :=
  mem_bind_iff (f a) g u

theorem map_eq_bind (h : A → B) (x : TraceSet E T A) :
    h <$> x = x >>= (fun a ↦ pure (h a)) := rfl

/-- Bind, decomposed through `bindTrace`. -/
theorem mem_bind_iff' (x : TraceSet E T A) (f : A → TraceSet E T B) (u : Trace E T B) :
    u ∈ (x >>= f) ↔ ∃ v, v ∈ x ∧ u ∈ bindTrace v f := by
  rw [mem_bind_iff]
  constructor
  · rintro (⟨a, e, v, ha, hv, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨Trace.done a e, ha, mem_smul.2 ⟨v, hv, rfl⟩⟩
    · exact ⟨Trace.inf t, ht, rfl⟩
  · rintro ⟨v, hv, hu⟩
    cases v with
    | done a e =>
        rcases mem_smul.1 hu with ⟨w, hw, rfl⟩
        exact Or.inl ⟨a, e, w, hv, hw, rfl⟩
    | inf t => exact Or.inr ⟨t, hv, hu⟩

/-- Kleisli composition, decomposed through `bindTrace`. -/
theorem mem_kcomp_iff' (f : A → TraceSet E T B) (g : B → TraceSet E T C) (a : A)
    (u : Trace E T C) : u ∈ kcomp f g a ↔ ∃ v, v ∈ f a ∧ u ∈ bindTrace v g :=
  mem_bind_iff' (f a) g u

/-- Membership of a `done` trace in a bind, with the effect split. -/
theorem mem_bind_done_iff {x : TraceSet E T A} {f : A → TraceSet E T B} {b : B} {e : E} :
    Trace.done b e ∈ (x >>= f) ↔
      ∃ a e₁ e₂, Trace.done a e₁ ∈ x ∧ Trace.done b e₂ ∈ f a ∧ e = e₁ * e₂ := by
  rw [mem_bind_iff]
  constructor
  · rintro (⟨a, e₁, v, ha, hv, hu⟩ | ⟨t, _, hu⟩)
    · rcases Trace.smul_eq_done_iff.mp hu.symm with ⟨e₂, rfl, rfl⟩
      exact ⟨a, e₁, e₂, ha, hv, rfl⟩
    · exact absurd hu (by simp)
  · rintro ⟨a, e₁, e₂, ha, hb, rfl⟩
    exact Or.inl ⟨a, e₁, Trace.done b e₂, ha, hb, rfl⟩

/-- Membership of an `inf` trace in a bind: either the continuation diverges after a
terminating prefix, or the prefix itself already diverged. -/
theorem mem_bind_inf_iff {x : TraceSet E T A} {f : A → TraceSet E T B} {t : T} :
    Trace.inf t ∈ (x >>= f) ↔
      (∃ a e₁ t₂, Trace.done a e₁ ∈ x ∧ Trace.inf t₂ ∈ f a ∧ t = e₁ • t₂) ∨
      Trace.inf t ∈ x := by
  rw [mem_bind_iff]
  constructor
  · rintro (⟨a, e₁, v, ha, hv, hu⟩ | ⟨t', ht, hu⟩)
    · rcases Trace.smul_eq_inf_iff.mp hu.symm with ⟨t₂, rfl, rfl⟩
      exact Or.inl ⟨a, e₁, t₂, ha, hv, rfl⟩
    · cases hu
      exact Or.inr ht
  · rintro (⟨a, e₁, t₂, ha, ht, rfl⟩ | ht)
    · exact Or.inl ⟨a, e₁, Trace.inf t₂, ha, ht, rfl⟩
    · exact Or.inr ⟨t, ht, rfl⟩

omit [One E] in
/-- Membership of a `done` trace in a shifted trace set. -/
theorem mem_smul_done_iff {e : E} {x : TraceSet E T A} {a : A} {e' : E} :
    Trace.done a e' ∈ e • x ↔ ∃ e₂, Trace.done a e₂ ∈ x ∧ e' = e * e₂ := by
  rw [mem_smul]
  constructor
  · rintro ⟨v, hv, hu⟩
    rcases Trace.smul_eq_done_iff.mp hu.symm with ⟨e₂, rfl, rfl⟩
    exact ⟨e₂, hv, rfl⟩
  · rintro ⟨e₂, hv, rfl⟩
    exact ⟨Trace.done a e₂, hv, rfl⟩

omit [One E] in
/-- Membership of an `inf` trace in a shifted trace set. -/
theorem mem_smul_inf_iff {e : E} {x : TraceSet E T A} {t : T} :
    Trace.inf t ∈ e • x ↔ ∃ t₂, Trace.inf t₂ ∈ x ∧ t = e • t₂ := by
  rw [mem_smul]
  constructor
  · rintro ⟨v, hv, hu⟩
    rcases Trace.smul_eq_inf_iff.mp hu.symm with ⟨t₂, rfl, rfl⟩
    exact ⟨t₂, hv, rfl⟩
  · rintro ⟨t₂, hv, rfl⟩
    exact ⟨Trace.inf t₂, hv, rfl⟩

end

section

variable [Monoid E] [MulAction E T]

/-- The functorial action on trace sets is the image under `Trace.map`.
Only `mul_one` is used. -/
theorem mem_map_iff (h : A → B) (x : TraceSet E T A) (u : Trace E T B) :
    u ∈ (h <$> x) ↔ ∃ v, v ∈ x ∧ u = Trace.map h v := by
  rw [map_eq_bind, mem_bind_iff]
  constructor
  · rintro (⟨a, e, v, ha, hv, rfl⟩ | ⟨t, ht, rfl⟩)
    · rw [mem_pure_iff] at hv
      subst hv
      exact ⟨Trace.done a e, ha, by simp⟩
    · exact ⟨Trace.inf t, ht, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    cases v with
    | done a e => exact Or.inl ⟨a, e, Trace.done (h a) 1, hv, rfl, by simp⟩
    | inf t => exact Or.inr ⟨t, hv, rfl⟩

instance instLawfulMonad : LawfulMonad (TraceSet E T) := LawfulMonad.mk'
  (id_map := by
    intro A x
    apply ext
    intro u
    rw [map_eq_bind, mem_bind_iff]
    constructor
    · rintro (⟨a, e, v, ha, hv, rfl⟩ | ⟨t, ht, rfl⟩)
      · rw [mem_pure_iff] at hv
        subst hv
        simpa using ha
      · exact ht
    · intro hu
      cases u with
      | done a e => exact Or.inl ⟨a, e, Trace.done a 1, hu, rfl, by simp⟩
      | inf t => exact Or.inr ⟨t, hu, rfl⟩)
  (pure_bind := by
    intro A B a f
    apply ext
    intro u
    rw [mem_bind_iff]
    constructor
    · rintro (⟨a', e, v, ha, hv, rfl⟩ | ⟨t, ht, rfl⟩)
      · rw [mem_pure_iff] at ha
        cases ha
        simpa using hv
      · rw [mem_pure_iff] at ht
        exact absurd ht (by simp)
    · intro hu
      exact Or.inl ⟨a, 1, u, rfl, hu, by simp⟩)
  (bind_assoc := by
    intro A B C x f g
    apply ext
    intro u
    cases u with
    | done c e =>
        constructor
        · intro h
          rcases mem_bind_done_iff.mp h with ⟨b, e₁, e₂, hb, hc, rfl⟩
          rcases mem_bind_done_iff.mp hb with ⟨a, e₃, e₄, ha, hb', rfl⟩
          exact mem_bind_done_iff.mpr ⟨a, e₃, e₄ * e₂, ha,
            mem_bind_done_iff.mpr ⟨b, e₄, e₂, hb', hc, rfl⟩, mul_assoc _ _ _⟩
        · intro h
          rcases mem_bind_done_iff.mp h with ⟨a, e₁, e₂, ha, hc, rfl⟩
          rcases mem_bind_done_iff.mp hc with ⟨b, e₃, e₄, hb, hc', rfl⟩
          exact mem_bind_done_iff.mpr ⟨b, e₁ * e₃, e₄,
            mem_bind_done_iff.mpr ⟨a, e₁, e₃, ha, hb, rfl⟩, hc', (mul_assoc _ _ _).symm⟩
    | inf t =>
        constructor
        · intro h
          rcases mem_bind_inf_iff.mp h with (⟨b, e₁, t₂, hb, ht, rfl⟩ | ht)
          · rcases mem_bind_done_iff.mp hb with ⟨a, e₃, e₄, ha, hb', rfl⟩
            exact mem_bind_inf_iff.mpr (Or.inl ⟨a, e₃, e₄ • t₂, ha,
              mem_bind_inf_iff.mpr (Or.inl ⟨b, e₄, t₂, hb', ht, rfl⟩), mul_smul _ _ _⟩)
          · rcases mem_bind_inf_iff.mp ht with (⟨a, e₁, t₂, ha, ht', rfl⟩ | ht')
            · exact mem_bind_inf_iff.mpr (Or.inl ⟨a, e₁, t₂, ha,
                mem_bind_inf_iff.mpr (Or.inr ht'), rfl⟩)
            · exact mem_bind_inf_iff.mpr (Or.inr ht')
        · intro h
          rcases mem_bind_inf_iff.mp h with (⟨a, e₁, t₂, ha, ht, rfl⟩ | ht)
          · rcases mem_bind_inf_iff.mp ht with (⟨b, e₃, t₄, hb, ht', rfl⟩ | ht')
            · exact mem_bind_inf_iff.mpr (Or.inl ⟨b, e₁ * e₃, t₄,
                mem_bind_done_iff.mpr ⟨a, e₁, e₃, ha, hb, rfl⟩, ht', (mul_smul _ _ _).symm⟩)
            · exact mem_bind_inf_iff.mpr (Or.inr
                (mem_bind_inf_iff.mpr (Or.inl ⟨a, e₁, t₂, ha, ht', rfl⟩)))
          · exact mem_bind_inf_iff.mpr (Or.inr (mem_bind_inf_iff.mpr (Or.inr ht))))
  (bind_pure_comp := by intro A B f x; rfl)

instance instMulAction : MulAction E (TraceSet E T A) where
  one_smul x := by
    apply ext
    intro u
    cases u with
    | done a e =>
        rw [mem_smul_done_iff]
        constructor
        · rintro ⟨e₂, h, rfl⟩
          rwa [one_mul]
        · intro h
          exact ⟨e, h, (one_mul e).symm⟩
    | inf t =>
        rw [mem_smul_inf_iff]
        constructor
        · rintro ⟨t₂, h, rfl⟩
          rwa [one_smul E t₂]
        · intro h
          exact ⟨t, h, (one_smul E t).symm⟩
  mul_smul e e' x := by
    apply ext
    intro u
    cases u with
    | done a e₀ =>
        simp only [mem_smul_done_iff]
        constructor
        · rintro ⟨e₂, h, rfl⟩
          exact ⟨e' * e₂, ⟨e₂, h, rfl⟩, mul_assoc _ _ _⟩
        · rintro ⟨e₂, ⟨e₃, h, rfl⟩, rfl⟩
          exact ⟨e₃, h, (mul_assoc _ _ _).symm⟩
    | inf t =>
        simp only [mem_smul_inf_iff]
        constructor
        · rintro ⟨t₂, h, rfl⟩
          exact ⟨e' • t₂, ⟨t₂, h, rfl⟩, mul_smul e e' t₂⟩
        · rintro ⟨t₂, ⟨t₃, h, rfl⟩, rfl⟩
          exact ⟨t₃, h, (mul_smul e e' t₃).symm⟩

theorem smul_bindTrace (e : E) (x : Trace E T A) (f : A → TraceSet E T B) :
    bindTrace (e • x) f = e • bindTrace x f := by
  cases x with
  | done a e' => simp [mul_smul]
  | inf t => simp

theorem smul_bind (e : E) (x : TraceSet E T A) (f : A → TraceSet E T B) :
    e • (x >>= f) = (e • x) >>= f := by
  apply ext
  intro u
  cases u with
  | done b e' =>
      rw [mem_smul_done_iff, mem_bind_done_iff]
      constructor
      · rintro ⟨e₂, hb, rfl⟩
        rw [mem_bind_done_iff] at hb
        rcases hb with ⟨a, e₁, e₃, ha, hf, rfl⟩
        exact ⟨a, e * e₁, e₃, mem_smul_done_iff.2 ⟨e₁, ha, rfl⟩, hf, (mul_assoc _ _ _).symm⟩
      · rintro ⟨a, e₁, e₃, ha, hf, rfl⟩
        rcases mem_smul_done_iff.1 ha with ⟨e₄, ha', rfl⟩
        exact ⟨e₄ * e₃, mem_bind_done_iff.2 ⟨a, e₄, e₃, ha', hf, rfl⟩, mul_assoc _ _ _⟩
  | inf t =>
      rw [mem_smul_inf_iff, mem_bind_inf_iff]
      constructor
      · rintro ⟨t₂, hb, rfl⟩
        rw [mem_bind_inf_iff] at hb
        rcases hb with (⟨a, e₁, t₃, ha, hf, rfl⟩ | ht)
        · exact Or.inl ⟨a, e * e₁, t₃, mem_smul_done_iff.2 ⟨e₁, ha, rfl⟩, hf,
            (mul_smul _ _ _).symm⟩
        · exact Or.inr (mem_smul_inf_iff.2 ⟨t₂, ht, rfl⟩)
      · rintro (⟨a, e₁, t₂, ha, hf, rfl⟩ | ht)
        · rcases mem_smul_done_iff.1 ha with ⟨e₄, ha', rfl⟩
          exact ⟨e₄ • t₂, mem_bind_inf_iff.2 (Or.inl ⟨a, e₄, t₂, ha', hf, rfl⟩),
            mul_smul _ _ _⟩
        · rcases mem_smul_inf_iff.1 ht with ⟨t₂, ht', rfl⟩
          exact ⟨t₂, mem_bind_inf_iff.2 (Or.inr ht'), rfl⟩

end

end TraceSet

end Isotope.Elgot
