import Isotope.Elgot.Brookes.Monad

/-!
# Iteration in the Brookes monad

Iteration is the paper's union of approximants:

```
f₀     := λ _. ⊥
f_{i+1} := f ; [id, f_i]
f†      := ⋃_{i ∈ ℕ} f_i
```

Every approximant is built from `bind`, `pure` and `⊥`, hence is closed by
construction, and closed sets are stable under unions; so no bespoke closure
argument is needed anywhere.  Unlike the deterministic models, `iterate` here is
computable: it needs no choice principle.

This is **partial correctness**: an infinite execution contributes nothing, so a
body that always recurses has denotation `⊥`.  Divergence is the bottom of the
refinement order and is not observationally distinguished from "no execution".

`Runs` is an auxiliary inductive description of a single finite unfolding.  It is
*not* the definition of `iterate`, because the set of `Runs`-traces is in general
not closed (a rewrite may cross the seam between two unfoldings); `iterate`
membership is `Runs` **up to refinement**, which is the content of
`mem_iter_iff_runs`.
-/

namespace Isotope.Elgot

universe u

namespace Brookes

variable {E : Type u} {c : Rewriting E} {A B C : Type u}

/-- The paper's iterates: `f₀ := λ _. ⊥` and `f_{i+1} := f ; [id, f_i]`. -/
def approx (f : A → Brookes c (B ⊕ A)) : Nat → A → Brookes c B
  | 0, _ => ⊥
  | n + 1, a => f a >>= Sum.elim pure (approx f n)

@[simp] theorem approx_zero (f : A → Brookes c (B ⊕ A)) (a : A) : approx f 0 a = ⊥ := rfl

theorem approx_succ (f : A → Brookes c (B ⊕ A)) (n : Nat) (a : A) :
    approx f (n + 1) a = f a >>= Sum.elim pure (approx f n) := rfl

/-- `f† := ⋃_{i ∈ ℕ} f_i`.  Divergent executions contribute nothing. -/
def iterate (f : A → Brookes c (B ⊕ A)) (a : A) : Brookes c B :=
  iUnion fun n : Nat ↦ approx f n a

instance : Iterate (Brookes c) where
  iter := iterate

theorem iter_eq (f : A → Brookes c (B ⊕ A)) : iter f = iterate f := rfl

theorem mem_iter_iff (f : A → Brookes c (B ⊕ A)) (a : A) (t : Trace E) (b : B) :
    (t, b) ∈ iter f a ↔ ∃ n, (t, b) ∈ approx f n a := mem_iUnion_iff

theorem approx_le_iter (f : A → Brookes c (B ⊕ A)) (n : Nat) (a : A) :
    approx f n a ≤ iter f a := le_iUnion (fun m : Nat ↦ approx f m a) n

theorem iter_le (f : A → Brookes c (B ⊕ A)) (a : A) {y : Brookes c B}
    (h : ∀ n, approx f n a ≤ y) : iter f a ≤ y :=
  iUnion_le (x := fun m : Nat ↦ approx f m a) h

/-- One immediately returning unfolding. -/
theorem mem_iter_done {f : A → Brookes c (B ⊕ A)} {a : A} {b : B} {t : Trace E}
    (h : (t, Sum.inl b) ∈ f a) : (t, b) ∈ iter f a := by
  refine (mem_iter_iff f a t b).2 ⟨1, ?_⟩
  rw [approx_succ, mem_bind_iff]
  refine ⟨Sum.inl b, t, [], h, mem_pure b, ?_⟩
  rw [List.append_nil]

/-- One recursive unfolding, prepending its trace. -/
theorem mem_iter_more {f : A → Brookes c (B ⊕ A)} {a a' : A} {b : B} {t t' : Trace E}
    (h : (t, Sum.inr a') ∈ f a) (h' : (t', b) ∈ iter f a') : (t ++ t', b) ∈ iter f a := by
  obtain ⟨n, hn⟩ := (mem_iter_iff f a' t' b).1 h'
  refine (mem_iter_iff f a (t ++ t') b).2 ⟨n + 1, ?_⟩
  rw [approx_succ, mem_bind_iff]
  exact ⟨Sum.inr a', t, t', h, hn, .refl⟩

/-! ## Finite unfoldings -/

/-- A single finite successful unfolding of an iteration body, recording the
concatenated trace.  The set of such traces need not be closed; membership in
`iter` is `Runs` up to refinement. -/
inductive Runs (f : A → Brookes c (B ⊕ A)) : A → B → Trace E → Prop
  | done {a b t} : (t, Sum.inl b) ∈ f a → Runs f a b t
  | more {a a' b t t'} : (t, Sum.inr a') ∈ f a → Runs f a' b t' → Runs f a b (t ++ t')

theorem mem_iter_of_runs {f : A → Brookes c (B ⊕ A)} {a : A} {b : B} {t : Trace E}
    (h : Runs f a b t) : (t, b) ∈ iter f a := by
  induction h with
  | done h₀ => exact mem_iter_done h₀
  | more h₀ _ ih => exact mem_iter_more h₀ ih

theorem runs_of_mem_approx {f : A → Brookes c (B ⊕ A)} :
    ∀ (n : Nat) {a : A} {b : B} {t : Trace E}, (t, b) ∈ approx f n a →
      ∃ t₀, Runs f a b t₀ ∧ c.Refines t₀ t := by
  intro n
  induction n with
  | zero => intro a b t h; exact h.elim
  | succ n ih =>
    intro a b t h
    rw [approx_succ, mem_bind_iff] at h
    obtain ⟨s, u, v, hu, hv, hr⟩ := h
    cases s with
    | inl b' =>
      obtain ⟨rfl, hv0⟩ := (mem_pure_iff b' b v).1 hv
      refine ⟨u, .done hu, ?_⟩
      have h1 : c.Refines (u ++ []) (u ++ v) := Rewriting.refines_appendLeft u hv0
      rw [List.append_nil] at h1
      exact h1.trans hr
    | inr a' =>
      obtain ⟨t₀, hrun, hrt⟩ := ih hv
      refine ⟨u ++ t₀, .more hu hrun, ?_⟩
      exact (Rewriting.refines_appendLeft u hrt).trans hr

/-- Membership in `iter` is exactly "a finite unfolding, up to refinement". -/
theorem mem_iter_iff_runs (f : A → Brookes c (B ⊕ A)) (a : A) (t : Trace E) (b : B) :
    (t, b) ∈ iter f a ↔ ∃ t₀, Runs f a b t₀ ∧ c.Refines t₀ t := by
  constructor
  · rintro h
    obtain ⟨n, hn⟩ := (mem_iter_iff f a t b).1 h
    exact runs_of_mem_approx n hn
  · rintro ⟨t₀, hrun, hr⟩
    exact mem_of_refines (mem_iter_of_runs hrun) hr

/-! ## The Elgot laws -/

theorem fixpoint (f : A → Brookes c (B ⊕ A)) :
    iter f = fun a ↦ f a >>= Sum.elim pure (iter f) := by
  funext a
  apply ext_mem
  intro t b
  rw [mem_iter_iff, mem_bind_iff]
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact hn.elim
    | succ n =>
      rw [approx_succ, mem_bind_iff] at hn
      obtain ⟨s, u, v, hu, hv, hr⟩ := hn
      refine ⟨s, u, v, hu, ?_, hr⟩
      cases s with
      | inl b' => exact hv
      | inr a' => exact (mem_iter_iff f a' v b).2 ⟨n, hv⟩
  · rintro ⟨s, u, v, hu, hv, hr⟩
    cases s with
    | inl b' =>
      refine ⟨1, ?_⟩
      rw [approx_succ, mem_bind_iff]
      exact ⟨Sum.inl b', u, v, hu, hv, hr⟩
    | inr a' =>
      obtain ⟨n, hn⟩ := (mem_iter_iff f a' v b).1 hv
      refine ⟨n + 1, ?_⟩
      rw [approx_succ, mem_bind_iff]
      exact ⟨Sum.inr a', u, v, hu, hn, hr⟩

theorem approx_bind (f : A → Brookes c (B ⊕ A)) (g : B → Brookes c C) :
    ∀ (n : Nat) (a : A), approx f n a >>= g = approx (mapReturn f g) n a := by
  intro n
  induction n with
  | zero => intro a; exact bot_bind g
  | succ n ih =>
    intro a
    rw [approx_succ, approx_succ, bind_assoc]
    change f a >>= (fun s ↦ Sum.elim pure (approx f n) s >>= g) = _
    change _ = (f a >>= Sum.elim (fun b ↦ g b >>= pure ∘ Sum.inl) (pure ∘ Sum.inr)) >>=
      Sum.elim pure (approx (mapReturn f g) n)
    rw [bind_assoc]
    congr 1
    funext s
    cases s with
    | inl b => simp [Function.comp_def]
    | inr a' => simpa using ih a'

theorem naturality (f : A → Brookes c (B ⊕ A)) (g : B → Brookes c C) :
    kcomp (iter f) g = iter (mapReturn f g) := by
  funext a
  change iterate f a >>= g = iterate (mapReturn f g) a
  rw [iterate, iUnion_bind]
  exact congrArg iUnion (funext fun n ↦ approx_bind f g n a)

theorem approx_uniform (f : A → Brookes c (B ⊕ A)) (g : C → Brookes c (B ⊕ C)) (h : A → C)
    (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g) :
    ∀ (n : Nat) (a : A), approx f n a = approx g n (h a) := by
  have square : ∀ a : A, f a >>= (fun s ↦ pure (Sum.map id h s)) = g (h a) := by
    intro a
    have := congrFun comm a
    change f a >>= (fun s ↦ pure (Sum.map id h s)) = _
    rw [show (f a >>= fun s ↦ pure (Sum.map id h s)) = kcomp f (liftPure (Sum.map id h)) a from rfl,
      this]
    change (pure (h a) : Brookes c C) >>= g = g (h a)
    rw [pure_bind_eq]
  intro n
  induction n with
  | zero => intro a; rfl
  | succ n ih =>
    intro a
    rw [approx_succ, approx_succ, ← square a, bind_assoc]
    congr 1
    funext s
    cases s with
    | inl b => change (pure b : Brookes c B) = _ ; rw [pure_bind_eq]; rfl
    | inr a' => change approx f n a' = _ ; rw [pure_bind_eq]; exact ih a'

theorem uniformity (f : A → Brookes c (B ⊕ A)) (g : C → Brookes c (B ⊕ C)) (h : A → C)
    (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g) :
    iter f = kcomp (liftPure h) (iter g) := by
  funext a
  change iterate f a = (pure (h a) : Brookes c C) >>= iterate g
  rw [pure_bind_eq]
  exact congrArg iUnion (funext fun n ↦ approx_uniform f g h comm n a)

/-! ## Codiagonal -/

section Codiagonal

variable {f : A → Brookes c ((B ⊕ A) ⊕ A)}

theorem mem_flattenBody_iff (f : A → Brookes c ((B ⊕ A) ⊕ A)) (a : A) (t : Trace E)
    (s : B ⊕ A) : (t, s) ∈ flattenBody f a ↔ ∃ x, (t, x) ∈ f a ∧ flatten x = s := by
  change (t, s) ∈ (f a >>= liftPure flatten) ↔ _
  rw [mem_bind_iff]
  constructor
  · rintro ⟨x, u, v, hu, hv, hr⟩
    obtain ⟨rfl, hv0⟩ := (mem_pure_iff (flatten x) s v).1 hv
    refine ⟨x, ?_, rfl⟩
    have h1 : c.Refines (u ++ []) (u ++ v) := Rewriting.refines_appendLeft u hv0
    rw [List.append_nil] at h1
    exact mem_of_refines hu (h1.trans hr)
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, t, [], hx, mem_pure _, ?_⟩
    rw [List.append_nil]

theorem runs_flatten_cases {a : A} {y : B ⊕ A} {t : Trace E} (h : Runs f a y t) :
    (∀ b : B, y = Sum.inl b → (t, b) ∈ iter (flattenBody f) a) ∧
    (∀ (a' : A) (b : B) (t' : Trace E), y = Sum.inr a' →
      (t', b) ∈ iter (flattenBody f) a' → (t ++ t', b) ∈ iter (flattenBody f) a) := by
  induction h with
  | @done a y t h₀ =>
    constructor
    · rintro b rfl
      exact mem_iter_done ((mem_flattenBody_iff f a t (Sum.inl b)).2 ⟨Sum.inl (Sum.inl b), h₀, rfl⟩)
    · rintro a' b t' rfl hmem
      exact mem_iter_more
        ((mem_flattenBody_iff f a t (Sum.inr a')).2 ⟨Sum.inl (Sum.inr a'), h₀, rfl⟩) hmem
  | @more a a₁ y t₁ t₂ h₀ _ ih =>
    have hstep : (t₁, Sum.inr a₁) ∈ flattenBody f a :=
      (mem_flattenBody_iff f a t₁ (Sum.inr a₁)).2 ⟨Sum.inr a₁, h₀, rfl⟩
    constructor
    · rintro b rfl
      exact mem_iter_more hstep (ih.1 b rfl)
    · rintro a' b t' rfl hmem
      have := mem_iter_more hstep (ih.2 a' b t' rfl hmem)
      rwa [← List.append_assoc] at this

theorem mem_iterFlatten_of_mem_iter {a : A} {b : B} {t : Trace E}
    (h : (t, Sum.inl b) ∈ iter f a) : (t, b) ∈ iter (flattenBody f) a := by
  obtain ⟨t₀, hrun, hr⟩ := (mem_iter_iff_runs f a t (Sum.inl b)).1 h
  exact mem_of_refines ((runs_flatten_cases hrun).1 b rfl) hr

theorem mem_iterFlatten_more {a a' : A} {b : B} {t t' : Trace E}
    (h : (t, Sum.inr a') ∈ iter f a) (h' : (t', b) ∈ iter (flattenBody f) a') :
    (t ++ t', b) ∈ iter (flattenBody f) a := by
  obtain ⟨t₀, hrun, hr⟩ := (mem_iter_iff_runs f a t (Sum.inr a')).1 h
  exact mem_of_refines ((runs_flatten_cases hrun).2 a' b t' rfl h')
    (Rewriting.refines_appendRight hr t')

theorem runs_nested_flatten {a : A} {b : B} {t : Trace E} (h : Runs (iter f) a b t) :
    (t, b) ∈ iter (flattenBody f) a := by
  induction h with
  | done h₀ => exact mem_iterFlatten_of_mem_iter h₀
  | more h₀ _ ih => exact mem_iterFlatten_more h₀ ih

/-- An inner unfolding of `f` may be prepended to a run of `f†`. -/
theorem prepend_iter_runs {a a' : A} {b : B} {t t' : Trace E}
    (h : (t, Sum.inr a') ∈ f a) (hr : Runs (iter f) a' b t') : Runs (iter f) a b (t ++ t') := by
  cases hr with
  | done h₀ => exact .done (mem_iter_more h h₀)
  | @more _ a'' _ t₁ t₂ h₀ hr' =>
    have := Runs.more (mem_iter_more h h₀) hr'
    rwa [List.append_assoc] at this

theorem runs_flatten_nested {a : A} {b : B} {t : Trace E} (h : Runs (flattenBody f) a b t) :
    (t, b) ∈ iter (iter f) a := by
  induction h with
  | @done a b t h₀ =>
    obtain ⟨x, hx, hfl⟩ := (mem_flattenBody_iff f a t (Sum.inl b)).1 h₀
    match x, hfl with
    | Sum.inl (Sum.inl b'), hfl =>
      cases hfl
      exact mem_iter_done (mem_iter_done hx)
  | @more a a' b t t' h₀ _ ih =>
    obtain ⟨x, hx, hfl⟩ := (mem_flattenBody_iff f a t (Sum.inr a')).1 h₀
    match x, hfl with
    | Sum.inl (Sum.inr a''), hfl =>
      cases hfl
      exact mem_iter_more (mem_iter_done hx) ih
    | Sum.inr a'', hfl =>
      cases hfl
      obtain ⟨t₀, hrun, hr⟩ := (mem_iter_iff_runs (iter f) a' t' b).1 ih
      exact mem_of_refines (mem_iter_of_runs (prepend_iter_runs hx hrun))
        (Rewriting.refines_appendLeft t hr)

theorem codiagonal (f : A → Brookes c ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f) := by
  funext a
  apply ext_mem
  intro t b
  constructor
  · intro h
    obtain ⟨t₀, hrun, hr⟩ := (mem_iter_iff_runs (iter f) a t b).1 h
    exact mem_of_refines (runs_nested_flatten hrun) hr
  · intro h
    obtain ⟨t₀, hrun, hr⟩ := (mem_iter_iff_runs (flattenBody f) a t b).1 h
    exact mem_of_refines (runs_flatten_nested hrun) hr

end Codiagonal

instance : LawfulElgotMonad (Brookes c) where
  fixpoint := fixpoint
  naturality := naturality
  codiagonal := codiagonal
  uniformity := uniformity

end Brookes

end Isotope.Elgot
