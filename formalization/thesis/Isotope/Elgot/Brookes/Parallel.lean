import Isotope.Elgot.Brookes.Monad
import Isotope.Elgot.Interleave

/-!
# Parallel composition in a Brookes model

Brookes traces are designed so that parallel composition is *trace shuffling*: a
step of the other thread appearing between two of my steps is exactly the
environment interference my rely-guarantee pairs already allow for.  This is the
paper's

```
T₁ ∥ T₂ = (⋃ {α ∥ β | α ∈ T₁, β ∈ T₂})†
```

(Brookes, *Full Abstraction for a Shared-Variable Parallel Language*,
Inform. and Comput. 127(2):145–163, 1996, journal p. 150 — **transcribed**),
carrying in addition the value component that the monadic presentation needs:
`par x y` returns the pair of the two results.  The shuffle relation itself is
`Isotope.Elgot.Interleave`.

`par`, `mem_par` and `mem_par_iff` were previously defined in
`Isotope/Elgot/Brookes/TSO/Interleaving.lean`, already generic in the rewriting
system; they are hoisted here unchanged so that the sequentially consistent
development can use them without depending on the TSO one, and that file now
imports this one.

## What is proved here

* `par_mono`, `bot_par`, `par_bot`, `par_iUnion`, `iUnion_par` — monotonicity,
  strictness and continuity for arbitrary unions.  Generic in `c`.
* `par_comm` — Brookes's `C₁ ∥ C₂ ≡ C₂ ∥ C₁` (Proposition 8.1), up to the
  symmetry isomorphism of the product of return types.  Generic in `c`.
* `par_assoc` — Brookes's `(C₁ ∥ C₂) ∥ C₃ ≡ C₁ ∥ (C₂ ∥ C₃)` (Proposition 8.1),
  up to the associativity isomorphism.  This one is **not** generic: closing the
  inner parallel composition has to be deferrable through the outer shuffle, a
  property of the rewriting system recorded as `DefersPar`.  Brookes asserts
  associativity in one line ("interleaving operations on transition traces are
  clearly associative", journal p. 152) without isolating this side condition;
  `DefersPar` is our reconstruction of what the argument uses, and
  `SeqCst.defersPar` discharges it for stuttering and mumbling.
* `bind_par_le_par_bind` — Brookes's `C₁; (C₂ ∥ C₃) ⊑ (C₁; C₂) ∥ C₃`
  (journal p. 152), and `seq_le_par` — the `C₁; C₂ ⊑ C₁ ∥ C₂` he derives from
  it.  Both generic in `c`.

The unit law `C ∥ skip ≡ C` is **not** here: it needs the stuttering rule
specifically, so it is proved for the sequentially consistent model in
`Isotope/Elgot/Brookes/SeqCst/Parallel.lean`.
-/

namespace Isotope.Elgot

universe u v

namespace Brookes

variable {E : Type u} {c : Rewriting E} {A B C : Type u}

/-! ## Two shuffle lemmas

Neither is in `Isotope/Elgot/Interleave.lean`; they are stated here, in the
`Brookes` namespace, to keep that shared file untouched. -/

/-- A shuffle whose left operand is a cons splits at the leading element: every
element of the merge before it comes from the right operand. -/
theorem interleave_consSplit : ∀ {x v w : List E}, Interleave x v w →
    ∀ {e : E} {t : List E}, x = e :: t →
      ∃ v₁ v₂ q, v = v₁ ++ v₂ ∧ w = v₁ ++ e :: q ∧ Interleave t v₂ q := by
  intro x v w h
  induction h with
  | nil => intro e t hx; exact absurd hx (by simp)
  | @left f t' u' w' h _ => intro e t hx; cases hx; exact ⟨[], u', w', rfl, rfl, h⟩
  | @right f t' u' w' _ ih =>
      intro e t hx
      obtain ⟨v₁, v₂, q, hv, hw, hi⟩ := ih hx
      exact ⟨f :: v₁, v₂, q, by rw [hv]; rfl, by rw [hw]; rfl, hi⟩

/-- Shuffling is associative: a merge of `t ∥ u` with `v` is a merge of `t` with
some merge of `u ∥ v`. -/
theorem interleave_assoc {t u tu v w : List E} (h₁ : Interleave t u tu)
    (h₂ : Interleave tu v w) : ∃ uv, Interleave u v uv ∧ Interleave t uv w := by
  induction h₂ generalizing t u with
  | nil => cases h₁; exact ⟨[], .nil, .nil⟩
  | @left e tu' v' w' _ ih =>
      cases h₁ with
      | @left _ t' _ _ h₁ =>
          obtain ⟨uv, hu, ht⟩ := ih h₁
          exact ⟨uv, hu, ht.left⟩
      | @right _ _ u' _ h₁ =>
          obtain ⟨uv, hu, ht⟩ := ih h₁
          exact ⟨e :: uv, hu.left, ht.right⟩
  | @right e tu' v' w' _ ih =>
      obtain ⟨uv, hu, ht⟩ := ih h₁
      exact ⟨e :: uv, hu.right, ht.right⟩

/-! ## A membership lemma for the functor action -/

/-- Mapping a closed computation changes only the returned value: `f <$> x` is
`x >>= pure ∘ f`, whose traces are those of `x` extended by an empty-trace
refinement, and `x` already absorbs those. -/
theorem mem_map_iff {f : A → B} {x : Brookes c A} {t : Trace E} {b : B} :
    (t, b) ∈ (f <$> x) ↔ ∃ a, b = f a ∧ (t, a) ∈ x := by
  rw [← bind_pure_comp, mem_bind_iff]
  constructor
  · rintro ⟨a, u, v, hu, hv, hr⟩
    obtain ⟨rfl, hv0⟩ := (mem_pure_iff (f a) b v).1 hv
    refine ⟨a, rfl, mem_of_refines hu (Relation.ReflTransGen.trans ?_ hr)⟩
    have := Rewriting.refines_appendLeft (c := c) u hv0
    rwa [List.append_nil] at this
  · rintro ⟨a, rfl, ha⟩
    refine ⟨a, t, [], ha, mem_pure (f a), ?_⟩
    rw [List.append_nil]

/-! ## Parallel composition -/

/-- Parallel composition: run both computations, shuffling their traces, and
return both results.  The closure is genuine: mumbling can merge a step of one
thread with a step of the other, and the result is no longer a shuffle. -/
def par (x : Brookes c A) (y : Brookes c B) : Brookes c (A × B) :=
  close c {p | ∃ t u, (t, p.2.1) ∈ x ∧ (u, p.2.2) ∈ y ∧ Interleave t u p.1}

theorem mem_par {x : Brookes c A} {y : Brookes c B} {t u w : Trace E} {a : A} {b : B}
    (ha : (t, a) ∈ x) (hb : (u, b) ∈ y) (h : Interleave t u w) : (w, (a, b)) ∈ par x y :=
  ⟨w, ⟨t, u, ha, hb, h⟩, .refl⟩

theorem mem_par_iff {x : Brookes c A} {y : Brookes c B} {w : Trace E} {a : A} {b : B} :
    (w, (a, b)) ∈ par x y ↔
      ∃ w₀ t u, (t, a) ∈ x ∧ (u, b) ∈ y ∧ Interleave t u w₀ ∧ c.Refines w₀ w := by
  constructor
  · rintro ⟨w₀, ⟨t, u, ha, hb, hi⟩, hr⟩
    exact ⟨w₀, t, u, ha, hb, hi, hr⟩
  · rintro ⟨w₀, t, u, ha, hb, hi, hr⟩
    exact ⟨w₀, ⟨t, u, ha, hb, hi⟩, hr⟩

/-! ## Structural laws -/

/-- Parallel composition is monotone in both arguments. -/
theorem par_mono {x x' : Brookes c A} {y y' : Brookes c B} (hx : x ≤ x') (hy : y ≤ y') :
    par x y ≤ par x' y' := by
  apply le_of_mem
  rintro w ⟨a, b⟩ hm
  rw [mem_par_iff] at hm ⊢
  obtain ⟨w₀, t, u, ha, hb, hi, hr⟩ := hm
  exact ⟨w₀, t, u, hx ha, hy hb, hi, hr⟩

/-- A thread that cannot run blocks the whole system. -/
@[simp] theorem bot_par (y : Brookes c B) : par (⊥ : Brookes c A) y = ⊥ := by
  refine eq_bot_iff_forall.2 fun w p hm ↦ ?_
  obtain ⟨a, b⟩ := p
  obtain ⟨_, _, _, ha, _, _, _⟩ := mem_par_iff.1 hm
  exact ha

@[simp] theorem par_bot (x : Brookes c A) : par x (⊥ : Brookes c B) = ⊥ := by
  refine eq_bot_iff_forall.2 fun w p hm ↦ ?_
  obtain ⟨a, b⟩ := p
  obtain ⟨_, _, _, _, hb, _, _⟩ := mem_par_iff.1 hm
  exact hb

/-- Parallel composition is continuous in its left argument. -/
theorem iUnion_par {ι : Sort v} (x : ι → Brookes c A) (y : Brookes c B) :
    par (iUnion x) y = iUnion fun i ↦ par (x i) y := by
  apply ext_mem
  rintro w ⟨a, b⟩
  rw [mem_par_iff, mem_iUnion_iff]
  constructor
  · rintro ⟨w₀, t, u, ha, hb, hi, hr⟩
    obtain ⟨i, hi'⟩ := mem_iUnion_iff.1 ha
    exact ⟨i, mem_par_iff.2 ⟨w₀, t, u, hi', hb, hi, hr⟩⟩
  · rintro ⟨i, hm⟩
    obtain ⟨w₀, t, u, ha, hb, hi, hr⟩ := mem_par_iff.1 hm
    exact ⟨w₀, t, u, mem_iUnion_iff.2 ⟨i, ha⟩, hb, hi, hr⟩

/-- Parallel composition is continuous in its right argument. -/
theorem par_iUnion {ι : Sort v} (x : Brookes c A) (y : ι → Brookes c B) :
    par x (iUnion y) = iUnion fun i ↦ par x (y i) := by
  apply ext_mem
  rintro w ⟨a, b⟩
  rw [mem_par_iff, mem_iUnion_iff]
  constructor
  · rintro ⟨w₀, t, u, ha, hb, hi, hr⟩
    obtain ⟨i, hi'⟩ := mem_iUnion_iff.1 hb
    exact ⟨i, mem_par_iff.2 ⟨w₀, t, u, ha, hi', hi, hr⟩⟩
  · rintro ⟨i, hm⟩
    obtain ⟨w₀, t, u, ha, hb, hi, hr⟩ := mem_par_iff.1 hm
    exact ⟨w₀, t, u, ha, mem_iUnion_iff.2 ⟨i, hb⟩, hi, hr⟩

/-- **Commutativity** (Brookes, Proposition 8.1: `C₁ ∥ C₂ ≡ C₂ ∥ C₁`), stated up
to the symmetry isomorphism of the product of return types. -/
theorem par_comm (x : Brookes c A) (y : Brookes c B) :
    par y x = Prod.swap <$> par x y := by
  apply ext_mem
  rintro w ⟨b, a⟩
  rw [mem_par_iff, mem_map_iff]
  constructor
  · rintro ⟨w₀, u, t, hb, ha, hi, hr⟩
    exact ⟨(a, b), rfl, mem_par_iff.2 ⟨w₀, t, u, ha, hb, hi.swap, hr⟩⟩
  · rintro ⟨⟨a', b'⟩, heq, hm⟩
    rw [Prod.swap] at heq
    obtain ⟨rfl, rfl⟩ : b = b' ∧ a = a' := Prod.mk.injEq .. ▸ heq
    obtain ⟨w₀, t, u, ha, hb, hi, hr⟩ := mem_par_iff.1 hm
    exact ⟨w₀, u, t, hb, ha, hi.swap, hr⟩

/-! ## Deferral of closure through a shuffle -/

/-- The rewriting system `c` *defers closure through shuffling*: rewriting one
operand of a shuffle can be postponed until after the shuffle.

This is the side condition Brookes's one-line proof of associativity of `∥`
(journal p. 152) silently uses: without it, `par (par x y) z` closes the inner
shuffle before the outer one and the two bracketings need not agree.  It is the
Brookes-model analogue of Dvir–Kammar–Lahav's *Deferral of Closure* for `∥`. -/
def DefersPar (c : Rewriting E) : Prop :=
  ∀ {t t' v w : Trace E}, c.Step t t' → Interleave t' v w →
    ∃ w', Interleave t v w' ∧ c.Refines w' w

/-- Deferral extends from single steps to refinement. -/
theorem DefersPar.refines (hd : DefersPar c) {t t' : Trace E} (h : c.Refines t t') :
    ∀ {v w : Trace E}, Interleave t' v w → ∃ w', Interleave t v w' ∧ c.Refines w' w := by
  induction h with
  | refl => exact fun hi ↦ ⟨_, hi, .refl⟩
  | tail _ hstep ih =>
      intro v w hi
      obtain ⟨w₁, hi₁, hr₁⟩ := hd hstep hi
      obtain ⟨w₂, hi₂, hr₂⟩ := ih hi₁
      exact ⟨w₂, hi₂, hr₂.trans hr₁⟩

/-- Deferral on the right operand, by symmetry of shuffling. -/
theorem DefersPar.refines_right (hd : DefersPar c) {u u' : Trace E} (h : c.Refines u u')
    {t w : Trace E} (hi : Interleave t u' w) : ∃ w', Interleave t u w' ∧ c.Refines w' w := by
  obtain ⟨w', hi', hr⟩ := hd.refines h hi.swap
  exact ⟨w', hi'.swap, hr⟩

/-- **Associativity** (Brookes, Proposition 8.1: `(C₁ ∥ C₂) ∥ C₃ ≡ C₁ ∥ (C₂ ∥ C₃)`),
stated up to the associativity isomorphism of the product of return types, and
subject to `DefersPar`. -/
theorem par_assoc (hd : DefersPar c) (x : Brookes c A) (y : Brookes c B) (z : Brookes c C) :
    par (par x y) z = (fun p : A × B × C ↦ ((p.1, p.2.1), p.2.2)) <$> par x (par y z) := by
  apply ext_mem
  rintro w ⟨⟨a, b⟩, d⟩
  rw [mem_par_iff, mem_map_iff]
  constructor
  · rintro ⟨w₀, tu, v, hab, hd', hi, hr⟩
    obtain ⟨tu₀, t, u, ha, hb, hi', hr'⟩ := mem_par_iff.1 hab
    obtain ⟨w₁, hi₁, hr₁⟩ := hd.refines hr' hi
    obtain ⟨uv, huv, htuv⟩ := interleave_assoc hi' hi₁
    exact ⟨(a, b, d), rfl,
      mem_of_refines (mem_par ha (mem_par hb hd' huv) htuv) (hr₁.trans hr)⟩
  · rintro ⟨⟨a', b', d'⟩, heq, hm⟩
    obtain ⟨rfl, rfl, rfl⟩ : a = a' ∧ b = b' ∧ d = d' := by
      simp only [Prod.mk.injEq] at heq; exact ⟨heq.1.1, heq.1.2, heq.2⟩
    obtain ⟨w₀, t, uv, ha, hbd, hi, hr⟩ := mem_par_iff.1 hm
    obtain ⟨uv₀, u, v, hb, hd', hi', hr'⟩ := mem_par_iff.1 hbd
    obtain ⟨w₁, hi₁, hr₁⟩ := hd.refines_right hr' hi
    obtain ⟨tu, htu, htuv⟩ := interleave_assoc hi'.swap hi₁.swap
    exact mem_par_iff.1
      (mem_of_refines (mem_par (mem_par ha hb htu.swap) hd' htuv.swap) (hr₁.trans hr))

/-! ## Interaction with sequencing -/

/-- **Brookes's `C₁; (C₂ ∥ C₃) ⊑ (C₁; C₂) ∥ C₃`** (journal p. 152): a prefix run
before a parallel composition may equally well be run inside the left thread. -/
theorem bind_par_le_par_bind (x : Brookes c A) (f : A → Brookes c B) (y : Brookes c C) :
    (x >>= fun a ↦ par (f a) y) ≤ par (x >>= f) y := by
  apply le_of_mem
  rintro w ⟨b, d⟩ hm
  obtain ⟨a, u, v', hu, hv', hr⟩ := (mem_bind_iff _ _ _ _).1 hm
  obtain ⟨v₀, t, v, ht, hv, hi, hr'⟩ := mem_par_iff.1 hv'
  refine mem_of_refines (mem_par (mem_bind x f hu ht) hv
    ((Interleave.nil_right u).appendCompat hi)) ?_
  exact (Rewriting.refines_appendLeft u hr').trans hr

/-- **Brookes's `C₁; C₂ ⊑ C₁ ∥ C₂`** (journal p. 152), the derived law: running
two computations in sequence is one of the ways of running them in parallel. -/
theorem seq_le_par (x : Brookes c A) (y : Brookes c B) :
    (x >>= fun a ↦ y >>= fun b ↦ pure (a, b)) ≤ par x y := by
  apply le_of_mem
  rintro w ⟨a, b⟩ hm
  obtain ⟨a', u, r, hu, hr', hr⟩ := (mem_bind_iff _ _ _ _).1 hm
  obtain ⟨b', v, s, hv, hs, hrs⟩ := (mem_bind_iff _ _ _ _).1 hr'
  obtain ⟨heq, hs0⟩ := (mem_pure_iff (a', b') (a, b) s).1 hs
  obtain ⟨rfl, rfl⟩ : a = a' ∧ b = b' := Prod.mk.injEq .. ▸ heq
  refine mem_of_refines (mem_par hu hv (Interleave.append u v)) ?_
  refine (Rewriting.refines_appendLeft u ?_).trans hr
  refine Relation.ReflTransGen.trans ?_ hrs
  have := Rewriting.refines_appendLeft (c := c) v hs0
  rwa [List.append_nil] at this

end Brookes

end Isotope.Elgot
