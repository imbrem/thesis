import Isotope.Elgot.Par.Basic
import Isotope.Elgot.Par.Shuffle
import Isotope.Elgot.Brookes

/-!
# The equational theory of Brookes-style parallel composition

`Isotope.Elgot.Brookes.par` interleaves the traces of two computations and closes the result.
This module proves its laws — monotonicity, symmetry, **associativity**, **both unit laws**,
naturality, the interchange law with `bind`, and thread inlining — and packages them as
instances of the classes of `Isotope/Elgot/Par/Basic.lean`.

## The obstacle, and what removes it

`par x y` is a *closure* of raw interleavings, so an element of `par (par x y) z` interleaves
a trace that has already been rewritten.  To regroup it one must pull a rewrite back through
a shuffle:

> if `t'` is a rewrite of `t` and `w` is a shuffle of `t'` with `u`, then `w` is a rewrite of
> some shuffle `w'` of `t` with `u`.

This is **false for an arbitrary `Rewriting`**: its two congruence fields say a rewrite may be
performed in a context, not that a rewrite *is* a context surrounding a local replacement, and
a shuffle can insert events of the other thread into the middle of a rewritten block.
`IsPointwise` is the missing hypothesis: every step replaces a contiguous block by a **single**
event, in any context.  Brookes's stuttering (`ε ↝ ⟨μ,μ⟩`) and mumbling
(`⟨μ,ρ⟩⟨ρ,θ⟩ ↝ ⟨μ,θ⟩`) both have singleton right-hand sides, so `SeqCst.rewriting S` is
pointwise — and hence so is the store-buffer TSO model, which is the *same* rewriting system
at `S = St Tid Loc Val`.

## Provenance

Brookes (*Full abstraction for a shared-variable parallel language*, 1996) states the
laws of `∥` for his concrete model; nothing in the present repository proved any of them, and
the formulation by way of `IsPointwise` — one hypothesis covering every model built on
stuttering and mumbling at once — is ours.  Every proof here is original.
-/

universe u v

namespace Isotope.Elgot.Par

open Isotope.Elgot Isotope.Elgot.Brookes

variable {E : Type u} {c : Rewriting E} {A B C A' B' : Type u}

/-! ## Pointwise rewriting systems -/

/-- A rewriting system is **pointwise** when every step replaces a contiguous block of the
trace by a single event, and does so in every context.  Stuttering and mumbling are both of
this shape. -/
class IsPointwise (c : Rewriting E) : Prop where
  /-- Every step is a one-event replacement in a context. -/
  step_decomp {t t' : Trace E} : c.Step t t' →
    ∃ (p m : Trace E) (e : E) (q : Trace E),
      t = p ++ m ++ q ∧ t' = p ++ e :: q ∧
      ∀ x y : Trace E, c.Step (x ++ m ++ y) (x ++ e :: y)

/-- **Pulling one rewrite back through a shuffle.**  If `w` shuffles `t` with a rewrite `u'`
of `u`, then `w` is a rewrite of a shuffle of `t` with `u` itself. -/
theorem step_interleave_right [hp : IsPointwise c] {t u u' w : Trace E}
    (hs : c.Step u u') (hi : Interleave t u' w) :
    ∃ w', Interleave t u w' ∧ c.Refines w' w := by
  obtain ⟨p, m, e, q, rfl, rfl, hctx⟩ := hp.step_decomp hs
  obtain ⟨tp, tr, wp, wr, rfl, rfl, hip, hir⟩ := hi.splitRight p (e :: q) rfl
  obtain ⟨te, tq, we, wq, rfl, rfl, hie, hiq⟩ := hir.splitRight [e] q rfl
  obtain ⟨ua, ub, rfl, rfl⟩ := Shuffle.single_right hie
  refine ⟨wp ++ ((ua ++ m ++ ub) ++ wq), ?_, ?_⟩
  · have hmid : Interleave (ua ++ ub) m (ua ++ m ++ ub) := by
      have := (Interleave.nil_right ua).appendCompat
        ((Interleave.nil_left m).appendCompat (Interleave.nil_right ub))
      simpa using this
    have := hip.appendCompat (hmid.appendCompat hiq)
    simpa using this
  · have hstep : c.Step (ua ++ m ++ ub) (ua ++ e :: ub) := by
      have := hctx ua ub
      simpa using this
    have h1 : c.Refines ((ua ++ m ++ ub) ++ wq) ((ua ++ e :: ub) ++ wq) :=
      Rewriting.refines_appendRight (Relation.ReflTransGen.single hstep) wq
    have h2 := Rewriting.refines_appendLeft wp h1
    simpa using h2

/-- **Pulling a refinement back through a shuffle**, on the right. -/
theorem refines_interleave_right [IsPointwise c] {t u u' : Trace E}
    (hr : c.Refines u u') : ∀ {w : Trace E}, Interleave t u' w →
      ∃ w', Interleave t u w' ∧ c.Refines w' w := by
  induction hr with
  | refl => exact fun hi ↦ ⟨_, hi, .refl⟩
  | @tail b d _ hstep ih =>
      intro w hi
      obtain ⟨w₁, hi₁, hr₁⟩ := step_interleave_right hstep hi
      obtain ⟨w₂, hi₂, hr₂⟩ := ih hi₁
      exact ⟨w₂, hi₂, hr₂.trans hr₁⟩

/-- **Pulling a refinement back through a shuffle**, on the left. -/
theorem refines_interleave_left [IsPointwise c] {t t' u w : Trace E}
    (hr : c.Refines t t') (hi : Interleave t' u w) :
    ∃ w', Interleave t u w' ∧ c.Refines w' w := by
  obtain ⟨w', hi', hr'⟩ := refines_interleave_right hr hi.swap
  exact ⟨w', hi'.swap, hr'⟩

/-! ## Stuttering and mumbling are pointwise -/

/-- **Sequential consistency is a pointwise rewriting system.**  Stuttering inserts one event
and mumbling replaces two adjacent events by one, so both have singleton right-hand sides.
The store-buffer TSO model of `Isotope/Elgot/Brookes/TSO/` is this same rewriting system at
`S = St Tid Loc Val`, and so is pointwise too. -/
instance instIsPointwiseSeqCst (S : Type u) : IsPointwise (SeqCst.rewriting S) where
  step_decomp {t t'} h := by
    induction h with
    | stutter μ t =>
        refine ⟨[], [], (μ, μ), t, by simp, by simp, fun x y ↦ ?_⟩
        have := (SeqCst.rewriting S).step_appendLeft x (SeqCst.Step.stutter μ y)
        simpa using this
    | mumble μ ρ θ t =>
        refine ⟨[], [(μ, ρ), (ρ, θ)], (μ, θ), t, by simp, by simp, fun x y ↦ ?_⟩
        have := (SeqCst.rewriting S).step_appendLeft x (SeqCst.Step.mumble μ ρ θ y)
        simpa using this
    | cons q _ ih =>
        obtain ⟨p, m, e, r, rfl, rfl, hctx⟩ := ih
        exact ⟨q :: p, m, e, r, by simp, by simp, hctx⟩

/-! ## Relabelling a Brookes computation -/

/-- Membership in a relabelled computation.  `map` is `bind`-and-`pure`, so a trace of
`f <$> x` is any refinement of a trace of `x`. -/
theorem mem_map_iff {f : A → B} {x : Brookes c A} {t : Trace E} {b : B} :
    (t, b) ∈ (f <$> x) ↔ ∃ a u, (u, a) ∈ x ∧ b = f a ∧ c.Refines u t := by
  rw [map_eq_pure_bind, Brookes.mem_bind_iff]
  constructor
  · rintro ⟨a, u, v, hu, hv, hr⟩
    obtain ⟨rfl, hv'⟩ := (Brookes.mem_pure_iff (f a) b v).1 hv
    refine ⟨a, u, hu, rfl, ?_⟩
    have : c.Refines (u ++ []) (u ++ v) := Rewriting.refines_appendLeft u hv'
    simpa using this.trans hr
  · rintro ⟨a, u, hu, rfl, hr⟩
    exact ⟨a, u, [], hu, Brookes.mem_pure (f a), by simpa using hr⟩

/-! ## The laws of `par` -/

/-- Parallel composition is monotone in both arguments. -/
theorem par_mono {x x' : Brookes c A} {y y' : Brookes c B} (hx : x ≤ x') (hy : y ≤ y') :
    Brookes.par x y ≤ Brookes.par x' y' := by
  refine Brookes.le_of_mem ?_
  rintro t ⟨a, b⟩ hm
  obtain ⟨w₀, t₁, t₂, h₁, h₂, hi, hr⟩ := Brookes.mem_par_iff.1 hm
  exact Brookes.mem_par_iff.2 ⟨w₀, t₁, t₂, hx h₁, hy h₂, hi, hr⟩

/-- **Symmetry.**  Swapping the two threads swaps the two returned values, on the nose. -/
theorem par_swap (x : Brookes c A) (y : Brookes c B) :
    Prod.swap <$> Brookes.par x y = Brookes.par y x := by
  apply le_antisymm
  · refine Brookes.le_of_mem ?_
    rintro t ⟨b, a⟩ hm
    obtain ⟨⟨a', b'⟩, u, hu, hswap, hr⟩ := mem_map_iff.1 hm
    obtain ⟨rfl, rfl⟩ : b = b' ∧ a = a' := Prod.mk.injEq .. ▸ hswap
    obtain ⟨w₀, t₁, t₂, h₁, h₂, hi, hr'⟩ := Brookes.mem_par_iff.1 hu
    exact Brookes.mem_par_iff.2 ⟨w₀, t₂, t₁, h₂, h₁, hi.swap, hr'.trans hr⟩
  · refine Brookes.le_of_mem ?_
    rintro t ⟨b, a⟩ hm
    obtain ⟨w₀, t₂, t₁, h₂, h₁, hi, hr⟩ := Brookes.mem_par_iff.1 hm
    exact mem_map_iff.2 ⟨(a, b), t, Brookes.mem_par_iff.2 ⟨w₀, t₁, t₂, h₁, h₂, hi.swap, hr⟩,
      rfl, .refl⟩

/-- **Associativity**, up to the associator.  This is where `IsPointwise` is needed: the inner
`par` is a closure, so the outer shuffle must be pulled back through a rewrite before the
three-way shuffle lemma applies. -/
theorem par_assoc [IsPointwise c] (x : Brookes c A) (y : Brookes c B) (z : Brookes c C) :
    assocRL <$> Brookes.par (Brookes.par x y) z = Brookes.par x (Brookes.par y z) := by
  apply le_antisymm
  · refine Brookes.le_of_mem ?_
    rintro t ⟨a, b, d⟩ hm
    obtain ⟨⟨⟨a', b'⟩, d'⟩, u, hu, heq, hr⟩ := mem_map_iff.1 hm
    obtain ⟨rfl, rfl, rfl⟩ : a = a' ∧ b = b' ∧ d = d' := by
      simp only [assocRL, Prod.mk.injEq] at heq; exact ⟨heq.1, heq.2.1, heq.2.2⟩
    obtain ⟨w₀, s, v, hs, hv, hi, hr'⟩ := Brookes.mem_par_iff.1 hu
    obtain ⟨s₀, t₁, t₂, h₁, h₂, hi₁, hrs⟩ := Brookes.mem_par_iff.1 hs
    obtain ⟨w₁, hi₂, hr₁⟩ := refines_interleave_left hrs hi
    obtain ⟨m, hm₁, hm₂⟩ := Shuffle.assoc hi₂ hi₁
    exact Brookes.mem_par_iff.2
      ⟨w₁, t₁, m, h₁, Brookes.mem_par h₂ hv hm₁, hm₂, (hr₁.trans hr').trans hr⟩
  · refine Brookes.le_of_mem ?_
    rintro t ⟨a, b, d⟩ hm
    obtain ⟨w₀, t₁, m, h₁, hm', hi, hr⟩ := Brookes.mem_par_iff.1 hm
    obtain ⟨m₀, t₂, v, h₂, hv, hi₂, hrm⟩ := Brookes.mem_par_iff.1 hm'
    obtain ⟨w₁, hi₁, hr₁⟩ := refines_interleave_right hrm hi
    obtain ⟨ab, hab, habw⟩ := Shuffle.assoc' hi₂ hi₁
    exact mem_map_iff.2 ⟨((a, b), d), w₁,
      Brookes.mem_par_iff.2 ⟨w₁, ab, v, Brookes.mem_par h₁ h₂ hab, hv, habw, .refl⟩,
      rfl, hr₁.trans hr⟩

/-- **The right unit law.**  An idle thread on the right contributes nothing. -/
theorem par_unit_right [IsPointwise c] (x : Brookes c A) :
    (Prod.fst : A × PUnit.{u + 1} → A) <$> Brookes.par x (pure PUnit.unit) = x := by
  apply le_antisymm
  · refine Brookes.le_of_mem ?_
    rintro t a hm
    obtain ⟨⟨a', u⟩, s, hs, rfl, hr⟩ := mem_map_iff.1 hm
    obtain ⟨w₀, t₁, t₂, h₁, h₂, hi, hr'⟩ := Brookes.mem_par_iff.1 hs
    obtain ⟨-, hnil⟩ := (Brookes.mem_pure_iff PUnit.unit u t₂).1 h₂
    obtain ⟨w', hi', hr''⟩ := refines_interleave_right hnil hi
    rw [Shuffle.eq_of_nil_right hi'] at hr''
    exact x.closed.mem_of_refines h₁ ((hr''.trans hr').trans hr)
  · refine Brookes.le_of_mem ?_
    intro t a hm
    exact mem_map_iff.2 ⟨(a, PUnit.unit), t,
      Brookes.mem_par hm (Brookes.mem_pure PUnit.unit) (Interleave.nil_right t), rfl, .refl⟩

/-- **The left unit law.** -/
theorem par_unit_left [IsPointwise c] (x : Brookes c A) :
    (Prod.snd : PUnit.{u + 1} × A → A) <$> Brookes.par (pure PUnit.unit) x = x := by
  have h := par_unit_right x
  rw [← par_swap (pure PUnit.unit) x, ← comp_map] at h
  exact h

/-- **Naturality in the left argument.** -/
theorem par_map_left [IsPointwise c] (f : A → A') (x : Brookes c A) (y : Brookes c B) :
    Brookes.par (f <$> x) y = Prod.map f id <$> Brookes.par x y := by
  apply le_antisymm
  · refine Brookes.le_of_mem ?_
    rintro t ⟨a', b⟩ hm
    obtain ⟨w₀, t₁, t₂, h₁, h₂, hi, hr⟩ := Brookes.mem_par_iff.1 hm
    obtain ⟨a, u, hu, rfl, hru⟩ := mem_map_iff.1 h₁
    obtain ⟨w₁, hi₁, hr₁⟩ := refines_interleave_left hru hi
    exact mem_map_iff.2 ⟨(a, b), w₁, Brookes.mem_par hu h₂ hi₁, rfl, hr₁.trans hr⟩
  · refine Brookes.le_of_mem ?_
    rintro t ⟨a', b⟩ hm
    obtain ⟨⟨a, b'⟩, u, hu, heq, hr⟩ := mem_map_iff.1 hm
    obtain ⟨rfl, rfl⟩ : a' = f a ∧ b = b' := by
      simp only [Prod.map, Prod.mk.injEq, id_eq] at heq; exact ⟨heq.1, heq.2⟩
    obtain ⟨w₀, t₁, t₂, h₁, h₂, hi, hr'⟩ := Brookes.mem_par_iff.1 hu
    exact Brookes.mem_par_iff.2 ⟨w₀, t₁, t₂, mem_map_iff.2 ⟨a, t₁, h₁, rfl, .refl⟩, h₂, hi,
      hr'.trans hr⟩

/-- **Naturality in the right argument.** -/
theorem par_map_right [IsPointwise c] (g : B → B') (x : Brookes c A) (y : Brookes c B) :
    Brookes.par x (g <$> y) = Prod.map id g <$> Brookes.par x y := by
  have h := par_map_left g y x
  have h2 := congrArg (fun z ↦ Prod.swap <$> z) h
  simp only at h2
  rw [par_swap, ← comp_map] at h2
  rw [← par_swap x y, ← comp_map] at h2
  exact h2

/-- **The interchange law.**  Running the two threads in lockstep is one way of running them
concurrently: every interleaving that respects the seam is an interleaving. -/
theorem exchange (x : Brookes c A) (y : Brookes c B) (f : A → Brookes c A')
    (g : B → Brookes c B') :
    (Brookes.par x y >>= fun p ↦ Brookes.par (f p.1) (g p.2)) ≤
      Brookes.par (x >>= f) (y >>= g) := by
  refine Brookes.le_of_mem ?_
  rintro t ⟨a', b'⟩ hm
  obtain ⟨⟨a, b⟩, u, v, hu, hv, hr⟩ := (Brookes.mem_bind_iff _ _ _ _).1 hm
  obtain ⟨u₀, t₁, t₂, h₁, h₂, hiu, hru⟩ := Brookes.mem_par_iff.1 hu
  obtain ⟨v₀, v₁, v₂, k₁, k₂, hiv, hrv⟩ := Brookes.mem_par_iff.1 hv
  refine Brookes.mem_par_iff.2 ⟨u₀ ++ v₀, t₁ ++ v₁, t₂ ++ v₂,
    Brookes.mem_bind _ _ h₁ k₁, Brookes.mem_bind _ _ h₂ k₂, hiu.appendCompat hiv, ?_⟩
  exact (Rewriting.refines_append hru hrv).trans hr

/-- **Thread inlining.**  Running the two threads one after the other is one of the ways of
running them concurrently. -/
theorem inline_le_par (x : Brookes c A) (y : Brookes c B) :
    (x >>= fun a ↦ y >>= fun b ↦ pure (a, b)) ≤ Brookes.par x y := by
  refine Brookes.le_of_mem ?_
  rintro t ⟨a, b⟩ hm
  obtain ⟨a₀, u, v, hu, hv, hr⟩ := (Brookes.mem_bind_iff _ _ _ _).1 hm
  obtain ⟨b₀, v₁, v₂, hv₁, hv₂, hrv⟩ := (Brookes.mem_bind_iff _ _ _ _).1 hv
  obtain ⟨heq, hnil⟩ := (Brookes.mem_pure_iff (a₀, b₀) (a, b) v₂).1 hv₂
  obtain ⟨rfl, rfl⟩ : a = a₀ ∧ b = b₀ := Prod.mk.injEq .. ▸ heq
  refine Brookes.mem_par_iff.2 ⟨u ++ v₁, u, v₁, hu, hv₁, Interleave.append u v₁, ?_⟩
  have h1 : c.Refines (v₁ ++ []) (v₁ ++ v₂) := Rewriting.refines_appendLeft v₁ hnil
  simp only [List.append_nil] at h1
  exact (Rewriting.refines_append (Relation.ReflTransGen.refl) (h1.trans hrv)).trans hr

/-! ## Instances -/

/-- Brookes-style parallel composition, as a `ParOp`. -/
instance instParOp : ParOp (Brookes c) where
  par := Brookes.par

theorem par_eq (x : Brookes c A) (y : Brookes c B) :
    ParOp.par x y = Brookes.par x y := rfl

instance instParMono : ParMono (Brookes c) where
  par_mono := par_mono

instance instParSymm : ParSymm (Brookes c) where
  par_swap := par_swap

instance instParAssoc [IsPointwise c] : ParAssoc (Brookes c) where
  par_assoc := par_assoc

instance instParUnit [IsPointwise c] : ParUnit (Brookes c) where
  par_unit_right := par_unit_right
  par_unit_left := par_unit_left

instance instParNat [IsPointwise c] : ParNat (Brookes c) where
  par_map_left := par_map_left
  par_map_right := par_map_right

instance instParExchange : ParExchange (Brookes c) where
  exchange := exchange

instance instParInline : ParInline (Brookes c) where
  inline_le_par := inline_le_par

/-- **Unit-returning Brookes computations form a commutative monoid under `∥`.**  This is the
statement that can be compared directly with the pomset operator of
`Isotope/Pomset/Quotient.lean`, which is a commutative monoid on the nose. -/
instance instParMonoid [IsPointwise c] : ParMonoid (Brookes c PUnit.{u + 1}) :=
  punitParMonoid (Brookes c)

end Isotope.Elgot.Par
