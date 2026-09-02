import Isotope.Elgot.Brookes.Iteration
import Isotope.Elgot.Trace

/-!
# Comparison with the deterministic finite-trace model

`FiniteTrace E A` records at most one terminating observation, a value together
with its complete finite trace.  Every such computation has a Brookes denotation:
close its unique observation under the rewriting system.  Divergence, which
`FiniteTrace` records as `Part.none`, becomes `⊥`.

`ofFiniteTrace` is a morphism of monads *with iteration*: it commutes with `pure`,
`bind` and `iter` on the nose.  It is not injective, and that is the point —
Brookes identifies observations that `FiniteTrace` keeps apart, namely any two
traces related by the closure rules.

The analogous comparison with the nondeterministic finite/infinite trace-set
monad of issue #28 is *not* stated here: no such carrier exists in this
formalization yet.  The intended shape, with `ε := Trace E` and
`τ := Stream' E`, is

```
def ofTraceSet (x : TraceSet E (Stream' E) A) : Brookes c A :=
  close c {p | Trace.done p.2 p.1 ∈ x}
```

which discards `Trace.inf` outright and so should factor through the finite part
of that model's iteration.
-/

namespace Isotope.Elgot

universe u

namespace Brookes

variable {E : Type u} {A B : Type u}

/-- The Brookes denotation of a deterministic finite-trace computation: the
closure of its unique terminating observation. -/
def ofFiniteTrace (c : Rewriting E) (x : FiniteTrace E A) : Brookes c A :=
  close c {p : Trace E × A | (p.2, (p.1 : FreeMonoid E)) ∈ x}

theorem mem_ofFiniteTrace_iff (c : Rewriting E) (x : FiniteTrace E A) (t : Trace E) (a : A) :
    (t, a) ∈ ofFiniteTrace c x ↔ ∃ t₀ : Trace E, (a, (t₀ : FreeMonoid E)) ∈ x ∧
      c.Refines t₀ t := Iff.rfl

@[simp] theorem ofFiniteTrace_diverge (c : Rewriting E) :
    ofFiniteTrace c (FiniteTrace.diverge : FiniteTrace E A) = ⊥ := by
  apply ext_mem
  intro t a
  rw [mem_ofFiniteTrace_iff]
  constructor
  · rintro ⟨t₀, h, -⟩
    exact (FiniteTrace.not_mem_diverge (a, (t₀ : FreeMonoid E)) h).elim
  · intro h; exact h.elim

@[simp] theorem ofFiniteTrace_done (c : Rewriting E) (t : Trace E) (a : A) :
    ofFiniteTrace c (FiniteTrace.done (t : FreeMonoid E) a) = close c {(t, a)} := by
  apply ext_mem
  intro u b
  rw [mem_ofFiniteTrace_iff, mem_close_iff]
  constructor
  · rintro ⟨u₀, hu₀, hru⟩
    have hu₀' : (b, u₀) = (a, t) := _root_.Part.mem_some_iff.1 hu₀
    rw [Prod.mk.injEq] at hu₀'
    obtain ⟨rfl, rfl⟩ := hu₀'
    exact ⟨u₀, rfl, hru⟩
  · rintro ⟨u₀, hu₀, hru⟩
    rw [Set.mem_singleton_iff, Prod.mk.injEq] at hu₀
    obtain ⟨rfl, rfl⟩ := hu₀
    exact ⟨u₀, _root_.Part.mem_some _, hru⟩

@[simp] theorem ofFiniteTrace_pure (c : Rewriting E) (a : A) :
    ofFiniteTrace c (pure a : FiniteTrace E A) = (pure a : Brookes c A) := by
  apply ext_mem
  intro u b
  rw [mem_ofFiniteTrace_iff, mem_pure_iff]
  constructor
  · rintro ⟨u₀, hu₀, hru⟩
    have hu₀' : (b, u₀) = (a, (1 : FreeMonoid E)) := _root_.Part.mem_some_iff.1 hu₀
    have hb : b = a := congrArg Prod.fst hu₀'
    have hu : u₀ = (1 : FreeMonoid E) := congrArg Prod.snd hu₀'
    subst hb
    subst hu
    exact ⟨rfl, hru⟩
  · rintro ⟨rfl, hru⟩
    exact ⟨[], _root_.Part.mem_some _, hru⟩

theorem ofFiniteTrace_bind (c : Rewriting E) (x : FiniteTrace E A) (f : A → FiniteTrace E B) :
    ofFiniteTrace c (x >>= f) = ofFiniteTrace c x >>= fun a ↦ ofFiniteTrace c (f a) := by
  apply ext_mem
  intro t b
  rw [mem_ofFiniteTrace_iff, mem_bind_iff]
  constructor
  · rintro ⟨t₀, hmem, hr⟩
    obtain ⟨a, u, v, hu, hv, rfl⟩ := (FiniteTrace.mem_bind_iff x f b t₀).1 hmem
    exact ⟨a, u, v, (mem_ofFiniteTrace_iff c x u a).2 ⟨u, hu, .refl⟩,
      (mem_ofFiniteTrace_iff c (f a) v b).2 ⟨v, hv, .refl⟩, hr⟩
  · rintro ⟨a, u, v, hu, hv, hr⟩
    obtain ⟨u₀, hu₀, hru⟩ := (mem_ofFiniteTrace_iff c x u a).1 hu
    obtain ⟨v₀, hv₀, hrv⟩ := (mem_ofFiniteTrace_iff c (f a) v b).1 hv
    refine ⟨u₀ ++ v₀, (FiniteTrace.mem_bind_iff x f b _).2 ⟨a, u₀, v₀, hu₀, hv₀, rfl⟩, ?_⟩
    exact (Rewriting.refines_append hru hrv).trans hr

theorem mem_iter_of_finiteTrace_runs {c : Rewriting E} {f : A → FiniteTrace E (B ⊕ A)} {a : A}
    {b : B} {t : Trace E} (h : FiniteTrace.Runs f a b t) :
    (t, b) ∈ iter (fun a ↦ ofFiniteTrace c (f a)) a := by
  induction h with
  | @done a b t h₀ =>
    exact mem_iter_done ((mem_ofFiniteTrace_iff c (f a) t (Sum.inl b)).2 ⟨t, h₀, .refl⟩)
  | @more a a' b t t' h₀ _ ih =>
    exact mem_iter_more ((mem_ofFiniteTrace_iff c (f a) t (Sum.inr a')).2 ⟨t, h₀, .refl⟩) ih

theorem mem_ofFiniteTrace_iter_of_runs {c : Rewriting E} {f : A → FiniteTrace E (B ⊕ A)} {a : A}
    {b : B} {t : Trace E} (h : Runs (fun a ↦ ofFiniteTrace c (f a)) a b t) :
    (t, b) ∈ ofFiniteTrace c (iter f a) := by
  induction h with
  | @done a b t h₀ =>
    obtain ⟨u, hu, hru⟩ := (mem_ofFiniteTrace_iff c (f a) t (Sum.inl b)).1 h₀
    exact (mem_ofFiniteTrace_iff c (iter f a) t b).2
      ⟨u, (FiniteTrace.mem_iter_iff f a b _).2 (.done hu), hru⟩
  | @more a a' b t t' h₀ _ ih =>
    obtain ⟨u, hu, hru⟩ := (mem_ofFiniteTrace_iff c (f a) t (Sum.inr a')).1 h₀
    obtain ⟨w, hw, hrw⟩ := (mem_ofFiniteTrace_iff c (iter f a') t' b).1 ih
    refine (mem_ofFiniteTrace_iff c (iter f a) (t ++ t') b).2 ⟨u ++ w, ?_, ?_⟩
    · exact (FiniteTrace.mem_iter_iff f a b _).2
        (.more hu ((FiniteTrace.mem_iter_iff f a' b w).1 hw))
    · exact Rewriting.refines_append hru hrw

/-- `ofFiniteTrace` commutes with iteration on the nose. -/
theorem ofFiniteTrace_iter (c : Rewriting E) (f : A → FiniteTrace E (B ⊕ A)) (a : A) :
    ofFiniteTrace c (iter f a) = iter (fun a ↦ ofFiniteTrace c (f a)) a := by
  apply ext_mem
  intro t b
  constructor
  · intro h
    obtain ⟨t₀, hmem, hr⟩ := (mem_ofFiniteTrace_iff c (iter f a) t b).1 h
    exact mem_of_refines
      (mem_iter_of_finiteTrace_runs ((FiniteTrace.mem_iter_iff f a b t₀).1 hmem)) hr
  · intro h
    obtain ⟨t₀, hrun, hr⟩ := (mem_iter_iff_runs _ a t b).1 h
    exact mem_of_refines (mem_ofFiniteTrace_iter_of_runs hrun) hr

/-- `ofFiniteTrace` is monotone for refinement of the recorded trace: Brookes
identifies observations the deterministic model keeps apart. -/
theorem ofFiniteTrace_le_of_refines (c : Rewriting E) {t t' : Trace E}
    (h : c.Refines t t') (a : A) :
    ofFiniteTrace c (FiniteTrace.done (t' : FreeMonoid E) a) ≤
      ofFiniteTrace c (FiniteTrace.done (t : FreeMonoid E) a) := by
  apply le_of_mem
  intro u b hu
  obtain ⟨u₀, hu₀, hru⟩ := (mem_ofFiniteTrace_iff c _ u b).1 hu
  have hu₀' : (b, u₀) = (a, t') := _root_.Part.mem_some_iff.1 hu₀
  rw [Prod.mk.injEq] at hu₀'
  obtain ⟨rfl, rfl⟩ := hu₀'
  exact (mem_ofFiniteTrace_iff c _ u b).2 ⟨t, _root_.Part.mem_some _, h.trans hru⟩

end Brookes

end Isotope.Elgot
