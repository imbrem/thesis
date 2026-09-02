import Isotope.Elgot.Brookes.SeqCst
import Isotope.Elgot.Brookes.Parallel

/-!
# Parallel composition for sequential consistency

This file discharges, for the stuttering/mumbling rewriting system, the two
facts about `Brookes.par` that `Isotope/Elgot/Brookes/Parallel.lean` cannot
prove generically:

* `SeqCst.defersPar` — the *deferral of closure* side condition, hence
  associativity of `∥` (Brookes, Proposition 8.1) for this model;
* `SeqCst.par_pure_right` / `par_pure_left` — the unit law `C ∥ skip ≡ C`
  (Proposition 8.1) in its monadic form, where the unit is `pure`.

Both need stuttering and mumbling specifically, and both are stated by Brookes
without proof ("interleaving operations on transition traces are clearly
associative … `skip` is a unit for sequential and parallel composition because
trace sets are closed under stuttering and mumbling", journal p. 152); the
proofs here are ours.

`refines_nil_iff` characterises the traces of `pure`: they are exactly the
all-stutter traces.  Only the forward direction (`compat_eq_of_refines_nil`) was
already available.
-/

namespace Isotope.Elgot.Brookes

universe u

namespace SeqCst

variable {S : Type u} {A B : Type u}

/-! ## The traces refined from the empty trace -/

/-- A trace all of whose pairs are stutters is refined from the empty trace. -/
theorem refines_nil_of_stutters {t : Trace (S × S)} (h : ∀ p ∈ t, p.1 = p.2) :
    (rewriting S).Refines [] t := by
  induction t with
  | nil => exact .refl
  | cons p t ih =>
      obtain ⟨μ, ρ⟩ := p
      have hμ : μ = ρ := h (μ, ρ) (by simp)
      subst hμ
      exact (ih fun q hq ↦ h q (by simp [hq])).tail (Step.stutter μ t)

/-- The traces refined from the empty trace are exactly the all-stutter traces.
Equivalently: the traces of `pure` are the finite sequences of stutters. -/
theorem refines_nil_iff {t : Trace (S × S)} :
    (rewriting S).Refines [] t ↔ ∀ p ∈ t, p.1 = p.2 :=
  ⟨compat_eq_of_refines_nil, refines_nil_of_stutters⟩

/-- Shuffling in a trace of stutters can only be undone: the result refines from
the other operand. -/
theorem interleave_stutters_refines {t u w : Trace (S × S)} (h : Interleave t u w)
    (hu : ∀ p ∈ u, p.1 = p.2) : (rewriting S).Refines t w := by
  induction h with
  | nil => exact .refl
  | @left e t u w _ ih =>
      exact (rewriting S).refines_appendLeft [e] (ih hu)
  | @right e t u w _ ih =>
      obtain ⟨μ, ρ⟩ := e
      have hμ : μ = ρ := hu (μ, ρ) (by simp)
      subst hμ
      exact (ih fun q hq ↦ hu q (by simp [hq])).tail (Step.stutter μ w)

/-! ## Deferral of closure through a shuffle -/

/-- **Deferral of closure for `∥`.**  A stutter inserted into one operand of a
shuffle can be inserted into the shuffle instead, and a mumble performed in one
operand can be performed in the shuffle instead — in both cases *after* the
shuffle rather than before.  This is what makes `par` associative. -/
theorem defersPar : DefersPar (rewriting S) := by
  intro t t' v w hstep
  induction hstep generalizing v w with
  | stutter μ t =>
      intro hi
      obtain ⟨v₁, v₂, q, rfl, rfl, hq⟩ := interleave_consSplit hi rfl
      exact ⟨v₁ ++ q, (Interleave.nil_left v₁).appendCompat hq,
        .single ((rewriting S).step_appendLeft v₁ (Step.stutter μ q))⟩
  | mumble μ ρ θ t =>
      intro hi
      obtain ⟨v₁, v₂, q, rfl, rfl, hq⟩ := interleave_consSplit hi rfl
      exact ⟨v₁ ++ (μ, ρ) :: (ρ, θ) :: q,
        (Interleave.nil_left v₁).appendCompat hq.left.left,
        .single ((rewriting S).step_appendLeft v₁ (Step.mumble μ ρ θ q))⟩
  | cons p _ ih =>
      intro hi
      obtain ⟨v₁, v₂, q, rfl, rfl, hq⟩ := interleave_consSplit hi rfl
      obtain ⟨q', hq', hr'⟩ := ih hq
      exact ⟨v₁ ++ p :: q', (Interleave.nil_left v₁).appendCompat hq'.left,
        (rewriting S).refines_appendLeft v₁ ((rewriting S).refines_appendLeft [p] hr')⟩

/-- **Associativity of parallel composition** for sequential consistency
(Brookes, Proposition 8.1), up to the associativity isomorphism of the product of
return types. -/
theorem par_assoc' {C : Type u} (x : Brookes (rewriting S) A) (y : Brookes (rewriting S) B)
    (z : Brookes (rewriting S) C) :
    par (par x y) z = (fun p : A × B × C ↦ ((p.1, p.2.1), p.2.2)) <$> par x (par y z) :=
  par_assoc defersPar x y z

/-! ## The unit law -/

/-- **`C ∥ skip ≡ C`** (Brookes, Proposition 8.1) in its monadic form: `pure` is
a unit for parallel composition, because its traces are all stutters and trace
sets absorb stuttering. -/
theorem par_pure_right (x : Brookes (rewriting S) A) (b : B) :
    par x (pure b) = (fun a ↦ (a, b)) <$> x := by
  apply ext_mem
  rintro w ⟨a, b'⟩
  rw [mem_par_iff, mem_map_iff]
  constructor
  · rintro ⟨w₀, t, u, ht, hu, hi, hr⟩
    obtain ⟨hb, hu0⟩ := (mem_pure_iff b b' u).1 hu
    exact ⟨a, by rw [hb], mem_of_refines ht
      ((interleave_stutters_refines hi (refines_nil_iff.1 hu0)).trans hr)⟩
  · rintro ⟨a', heq, ha⟩
    obtain ⟨ha', hb'⟩ : a = a' ∧ b' = b := Prod.mk.injEq .. ▸ heq
    exact ⟨w, w, [], by rw [ha']; exact ha, (mem_pure_iff b b' []).2 ⟨hb', .refl⟩,
      Interleave.nil_right w, .refl⟩

/-- `pure` is a unit for parallel composition on the left. -/
theorem par_pure_left (x : Brookes (rewriting S) A) (b : B) :
    par (pure b) x = (fun a ↦ (b, a)) <$> x := by
  apply ext_mem
  rintro w ⟨b', a⟩
  rw [mem_par_iff, mem_map_iff]
  constructor
  · rintro ⟨w₀, u, t, hu, ht, hi, hr⟩
    obtain ⟨hb, hu0⟩ := (mem_pure_iff b b' u).1 hu
    exact ⟨a, by rw [hb], mem_of_refines ht
      ((interleave_stutters_refines hi.swap (refines_nil_iff.1 hu0)).trans hr)⟩
  · rintro ⟨a', heq, ha⟩
    obtain ⟨hb', ha'⟩ : b' = b ∧ a = a' := Prod.mk.injEq .. ▸ heq
    exact ⟨w, [], w, (mem_pure_iff b b' []).2 ⟨hb', .refl⟩, by rw [ha']; exact ha,
      Interleave.nil_left w, .refl⟩

end SeqCst

end Isotope.Elgot.Brookes
