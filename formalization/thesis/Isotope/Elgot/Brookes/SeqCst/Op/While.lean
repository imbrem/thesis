import Isotope.Elgot.Brookes.SeqCst.Op.Seq
import Isotope.Elgot.Brookes.SeqCst.Op.Clauses
import Isotope.Elgot.Brookes.SeqCst.Laws

/-!
# Proposition 6.2: the loop clause

This file proves

```
T[while B do C] = (T[B];T[C])*;T[¬B]
```

i.e. `opDen (Com.wh b C) = star (test b.eval >>= fun _ ↦ opDen C)
  >>= fun _ ↦ test (BExp.neg b).eval`, which is `SeqCst.den`'s defining clause
for `wh` read operationally.

The proof is in three pieces.

* `opDen_wh_unfold` is the operational form of the already-proved
  `SeqCst.den_wh_unfold`: peeling the first small step off a transition trace of
  `while B do C` exposes either `whT` (the guard holds, and the machine
  continues as `C ; while B do C`) or `whF` (the guard fails and the loop
  terminates at once).  It is an unconditional equation and needs no induction.

* `opDen_wh_ge` — the `⊇` half — is an induction over the `power`s of the loop
  body, using `opDen_wh_unfold` and the sequential clause `opDen_seq` to absorb
  one more iteration at each step.  No operational reasoning is involved beyond
  the two one-step transition traces `ttrace_wh_true` and `ttrace_wh_false`.

* `runN_wh_mem` — the `⊆` half — is the one place in the development that needs
  step indexing.  A transition trace of `while B do C` is decomposed by peeling
  its first step and then splitting the resulting run of `C ; while B do C` with
  `runN_seq_inv`; the residual run of `while B do C` is *structurally larger*
  than nothing at all, so the recursion cannot be justified by an induction on
  the run.  It is justified instead by the step count: the peel costs one step
  and, by `RunN.pos`, `C`'s own run costs at least one more, so the tail loop's
  run is strictly cheaper.  Hence `Nat.strong_induction_on` on the count.

## Where the closure is unavoidable

Exactly as for `ite` and `seq`: the loop's own step contributes a stutter pair
`⟨μ, μ⟩` that the environment need not observe, so it is mumbled into the
following pair (`refines_mumble_head`), and the stutter pairs of segments in
which the machine did not move at all are absorbed by `refines_stutter_prefix`.
-/

universe u

namespace Isotope.Elgot.Brookes.SeqCst.Op

open Isotope.Elgot Isotope.Elgot.Brookes

variable {Loc Val : Type u}

section

variable [DecidableEq Loc] [DecidableEq Val]

/-! ## One-step transition traces of a loop -/

/-- Exiting the loop: when the guard fails, `while b do C` takes a single step
to termination, contributing one stutter pair. -/
theorem ttrace_wh_false {b : BExp Loc Val} {C : Com Loc Val} {μ : Store Loc Val}
    (hb : b.eval μ = false) : TTrace (Com.wh b C) [(μ, μ)] :=
  Run.cons (steps_single (Red.whF hb)) (Run.refl (none : Option (Com Loc Val)))

/-- Entering the loop body: when the guard holds, `while b do C` takes a single
stutter step and continues as `C ; while b do C`. -/
theorem ttrace_wh_true {b : BExp Loc Val} {C : Com Loc Val} {μ : Store Loc Val}
    {w : Trace (Store Loc Val × Store Loc Val)} (hb : b.eval μ = true)
    (h : TTrace (Com.seq C (Com.wh b C)) w) : TTrace (Com.wh b C) ((μ, μ) :: w) :=
  Run.cons (steps_single (Red.whT hb)) h

/-! ## Unfolding -/

omit [DecidableEq Loc] [DecidableEq Val] in
/-- A computation is below the left summand's binary union with anything. -/
theorem le_union2_left (x y : Comp Loc Val PUnit) : x ≤ SeqCst.union2 x y :=
  Brookes.le_of_mem fun _ _ hm ↦ SeqCst.mem_union2_iff.2 (Or.inl hm)

/-- **Operational loop unfolding**, the transition-trace form of
`SeqCst.den_wh_unfold`:
`T[while B do C] = T[B];T[C ; while B do C] ∪ T[¬B]`.

The `⊆` half peels the first small step, which must be `whT` or `whF`; the
`⊇` half is `ttrace_wh_true`/`ttrace_wh_false`.  Unlike the denotational
unfolding this is proved directly from the machine, with no appeal to the
Kleene star. -/
theorem opDen_wh_unfold (b : BExp Loc Val) (C : Com Loc Val) :
    opDen (Com.wh b C)
      = SeqCst.union2 (SeqCst.test b.eval >>= fun _ ↦ opDen (Com.seq C (Com.wh b C)))
          (SeqCst.test (BExp.neg b).eval) := by
  apply Brookes.ext_mem
  intro t x
  constructor
  · rintro ⟨t₀, ht₀, hr⟩
    obtain ⟨s, μ, ν, oD, ρ, oE, t', hst, ht, hred, hsteps, hrun⟩ := run_peel ht₀
    simp only at ht hr
    subst ht
    cases hred with
    | whT hb =>
        have hfin : (rewriting (Store Loc Val)).Refines ((μ, μ) :: (μ, ν) :: t') t :=
          ((refines_mumble_head μ ν t').trans
            (refines_stutter_prefix hst ((μ, ν) :: t'))).trans hr
        refine SeqCst.mem_union2_iff.2 (Or.inl (Brookes.mem_of_refines ?_ hfin))
        exact (Brookes.mem_bind_iff _ _ _ x).2
          ⟨PUnit.unit, [(μ, μ)], (μ, ν) :: t',
            SeqCst.mem_atom_iff.2 ⟨μ, μ, ⟨hb, rfl⟩, Relation.ReflTransGen.refl⟩,
            mem_opDen (Run.cons hsteps hrun) x, Relation.ReflTransGen.refl⟩
    | whF hb =>
        have hy : ((oE, ν) : Config Loc Val) = ((none : Option (Com Loc Val)), μ) :=
          steps_none_inv hsteps
        rw [Prod.mk.injEq] at hy
        obtain ⟨hoE, hν⟩ := hy
        subst hoE
        subst hν
        obtain ⟨rfl, -⟩ := Run.none_inv hrun
        refine SeqCst.mem_union2_iff.2 (Or.inr (Brookes.mem_of_refines ?_
          ((refines_stutter_prefix hst [(ν, ν)]).trans hr)))
        exact SeqCst.mem_atom_iff.2
          ⟨ν, ν, ⟨(neg_eval b ν).2 hb, rfl⟩, Relation.ReflTransGen.refl⟩
  · intro h
    rcases SeqCst.mem_union2_iff.1 h with h | h
    · obtain ⟨_, u, v, hu, hv, hruv⟩ := (Brookes.mem_bind_iff _ _ t x).1 h
      obtain ⟨μ, ν, ⟨hb, rfl⟩, hu'⟩ := SeqCst.mem_atom_iff.1 hu
      obtain ⟨v₀, hv₀, hv'⟩ := hv
      exact Brookes.mem_of_refines (mem_opDen (ttrace_wh_true hb hv₀) x)
        ((Rewriting.refines_append hu' hv').trans hruv)
    · obtain ⟨μ, ν, ⟨hb, rfl⟩, hu'⟩ := SeqCst.mem_atom_iff.1 h
      exact Brookes.mem_of_refines
        (mem_opDen (ttrace_wh_false ((neg_eval b ν).1 hb)) x) hu'

/-! ## The easy inclusion -/

/-- Every `n`-fold iteration of the loop body followed by a failing guard is a
transition trace of the loop.  The induction step absorbs one iteration using
the operational unfolding and the sequential clause. -/
theorem power_bind_le_opDen_wh (b : BExp Loc Val) (C : Com Loc Val) : ∀ n : Nat,
    (SeqCst.power (SeqCst.test b.eval >>= fun _ ↦ opDen C) n
      >>= fun _ ↦ SeqCst.test (BExp.neg b).eval) ≤ opDen (Com.wh b C) := by
  intro n
  induction n with
  | zero =>
      rw [SeqCst.power_zero, Brookes.pure_bind_eq]
      refine Brookes.le_of_mem fun t x hm ↦ ?_
      obtain ⟨μ, ν, ⟨hb, rfl⟩, hr⟩ := SeqCst.mem_atom_iff.1 hm
      exact Brookes.mem_of_refines
        (mem_opDen (ttrace_wh_false ((neg_eval b ν).1 hb)) x) hr
  | succ n ih =>
      rw [SeqCst.power_succ, Brookes.bind_assoc_eq]
      refine le_trans (Brookes.bind_mono_right _ fun _ ↦ ih) ?_
      rw [Brookes.bind_assoc_eq, ← opDen_seq C (Com.wh b C)]
      conv_rhs => rw [opDen_wh_unfold b C]
      exact le_union2_left _ _

/-- **The `⊇` half of the loop clause.**  `(T[B];T[C])*;T[¬B] ⊆ T[while B do C]`. -/
theorem opDen_wh_ge (b : BExp Loc Val) (C : Com Loc Val) :
    (SeqCst.star (SeqCst.test b.eval >>= fun _ ↦ opDen C)
      >>= fun _ ↦ SeqCst.test (BExp.neg b).eval) ≤ opDen (Com.wh b C) := by
  have hs : SeqCst.star (SeqCst.test b.eval >>= fun _ ↦ opDen C)
      = Brookes.iUnion (SeqCst.power (SeqCst.test b.eval >>= fun _ ↦ opDen C)) := rfl
  rw [hs, Brookes.iUnion_bind]
  exact Brookes.iUnion_le (power_bind_le_opDen_wh b C)

/-! ## The hard inclusion -/

/-- **The `⊆` half of the loop clause**, by strong induction on the number of
small steps.

Peeling the first step of a run of `while b do C` costs one step; if the guard
holds, `runN_seq_inv` splits the rest into a run of `C` and a run of
`while b do C`, and `RunN.pos` says the former costs at least one step, so the
latter is strictly cheaper than the whole.  That strict decrease — not a
structural one, since the residual loop is the very same command — is what makes
the recursion well founded. -/
theorem runN_wh_mem (b : BExp Loc Val) (C : Com Loc Val) : ∀ (n : Nat)
    (t : Trace (Store Loc Val × Store Loc Val)), RunN n (some (Com.wh b C)) t none →
      (t, PUnit.unit) ∈ (SeqCst.star (SeqCst.test b.eval >>= fun _ ↦ opDen C)
        >>= fun _ ↦ SeqCst.test (BExp.neg b).eval) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t h
    obtain ⟨s, μ, ν, oD, ρ, oE, t', k, m, hst, ht, hred, hk, hm, hkm⟩ := runN_peel h
    subst ht
    cases hred with
    | whF hb =>
        obtain ⟨-, hy⟩ := stepsN_none hk
        rw [Prod.mk.injEq] at hy
        obtain ⟨hoE, hν⟩ := hy
        subst hoE
        subst hν
        obtain ⟨rfl, -⟩ := Run.none_inv hm.run
        refine (Brookes.mem_bind_iff _ _ _ PUnit.unit).2
          ⟨PUnit.unit, [], [(ν, ν)], ?_, ?_, ?_⟩
        · exact SeqCst.mem_star_iff.2
            ⟨0, by rw [SeqCst.power_zero]; exact Brookes.mem_pure PUnit.unit⟩
        · exact SeqCst.mem_atom_iff.2
            ⟨ν, ν, ⟨(neg_eval b ν).2 hb, rfl⟩, Relation.ReflTransGen.refl⟩
        · exact refines_stutter_prefix hst [(ν, ν)]
    | whT hb =>
        have hseq : RunN (k + m) (some (Com.seq C (Com.wh b C))) ((μ, ν) :: t') none :=
          RunN.cons hk hm
        obtain ⟨t₁, t₂, a, c, h₁, h₂, hac, href⟩ := runN_seq_inv hseq
        have hpos : 0 < a := RunN.pos h₁
        have hlt : c < n := by omega
        obtain ⟨a', u, v, hu, hv, hruv⟩ :=
          (Brookes.mem_bind_iff _ _ t₂ PUnit.unit).1 (ih c hlt t₂ h₂)
        obtain rfl : a' = PUnit.unit := rfl
        have hX : (((μ, μ) :: t₁), PUnit.unit)
            ∈ (SeqCst.test b.eval >>= fun _ ↦ opDen C) :=
          (Brookes.mem_bind_iff _ _ _ PUnit.unit).2
            ⟨PUnit.unit, [(μ, μ)], t₁,
              SeqCst.mem_atom_iff.2 ⟨μ, μ, ⟨hb, rfl⟩, Relation.ReflTransGen.refl⟩,
              mem_opDen h₁.run PUnit.unit, Relation.ReflTransGen.refl⟩
        have hstar : ((((μ, μ) :: t₁) ++ u), PUnit.unit)
            ∈ SeqCst.star (SeqCst.test b.eval >>= fun _ ↦ opDen C) := by
          rw [SeqCst.star_unfold]
          exact SeqCst.mem_union2_iff.2 (Or.inr ((Brookes.mem_bind_iff _ _ _ PUnit.unit).2
            ⟨PUnit.unit, (μ, μ) :: t₁, u, hX, hu, Relation.ReflTransGen.refl⟩))
        refine (Brookes.mem_bind_iff _ _ _ PUnit.unit).2
          ⟨PUnit.unit, ((μ, μ) :: t₁) ++ u, v, hstar, hv, ?_⟩
        simp only [List.cons_append, List.append_assoc]
        refine Relation.ReflTransGen.trans
          (Rewriting.refines_appendLeft [(μ, μ)]
            ((Rewriting.refines_appendLeft t₁ hruv).trans href)) ?_
        exact (refines_mumble_head μ ν t').trans
          (refines_stutter_prefix hst ((μ, ν) :: t'))

/-! ## The clause -/

/-- **Brookes, Proposition 6.2, the loop:**
`T[while B do C] = (T[B];T[C])*;T[¬B]`.

`⊆` is `runN_wh_mem`, `⊇` is `opDen_wh_ge`. -/
theorem opDen_wh (b : BExp Loc Val) (C : Com Loc Val) :
    opDen (Com.wh b C)
      = (SeqCst.star (SeqCst.test b.eval >>= fun _ ↦ opDen C)
          >>= fun _ ↦ SeqCst.test (BExp.neg b).eval) := by
  apply le_antisymm
  · refine opDen_le_iff.2 fun t ht ↦ ?_
    obtain ⟨n, hn⟩ := Run.exists_runN ht
    exact runN_wh_mem b C n t hn
  · exact opDen_wh_ge b C

end

end Isotope.Elgot.Brookes.SeqCst.Op
