import Isotope.Elgot.Brookes.SeqCst.Op.Traces

/-!
# Step-counted runs

The `while` clause of Proposition 6.2 is the one clause whose `⊆` half is not a
structural induction: peeling the first step of `while b do C` produces a run of
`C ; while b do C`, and decomposing *that* produces a run of `while b do C`
again.  The recursion is on the *number of machine steps* consumed, not on
anything structural, so this file re-presents runs with a step count.

`stepsN n x y` is `n` small steps from `x` to `y` — a plain `Nat`-recursive
definition rather than an inductive one, so that `stepsN 0` and `stepsN (n + 1)`
unfold definitionally.  `RunN n oC t oE` is `Run oC t oE` whose segments consume
`n` steps in total.  The two are interchangeable with `Relation.ReflTransGen`
and `Run` via `stepsN.steps`/`exists_stepsN` and `RunN.run`/`Run.exists_runN`;
the counted forms exist only to supply a decreasing measure.

**Only small steps are counted.**  A tempting alternative charges an extra unit
per segment, but that makes the sequential decomposition's bound
`a + b ≤ n + 1`, which is one too weak for the `while` recursion.  Counting
small steps alone gives `a + b ≤ n` exactly, and `a ≥ 1` because a run reaching
the terminated residual `none` from a running one must take at least one step
(`RunN.pos`); together these give the strict decrease `b < n` that the `while`
induction needs.

Accordingly `runN_peel` is `run_peel` with a budget: the peeled first step
accounts for the `+ 1` in `k + m + 1 ≤ n`, so the residual run and the rest of
the peeled segment are strictly cheaper than the whole.
-/

universe u

namespace Isotope.Elgot.Brookes.SeqCst.Op

open Isotope.Elgot Isotope.Elgot.Brookes

variable {Loc Val : Type u}

section

variable [DecidableEq Loc] [DecidableEq Val]

/-! ## Counted small steps -/

/-- `stepsN n x y`: the machine goes from configuration `x` to configuration `y`
in exactly `n` small steps.  Defined by recursion on `n` rather than as an
inductive family, so that both clauses hold by `rfl`. -/
def stepsN : Nat → Config Loc Val → Config Loc Val → Prop
  | 0, x, y => x = y
  | n + 1, x, y => ∃ z, CStep x z ∧ stepsN n z y

/-- Zero steps relate a configuration to itself. -/
@[simp] theorem stepsN_zero {x y : Config Loc Val} : stepsN 0 x y ↔ x = y := Iff.rfl

/-- A nonempty counted run exposes its first step. -/
theorem stepsN_succ {n : Nat} {x y : Config Loc Val} :
    stepsN (n + 1) x y ↔ ∃ z, CStep x z ∧ stepsN n z y := Iff.rfl

/-- Counted runs compose, adding their counts. -/
theorem stepsN.trans : ∀ {m n : Nat} {x y z : Config Loc Val},
    stepsN m x y → stepsN n y z → stepsN (m + n) x z := by
  intro m
  induction m with
  | zero =>
      intro n x y z h₁ h₂
      cases h₁
      rw [Nat.zero_add]
      exact h₂
  | succ m ih =>
      intro n x y z h₁ h₂
      obtain ⟨w, hw, hrest⟩ := h₁
      rw [Nat.succ_add]
      exact ⟨w, hw, ih hrest h₂⟩

/-- Forgetting the count. -/
theorem stepsN.steps : ∀ {n : Nat} {x y : Config Loc Val}, stepsN n x y →
    Relation.ReflTransGen CStep x y := by
  intro n
  induction n with
  | zero => intro x y h; cases h; exact Relation.ReflTransGen.refl
  | succ n ih =>
      intro x y h
      obtain ⟨z, hz, hrest⟩ := h
      exact Relation.ReflTransGen.head hz (ih hrest)

/-- Every run has a count. -/
theorem exists_stepsN {x y : Config Loc Val} (h : Relation.ReflTransGen CStep x y) :
    ∃ n, stepsN n x y := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | @tail b c _ hbc ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, hn.trans ⟨c, hbc, rfl⟩⟩

/-- A terminated configuration takes no steps. -/
theorem stepsN_none {n : Nat} {μ : Store Loc Val} {y : Config Loc Val}
    (h : stepsN n ((none : Option (Com Loc Val)), μ) y) : n = 0 ∧ y = (none, μ) := by
  cases n with
  | zero => exact ⟨rfl, ((stepsN_zero.1 h)).symm⟩
  | succ n => obtain ⟨z, hz, _⟩ := h; exact absurd hz id

/-! ## Counted runs -/

/-- `RunN n oC t oE` is `Run oC t oE` whose segments consume `n` small steps in
total.  Segments may still be empty, contributing a stutter pair at no cost. -/
inductive RunN : Nat → Option (Com Loc Val) → Trace (Store Loc Val × Store Loc Val) →
    Option (Com Loc Val) → Prop
  | /-- Stop, at no cost. -/ refl (oC) : RunN 0 oC [] oC
  | /-- One more segment, of known cost, at the front. -/
    cons {n m C μ oD ν t oE} : stepsN n (some C, μ) (oD, ν) → RunN m oD t oE →
      RunN (n + m) (some C) ((μ, ν) :: t) oE

/-- Forgetting the count. -/
theorem RunN.run : ∀ {n : Nat} {oC : Option (Com Loc Val)} {t oE},
    RunN n oC t oE → Run oC t oE := by
  intro n oC t oE h
  induction h with
  | refl oC => exact Run.refl oC
  | cons hs _ ih => exact Run.cons hs.steps ih

/-- Every run has a count. -/
theorem Run.exists_runN : ∀ {oC : Option (Com Loc Val)} {t oE},
    Run oC t oE → ∃ n, RunN n oC t oE := by
  intro oC t oE h
  induction h with
  | refl oC => exact ⟨0, RunN.refl oC⟩
  | cons hs _ ih =>
      obtain ⟨m, hm⟩ := ih
      obtain ⟨n, hn⟩ := exists_stepsN hs
      exact ⟨n + m, RunN.cons hn hm⟩

/-- Inversion at count `0`, in the generalized form the `RunN` induction demands:
`0` is a non-variable index, so it enters as an equational premise. -/
theorem RunN.zero_inv_gen : ∀ {n : Nat} {oC : Option (Com Loc Val)} {t oE},
    RunN n oC t oE → n = 0 → oE = oC := by
  intro n oC t oE h
  induction h with
  | refl oC => intro _; rfl
  | @cons n m C μ oD ν t oE hs _ ih =>
      intro hn
      have hm : m = 0 := by omega
      have hn0 : n = 0 := by omega
      subst hn0
      have h₃ : ((some C, μ) : Config Loc Val) = (oD, ν) := hs
      simp only [Prod.mk.injEq] at h₃
      obtain ⟨rfl, rfl⟩ := h₃
      exact ih hm

/-- A run of no steps does not change the residual. -/
theorem RunN.zero_inv {oC : Option (Com Loc Val)} {t oE} (h : RunN 0 oC t oE) : oE = oC :=
  RunN.zero_inv_gen h rfl

/-- **Reaching termination costs at least one step.**  This is what makes the
sequential decomposition's `a + b ≤ n` into a *strict* decrease for the second
component, and hence what makes the `while` recursion well-founded. -/
theorem RunN.pos {n : Nat} {C : Com Loc Val} {t : Trace (Store Loc Val × Store Loc Val)}
    (h : RunN n (some C) t none) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact absurd h.zero_inv (by simp)
  · exact hpos

/-! ## Counted peeling -/

/-- Counted peeling, in the generalized form the `RunN` induction demands: both
`some C` and `none` are non-variable indices, so they enter as equational
premises. -/
theorem runN_peel_gen : ∀ {n : Nat} {oC : Option (Com Loc Val)} {t oF}, RunN n oC t oF →
    ∀ {C : Com Loc Val}, oC = some C → oF = none →
      ∃ (s : Trace (Store Loc Val × Store Loc Val)) (μ ν : Store Loc Val)
        (oD : Option (Com Loc Val)) (ρ : Store Loc Val) (oE : Option (Com Loc Val))
        (t' : Trace (Store Loc Val × Store Loc Val)) (k m : Nat),
        (∀ p ∈ s, p.1 = p.2) ∧ t = s ++ (μ, ν) :: t' ∧ Red C μ oD ρ ∧
        stepsN k (oD, ρ) (oE, ν) ∧ RunN m oE t' none ∧ k + m + 1 ≤ n := by
  intro n oC t oF h
  induction h with
  | refl oC => intro C h₁ h₂; cases h₁; exact absurd h₂ (by simp)
  | @cons n m D a oD b t oF hs hr ih =>
      intro C h₁ h₂
      cases h₁
      cases n with
      | zero =>
          have h₃ : ((some D, a) : Config Loc Val) = (oD, b) := hs
          simp only [Prod.mk.injEq] at h₃
          obtain ⟨rfl, rfl⟩ := h₃
          obtain ⟨s, μ, ν, oD', ρ, oE, t', k, m', hst, ht, hred, hsteps, hrun, hle⟩ :=
            ih rfl h₂
          refine ⟨(a, a) :: s, μ, ν, oD', ρ, oE, t', k, m', ?_, ?_, hred, hsteps, hrun, ?_⟩
          · intro p hp
            rcases List.mem_cons.1 hp with rfl | hp
            · rfl
            · exact hst p hp
          · rw [ht]; rfl
          · omega
      | succ n =>
          obtain ⟨z, hz₁, hz₂⟩ := hs
          obtain ⟨z₁, z₂⟩ := z
          exact ⟨[], a, b, z₁, z₂, oD, t, n, m, by simp, rfl, hz₁, hz₂, h₂ ▸ hr, by omega⟩

/-- **Counted peeling.**  `run_peel` with a step budget: a counted transition
trace of `C` begins with stutter-only segments, then takes its first real small
step; the remainder of that segment costs `k`, the residual run costs `m`, and
`k + m + 1 ≤ n` — the `+ 1` being the peeled step itself. -/
theorem runN_peel {n : Nat} {C : Com Loc Val} {t : Trace (Store Loc Val × Store Loc Val)}
    (h : RunN n (some C) t none) :
    ∃ (s : Trace (Store Loc Val × Store Loc Val)) (μ ν : Store Loc Val)
      (oD : Option (Com Loc Val)) (ρ : Store Loc Val) (oE : Option (Com Loc Val))
      (t' : Trace (Store Loc Val × Store Loc Val)) (k m : Nat),
      (∀ p ∈ s, p.1 = p.2) ∧ t = s ++ (μ, ν) :: t' ∧ Red C μ oD ρ ∧
      stepsN k (oD, ρ) (oE, ν) ∧ RunN m oE t' none ∧ k + m + 1 ≤ n :=
  runN_peel_gen h rfl rfl

end

end Isotope.Elgot.Brookes.SeqCst.Op
