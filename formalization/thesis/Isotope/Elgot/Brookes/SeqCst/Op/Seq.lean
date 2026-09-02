import Isotope.Elgot.Brookes.SeqCst.Op.Counted

/-!
# Proposition 6.2: the sequential composition clause

This file proves

```
T[C₁ ; C₂] = T[C₁] ; T[C₂]
```

i.e. `opDen (Com.seq C₁ C₂) = opDen C₁ >>= fun _ ↦ opDen C₂`.

Everything turns on `seqCfg`, which describes the configurations reachable from
`C₁ ; C₂`: they are exactly `D₁ ; C₂` for a residual `D₁` of `C₁`, together with
`C₂` itself once `C₁` has terminated.  Reading `seqCfg` as a map on *residuals*
folds the two congruence rules `Red.seqL`/`Red.seqR` into a single statement,
and likewise folds the two cases of the decomposition, which halves the work:
`steps_seq_cong` and `stepsN_seq_cong` say that `C₁`'s execution lifts to
`C₁ ; C₂` step for step, and `stepsN_seq_inv` says every execution of `C₁ ; C₂`
arises that way.

Note that lifting is *exact* on step counts.  The step by which `C₁` terminates
(`Red C₁ μ none ν`) is the same step by which `C₁ ; C₂` hands control to `C₂`
(`Red.seqR`); no administrative step is inserted.  This is what makes the
counted decomposition's bound `a + b = n` — and hence, after peeling, the strict
decrease that `Op/While.lean` needs.

## Where the closure is unavoidable

A transition trace of `C₁ ; C₂` need not split as a transition trace of `C₁`
followed by one of `C₂`: the environment is not obliged to interrupt the machine
at the moment control passes from `C₁` to `C₂`, so a single segment `⟨μ, ν⟩` of
the trace may contain both the end of `C₁` (reaching some `ρ`) and the start of
`C₂`.  The decomposition therefore produces `⟨μ, ρ⟩` for `C₁` and `⟨ρ, ν⟩` for
`C₂`, and recovers the original by exactly one *mumbling* step.  This is why the
inversion lemmas conclude with a refinement `Refines (t₁ ++ t₂) t` rather than
an equality, and why the clause is an identity of *closed* trace sets.

The counted inversion `runN_seq_inv` is proved first and the uncounted
`ttrace_seq_inv` derived from it, so that the decomposition is written once.
-/

universe u

namespace Isotope.Elgot.Brookes.SeqCst.Op

open Isotope.Elgot Isotope.Elgot.Brookes

variable {Loc Val : Type u}

section

variable [DecidableEq Loc] [DecidableEq Val]

/-! ## Sequential residuals -/

/-- The residual of `C₁ ; C₂` determined by a residual of `C₁`: while `C₁` is
still running the whole command is `D₁ ; C₂`, and once `C₁` has terminated it is
`C₂`.  Every configuration reachable from `C₁ ; C₂` has this form. -/
def seqCfg : Option (Com Loc Val) → Com Loc Val → Option (Com Loc Val)
  | none, C₂ => some C₂
  | some C₁, C₂ => some (Com.seq C₁ C₂)

/-! ## Congruence -/

/-- **Counted sequential congruence.**  An execution of `C₁` lifts to one of
`C₁ ; C₂` consuming exactly the same number of steps: the step by which `C₁`
terminates is the step by which `C₁ ; C₂` hands control to `C₂`. -/
theorem stepsN_seq_cong : ∀ {n : Nat} {C₁ : Com Loc Val} {μ : Store Loc Val}
    {y : Config Loc Val}, stepsN n (some C₁, μ) y → ∀ C₂ : Com Loc Val,
      stepsN n (some (Com.seq C₁ C₂), μ) (seqCfg y.1 C₂, y.2) := by
  intro n
  induction n with
  | zero =>
      intro C₁ μ y h C₂
      have h' : ((some C₁, μ) : Config Loc Val) = y := h
      subst h'
      rfl
  | succ n ih =>
      intro C₁ μ y h C₂
      obtain ⟨z, hz, hrest⟩ := h
      obtain ⟨z₁, z₂⟩ := z
      cases z₁ with
      | none =>
          obtain ⟨hn, hy⟩ := stepsN_none hrest
          subst hn
          subst hy
          exact ⟨(some C₂, z₂), Red.seqR (cstep_some.1 hz), rfl⟩
      | some C₁' =>
          exact ⟨(some (Com.seq C₁' C₂), z₂), Red.seqL (cstep_some.1 hz), ih hrest C₂⟩

/-- **Sequential congruence.**  An execution of `C₁` lifts to one of `C₁ ; C₂`.
Stated over a variable target `y` with `y.1`/`y.2` projections, as a
`Relation.ReflTransGen` induction demands. -/
theorem steps_seq_cong {C₁ : Com Loc Val} {μ : Store Loc Val} {y : Config Loc Val}
    (h : Relation.ReflTransGen CStep (some C₁, μ) y) (C₂ : Com Loc Val) :
    Relation.ReflTransGen CStep (some (Com.seq C₁ C₂), μ) (seqCfg y.1 C₂, y.2) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hxy hyz ih =>
      obtain ⟨b₁, b₂⟩ := b
      obtain ⟨c₁, c₂⟩ := c
      cases b₁ with
      | none => exact absurd hyz id
      | some D =>
          cases c₁ with
          | none => exact ih.tail (Red.seqR (cstep_some.1 hyz))
          | some D' => exact ih.tail (Red.seqL (cstep_some.1 hyz))

/-! ## Decomposition of executions -/

/-- **Counted sequential decomposition.**  An execution of `C₁ ; C₂` either
stays inside `C₁`, or splits into an execution of `C₁` that terminates in some
intermediate store `ρ` followed by an execution of `C₂` from `ρ`, the two
consuming `n` steps between them. -/
theorem stepsN_seq_inv : ∀ {n : Nat} {C₁ C₂ : Com Loc Val} {μ : Store Loc Val}
    {y : Config Loc Val}, stepsN n (some (Com.seq C₁ C₂), μ) y →
      (∃ C₁' ν, y = (some (Com.seq C₁' C₂), ν) ∧ stepsN n (some C₁, μ) (some C₁', ν))
    ∨ (∃ ρ a b, stepsN a (some C₁, μ) ((none : Option (Com Loc Val)), ρ) ∧
        stepsN b (some C₂, ρ) y ∧ a + b = n) := by
  intro n
  induction n with
  | zero =>
      intro C₁ C₂ μ y h
      have h' : ((some (Com.seq C₁ C₂), μ) : Config Loc Val) = y := h
      subst h'
      exact Or.inl ⟨C₁, μ, rfl, rfl⟩
  | succ n ih =>
      intro C₁ C₂ μ y h
      obtain ⟨z, hz, hrest⟩ := h
      obtain ⟨z₁, z₂⟩ := z
      have hz' : Red (Com.seq C₁ C₂) μ z₁ z₂ := hz
      cases hz' with
      | @seqL _ _ C₁' _ _ hstep =>
          rcases ih hrest with ⟨C₁'', ν, hy, hs⟩ | ⟨ρ, a, b, ha, hb, hab⟩
          · exact Or.inl ⟨C₁'', ν, hy, ⟨(some C₁', z₂), hstep, hs⟩⟩
          · exact Or.inr ⟨ρ, a + 1, b, ⟨(some C₁', z₂), hstep, ha⟩, hb, by omega⟩
      | @seqR _ _ _ _ hstep =>
          exact Or.inr ⟨z₂, 1, n, ⟨((none : Option (Com Loc Val)), z₂), hstep, rfl⟩,
            hrest, by omega⟩

/-! ## Decomposition of transition traces -/

/-- Counted decomposition of transition traces, in the generalized form the
`RunN` induction demands: the initial residual is an arbitrary `seqCfg oD₁ C₂`,
and the final residual `none` enters as an equational premise.

The `+ 1` that peeling would need is absent here: `a + b ≤ n` exactly, because
the congruence is exact on step counts. -/
theorem runN_seq_inv_gen : ∀ {n : Nat} {oC : Option (Com Loc Val)}
    {t : Trace (Store Loc Val × Store Loc Val)} {oE}, RunN n oC t oE →
    ∀ {oD₁ : Option (Com Loc Val)} {C₂ : Com Loc Val}, oC = seqCfg oD₁ C₂ → oE = none →
      ∃ (t₁ t₂ : Trace (Store Loc Val × Store Loc Val)) (a b : Nat),
        RunN a oD₁ t₁ none ∧ RunN b (some C₂) t₂ none ∧ a + b ≤ n ∧
        (rewriting (Store Loc Val)).Refines (t₁ ++ t₂) t := by
  intro n oC t oE h
  induction h with
  | refl oC =>
      intro oD₁ C₂ h₁ h₂
      subst h₂
      cases oD₁ <;> simp [seqCfg] at h₁
  | @cons k m D μ oD ν t' oF hs hr ih =>
      intro oD₁ C₂ h₁ h₂
      subst h₂
      cases oD₁ with
      | none =>
          simp only [seqCfg, Option.some.injEq] at h₁
          subst h₁
          exact ⟨[], (μ, ν) :: t', 0, k + m, RunN.refl none, RunN.cons hs hr, by omega,
            Relation.ReflTransGen.refl⟩
      | some D₁ =>
          simp only [seqCfg, Option.some.injEq] at h₁
          subst h₁
          rcases stepsN_seq_inv hs with ⟨D₁', ν', heq, hstep⟩ | ⟨ρ, a, b, ha, hb, hab⟩
          · simp only [Prod.mk.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            obtain ⟨t₁, t₂, a, b, hr₁, hr₂, hab, href⟩ :=
              ih (oD₁ := some D₁') (C₂ := C₂) rfl rfl
            exact ⟨(μ, ν) :: t₁, t₂, k + a, b, RunN.cons hstep hr₁, hr₂, by omega,
              Rewriting.refines_appendLeft [(μ, ν)] href⟩
          · refine ⟨[(μ, ρ)], (ρ, ν) :: t', a, b + m, ?_, RunN.cons hb hr, by omega, ?_⟩
            · simpa using RunN.cons ha (RunN.refl (none : Option (Com Loc Val)))
            · exact Relation.ReflTransGen.single (SeqCst.Step.mumble μ ρ ν t')

/-- **Counted decomposition of transition traces.**  A counted transition trace
of `C₁ ; C₂` splits into transition traces of `C₁` and of `C₂` whose
concatenation refines it, the two consuming at most as many steps as the whole.

The refinement is genuinely needed: the segment in which `C₁` finishes may
continue straight on into `C₂`, so one pair of `t` corresponds to two pairs of
`t₁ ++ t₂`, recovered by a single mumbling step. -/
theorem runN_seq_inv {n : Nat} {C₁ C₂ : Com Loc Val}
    {t : Trace (Store Loc Val × Store Loc Val)} (h : RunN n (some (Com.seq C₁ C₂)) t none) :
    ∃ (t₁ t₂ : Trace (Store Loc Val × Store Loc Val)) (a b : Nat),
      RunN a (some C₁) t₁ none ∧ RunN b (some C₂) t₂ none ∧ a + b ≤ n ∧
      (rewriting (Store Loc Val)).Refines (t₁ ++ t₂) t :=
  runN_seq_inv_gen h (oD₁ := some C₁) (C₂ := C₂) rfl rfl

/-- **Decomposition of transition traces.**  Every transition trace of `C₁ ; C₂`
is refined from the concatenation of a transition trace of `C₁` with one of
`C₂`. -/
theorem ttrace_seq_inv {C₁ C₂ : Com Loc Val} {t : Trace (Store Loc Val × Store Loc Val)}
    (h : TTrace (Com.seq C₁ C₂) t) :
    ∃ t₁ t₂, TTrace C₁ t₁ ∧ TTrace C₂ t₂ ∧
      (rewriting (Store Loc Val)).Refines (t₁ ++ t₂) t := by
  obtain ⟨n, hn⟩ := Run.exists_runN h
  obtain ⟨t₁, t₂, a, b, h₁, h₂, _, hr⟩ := runN_seq_inv hn
  exact ⟨t₁, t₂, h₁.run, h₂.run, hr⟩

/-! ## Composition of transition traces -/

/-- Composition of runs, in the generalized form the `Run` induction demands:
a run of `oD₁` to `oF` followed by a run of the sequential residual `seqCfg oF C₂`
is a run of `seqCfg oD₁ C₂`. -/
theorem Run.seq_gen : ∀ {oD₁ : Option (Com Loc Val)}
    {t₁ : Trace (Store Loc Val × Store Loc Val)} {oF}, Run oD₁ t₁ oF →
    ∀ {C₂ : Com Loc Val} {t₂ : Trace (Store Loc Val × Store Loc Val)} {oE},
      Run (seqCfg oF C₂) t₂ oE → Run (seqCfg oD₁ C₂) (t₁ ++ t₂) oE := by
  intro oD₁ t₁ oF h
  induction h with
  | refl oC => intro C₂ t₂ oE h₂; exact h₂
  | cons hs _ ih => intro C₂ t₂ oE h₂; exact Run.cons (steps_seq_cong hs C₂) (ih h₂)

/-- **Composition of runs.**  A run of `oD₁` to termination followed by a run of
`C₂` is a run of the sequential residual `seqCfg oD₁ C₂`. -/
theorem Run.seq {oD₁ : Option (Com Loc Val)} {t₁ : Trace (Store Loc Val × Store Loc Val)}
    (h₁ : Run oD₁ t₁ none) {C₂ : Com Loc Val} {t₂ : Trace (Store Loc Val × Store Loc Val)}
    {oE} (h₂ : Run (some C₂) t₂ oE) : Run (seqCfg oD₁ C₂) (t₁ ++ t₂) oE :=
  Run.seq_gen h₁ h₂

/-- **Composition of transition traces.**  Concatenating a transition trace of
`C₁` with one of `C₂` gives a transition trace of `C₁ ; C₂` — no closure step is
needed in this direction. -/
theorem ttrace_seq {C₁ C₂ : Com Loc Val} {t₁ t₂ : Trace (Store Loc Val × Store Loc Val)}
    (h₁ : TTrace C₁ t₁) (h₂ : TTrace C₂ t₂) : TTrace (Com.seq C₁ C₂) (t₁ ++ t₂) :=
  Run.seq h₁ h₂

/-! ## The clause -/

/-- **Brookes, Proposition 6.2, sequential composition:** `T[C₁ ; C₂] = T[C₁] ; T[C₂]`.

`⊇` is `ttrace_seq`, which needs no closure; `⊆` is `ttrace_seq_inv`, whose one
mumbling step is absorbed by the closure in the codomain. -/
theorem opDen_seq (C₁ C₂ : Com Loc Val) :
    opDen (Com.seq C₁ C₂) = (opDen C₁ >>= fun _ ↦ opDen C₂) := by
  apply le_antisymm
  · refine opDen_le_iff.2 fun t ht ↦ ?_
    obtain ⟨t₁, t₂, h₁, h₂, hr⟩ := ttrace_seq_inv ht
    exact (Brookes.mem_bind_iff _ _ _ _).2
      ⟨PUnit.unit, t₁, t₂, mem_opDen h₁ PUnit.unit, mem_opDen h₂ PUnit.unit, hr⟩
  · refine Brookes.le_of_mem fun t x hmem ↦ ?_
    obtain ⟨_, u, v, hu, hv, hr⟩ := (Brookes.mem_bind_iff _ _ _ _).1 hmem
    obtain ⟨u₀, hu₀, hru⟩ := hu
    obtain ⟨v₀, hv₀, hrv⟩ := hv
    exact Brookes.mem_of_refines (mem_opDen (ttrace_seq hu₀ hv₀) x)
      ((Rewriting.refines_append hru hrv).trans hr)

end

end Isotope.Elgot.Brookes.SeqCst.Op
