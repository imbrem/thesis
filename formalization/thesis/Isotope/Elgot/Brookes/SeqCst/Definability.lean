import Isotope.Elgot.Brookes.SeqCst.Context
import Mathlib.Data.Fintype.Basic

/-!
# Definability: Brookes's separating contexts

This file builds Brookes's gadgets (journal p. 151) and proves the exact
characterisation of what they observe.

* `IS a` — the boolean expression true exactly at the state `a`.  Brookes:
  *"Since states are finite, for each state `s` there is a boolean expression
  `IS_s` that evaluates to `tt` from `s'` if `s'` agrees with `s` on `dom(s)`,
  and evaluates to `ff` otherwise."*  Ours is the finite conjunction of
  equations `ℓ = a ℓ`, one per location, which is exactly the form he assumes
  his condition language contains (journal p. 148).
* `MAKE v` — the command driving any state to `v`.  Brookes: *"a finite sequence
  of assignments to the identifiers in `dom(s)`."*  Ours assigns every location.
* `awaitStep a b = await IS_a then MAKE_b`, whose denotation is the atomic
  transition `a ↦ b`.
* `DO u` — the sequence of those, for `u = ᾱ`.  Brookes's `DO_α`.
* `sep u = [−] ∥ DO u` — his `P_α[−]`.

The theorem of the file is `obs_sep_iff`:

```
Obs ((sep u).plug C) s s'  ↔  zip s u s' ∈ T[C]
```

that is, the context `[−] ∥ DO u` observes `(s, s')` of `C` **exactly when** `C`
has the transition trace whose interruptions are `u`.  Brookes proves the two
directions separately for the particular `α` at hand; the `↔` is ours, and its
right-to-left direction is his positive argument (alternating shuffle, then
mumble) while its left-to-right direction is his negative one, discharged by
`refines_zip_of_interleave`.
-/

namespace Isotope.Elgot.Brookes

universe u

namespace SeqCst

variable {Loc Val : Type u}

/-! ## Every nonempty trace is a `zip` -/

/-- Every nonempty trace arises as `zip s u s'`: `s` is its first rely, `s'` its
last guarantee, and `u` its interruptions.  This is the inverse of Brookes's
`α ↦ ᾱ`, and is what turns `obs_sep_iff` into a completeness proof. -/
theorem exists_zip : ∀ {t : Trace (Store Loc Val × Store Loc Val)}, t ≠ [] →
    ∃ (s : Store Loc Val) (v : Trace (Store Loc Val × Store Loc Val)) (s' : Store Loc Val),
      t = zip s v s'
  | [], h => absurd rfl h
  | [(x, y)], _ => ⟨x, [], y, rfl⟩
  | (x, y) :: p :: t, _ => by
      obtain ⟨m, v, s', hv⟩ := exists_zip (t := p :: t) (by simp)
      exact ⟨x, (y, m) :: v, s', by rw [zip_cons, ← hv]⟩

/-! ## `IS`: a boolean expression naming a state -/

/-- The equation `ℓ = a ℓ`. -/
def eqLoc (a : Store Loc Val) (ℓ : Loc) : BExp Loc Val := .eq (.var ℓ) (.const (a ℓ))

/-- Finite conjunction of boolean expressions. -/
def conj : List (BExp Loc Val) → BExp Loc Val
  | [] => .tt
  | b :: bs => .and b (conj bs)

theorem eval_conj [DecidableEq Val] (bs : List (BExp Loc Val)) (μ : Store Loc Val) :
    (conj bs).eval μ = true ↔ ∀ b ∈ bs, b.eval μ = true := by
  induction bs with
  | nil => simp [conj, BExp.eval]
  | cons b bs ih => simp [conj, BExp.eval, Bool.and_eq_true, ih]

/-- `IS a`: **Brookes's `IS_s`**, the boolean expression true exactly at `a`. -/
noncomputable def IS [Fintype Loc] (a : Store Loc Val) : BExp Loc Val :=
  conj (((Finset.univ : Finset Loc).toList).map (eqLoc a))

theorem eval_IS [Fintype Loc] [DecidableEq Val] (a μ : Store Loc Val) :
    (IS a).eval μ = true ↔ μ = a := by
  rw [IS, eval_conj]
  constructor
  · intro h
    funext ℓ
    have hb := h (eqLoc a ℓ) (List.mem_map.2 ⟨ℓ, Finset.mem_toList.2 (Finset.mem_univ ℓ), rfl⟩)
    simpa [eqLoc, BExp.eval, Exp.eval] using hb
  · rintro rfl b hb
    obtain ⟨ℓ, _, rfl⟩ := List.mem_map.1 hb
    simp [eqLoc, BExp.eval, Exp.eval]

/-! ## `MAKE`: a command driving the state to a fixed value -/

/-- Overwrite a list of locations with their values in `v`. -/
def updateList [DecidableEq Loc] (v : Store Loc Val) :
    List Loc → Store Loc Val → Store Loc Val
  | [], μ => μ
  | ℓ :: L, μ => updateList v L (Function.update μ ℓ (v ℓ))

theorem updateList_apply [DecidableEq Loc] (v : Store Loc Val) (L : List Loc)
    (μ : Store Loc Val) (ℓ : Loc) :
    updateList v L μ ℓ = if ℓ ∈ L then v ℓ else μ ℓ := by
  induction L generalizing μ with
  | nil => simp [updateList]
  | cons ℓ' L ih =>
      rw [updateList, ih]
      by_cases hL : ℓ ∈ L
      · simp [hL]
      · by_cases h' : ℓ = ℓ'
        · subst h'; simp [hL]
        · simp [hL, h']

theorem updateList_univ [Fintype Loc] [DecidableEq Loc] (v μ : Store Loc Val) :
    updateList v ((Finset.univ : Finset Loc).toList) μ = v := by
  funext ℓ
  rw [updateList_apply]
  simp

/-- The command assigning `v ℓ` to each `ℓ` of a list, in order. -/
def makeFrom [DecidableEq Loc] (v : Store Loc Val) : List Loc → Com Loc Val
  | [] => .skip
  | ℓ :: L => .seq (.assign ℓ (.const (v ℓ))) (makeFrom v L)

/-- `MAKE v`: **Brookes's `MAKE_s`**, a finite sequence of assignments driving
any state to `v`. -/
noncomputable def MAKE [Fintype Loc] [DecidableEq Loc] (v : Store Loc Val) : Com Loc Val :=
  makeFrom v ((Finset.univ : Finset Loc).toList)

theorem obs_makeFrom [DecidableEq Loc] [DecidableEq Val] (v : Store Loc Val) (L : List Loc)
    (μ ν : Store Loc Val) : obs (den (makeFrom v L)) μ ν ↔ ν = updateList v L μ := by
  induction L generalizing μ with
  | nil => simp [makeFrom, updateList, obs_test]
  | cons ℓ L ih =>
      rw [makeFrom, den_seq, obs_bind, updateList]
      constructor
      · rintro ⟨ρ, hρ, hν⟩
        rw [den_assign, obs_atom] at hρ
        rw [ih] at hν
        rw [hν, hρ]
        rfl
      · intro hν
        exact ⟨Function.update μ ℓ (v ℓ), by rw [den_assign, obs_atom]; rfl, (ih _).2 hν⟩

theorem obs_MAKE [Fintype Loc] [DecidableEq Loc] [DecidableEq Val] (v μ ν : Store Loc Val) :
    obs (den (MAKE v)) μ ν ↔ ν = v := by
  rw [MAKE, obs_makeFrom, updateList_univ]

/-! ## `awaitStep` and `DO` -/

variable [Fintype Loc] [DecidableEq Loc] [DecidableEq Val]

/-- `awaitStep a b = await IS_a then MAKE_b`: the atomic transition `a ↦ b`. -/
noncomputable def awaitStep (a b : Store Loc Val) : Com Loc Val := .await (IS a) (MAKE b)

/-- The denotation of `awaitStep a b` is exactly the closure of the single trace
`[(a, b)]`. -/
theorem den_awaitStep (a b : Store Loc Val) :
    den (awaitStep a b) = atom fun μ ν ↦ μ = a ∧ ν = b := by
  rw [awaitStep, den_await]
  congr 1
  funext μ ν
  exact propext (by rw [eval_IS, obs_MAKE])

/-- **Brookes's `DO_α`**: the sequence of conditional critical regions realising
the interruptions `u = ᾱ`. -/
noncomputable def DO : Trace (Store Loc Val × Store Loc Val) → Com Loc Val
  | [] => .skip
  | (a, b) :: u => .seq (awaitStep a b) (DO u)

/-- Every trace of `DO u` is a refinement of `u`: `T[DO_α] ⊆ {ᾱ}†`. -/
theorem den_DO_refines (u : Trace (Store Loc Val × Store Loc Val))
    {t : Trace (Store Loc Val × Store Loc Val)} {x : PUnit} (h : (t, x) ∈ den (DO u)) :
    (rewriting (Store Loc Val)).Refines u t := by
  induction u generalizing t with
  | nil =>
      rw [DO, den_skip, test] at h
      obtain ⟨μ, ν, ⟨-, rfl⟩, hr⟩ := mem_atom_iff.1 h
      exact (Relation.ReflTransGen.single (Step.stutter ν [])).trans hr
  | cons p u ih =>
      obtain ⟨a, b⟩ := p
      rw [DO, den_seq] at h
      obtain ⟨y, u₁, v, hu₁, hv, hr⟩ := (mem_bind_iff _ _ _ _).1 h
      rw [den_awaitStep] at hu₁
      obtain ⟨μ, ν, ⟨rfl, rfl⟩, hr₁⟩ := mem_atom_iff.1 hu₁
      exact (Rewriting.refines_append hr₁ (ih hv)).trans hr

/-- `u` extended by one final stutter is a trace of `DO u`.  The stutter comes
from the trailing `skip`; it is needed because command denotations are `ε`-free,
so `DO []` denotes the nonempty stutters rather than `{ε}†`. -/
theorem mem_den_DO (u : Trace (Store Loc Val × Store Loc Val)) (s' : Store Loc Val)
    (x : PUnit) : (u ++ [(s', s')], x) ∈ den (DO u) := by
  induction u with
  | nil =>
      rw [DO, den_skip, test]
      exact mem_atom_iff.2 ⟨s', s', ⟨rfl, rfl⟩, .refl⟩
  | cons p u ih =>
      obtain ⟨a, b⟩ := p
      rw [DO, den_seq]
      have h₁ : ([(a, b)], PUnit.unit) ∈ den (awaitStep a b) := by
        rw [den_awaitStep]; exact mem_atom_iff.2 ⟨a, b, ⟨rfl, rfl⟩, .refl⟩
      have h₂ := mem_bind (den (awaitStep a b)) (fun _ ↦ den (DO u)) h₁ ih
      exact h₂

/-! ## The separating context -/

/-- **Brookes's `P_α[−] = [−] ∥ DO_α`.** -/
noncomputable def sep (u : Trace (Store Loc Val × Store Loc Val)) : Ctx Loc Val :=
  .parL .hole (DO u)

/-- **The separating-context theorem.**  Running `C` against `DO u` and
observing the pair `(s, s')` is possible **exactly when** `C` has the transition
trace whose interruptions are `u`.

Right-to-left is Brookes's positive argument: shuffle `α` with `ᾱ` alternately
to get an interference-free trace, then mumble it down to `(s₀, s_k')`.
Left-to-right is his negative argument, whose combinatorial content is
`refines_zip_of_interleave`. -/
theorem obs_sep_iff (C : Com Loc Val) (u : Trace (Store Loc Val × Store Loc Val))
    (s s' : Store Loc Val) :
    Obs ((sep u).plug C) s s' ↔ (zip s u s', PUnit.unit) ∈ den C := by
  rw [Obs, sep, Ctx.plug, Ctx.plug, den_par, obs]
  constructor
  · intro h
    obtain ⟨p, -, hp⟩ := mem_map_iff.1 h
    obtain ⟨w₀, t, β, ht, hβ, hi, hr⟩ := mem_par_iff'.1 hp
    exact mem_of_refines ht (refines_zip_of_interleave hi (den_DO_refines u hβ) hr)
  · intro h
    refine mem_map_iff.2 ⟨(PUnit.unit, PUnit.unit), rfl, ?_⟩
    have hi : Interleave (zip s u s') (u ++ [(s', s')]) (merge s u s' ++ [(s', s')]) := by
      have := (interleave_zip_merge s u s').appendCompat
        (Interleave.nil_left [(s', s')])
      rwa [List.append_nil] at this
    have hc : Chain s (merge s u s' ++ [(s', s')]) s' :=
      (chain_merge s u s').append (.cons s' s' (.nil s'))
    exact mem_of_refines (mem_par h (mem_den_DO u s' PUnit.unit) hi)
      (chain_iff_refines_single.1 hc)

end SeqCst

end Isotope.Elgot.Brookes
