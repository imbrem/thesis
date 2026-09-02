import Isotope.Elgot.RA.Exchange
import Isotope.Elgot.RA.Examples

/-!
# A worked parallel composition

`Isotope/Elgot/RA/Bounds.lean` characterises the paper's `inf_μ` rather than
constructing it, so `parGen` carries an `IsInfMem` hypothesis and a parallel
composition is not *a priori* known to be non-empty.  This file supplies a
concrete witness at the smallest interesting instance: two `return`s run in
parallel, over the paper's initial memory.  Both threads start from the same
view, so `inf_{ξ.o}{κ,κ} = κ` by `isInfMem_pair_self` and no existence theorem
is needed.

Together with `Comp.seqPair_le_par` — which shows that a parallel composition
contains the whole sequential pairing — this is the evidence that `Comp.par` is
not vacuous.

Nothing here is in the paper: its own litmus examples (SB, MP at Example 5.3
p.19; SB+F at §2.4 p.8) are stated *operationally* and it never carries out the
corresponding denotational calculation, remarking only that impossible outcomes
"can be shown indirectly by calculating its denotation" (p.42).
-/

universe u

namespace Isotope.Elgot.RA

open Isotope.Elgot (Interleave)

variable {Loc Val : Type} {A B : Type u}

/-- The two-transition chronicle `⟨μ,μ⟩⟨μ,μ⟩`: one stutter contributed by each
of two parallel `return`s. -/
def stutterPair (μ : Memory Loc Val) : Chro Loc Val where
  first := ⟨μ, μ⟩
  rest := [⟨μ, μ⟩]
  chain := List.isChain_cons_cons.mpr ⟨subset_refl _, List.isChain_singleton _⟩

@[simp] theorem stutterPair_toList (μ : Memory Loc Val) :
    (stutterPair (Val := Val) μ).toList = [⟨μ, μ⟩, ⟨μ, μ⟩] := rfl

@[simp] theorem stutterPair_o (μ : Memory Loc Val) :
    (stutterPair (Val := Val) μ).o = μ := rfl

/-- `return a ||| return b` is non-empty: it contains the trace whose chronicle
is one stutter per thread over the paper's initial memory, and whose returned
value is the pair. -/
theorem par_pure_pure_nonempty [Finite Loc] [Nonempty Loc] (v₀ : Val) (t₀ : ℚ)
    (a : A) (b : B) :
    (⟨(fun _ ↦ t₀ : View Loc), stutterPair (initialMem (Loc := Loc) v₀ t₀),
      (fun _ ↦ t₀), (a, b)⟩ : PreTrace Loc Val (A × B))
      ∈ ((pure a : Comp cRules Loc Val A).par (pure b : Comp cRules Loc Val B)).traces := by
  refine subset_closure (parGen_mono subset_closure subset_closure ?_)
  refine ⟨⟨_, Chro.single ⟨initialMem v₀ t₀, initialMem v₀ t₀⟩, _, a⟩,
    ⟨_, _, initialMem_wellFormed v₀ t₀, pointsDownInto_initialMem v₀ t₀, rfl⟩,
    ⟨_, Chro.single ⟨initialMem v₀ t₀, initialMem v₀ t₀⟩, _, b⟩,
    ⟨_, _, initialMem_wellFormed v₀ t₀, pointsDownInto_initialMem v₀ t₀, rfl⟩, ?_, ?_, ?_, rfl⟩
  · exact Interleave.left (Interleave.right Interleave.nil)
  · exact isInfMem_pair_self (pointsDownInto_initialMem v₀ t₀)
  · exact (sup_idem _).symm

/-- Hence a parallel composition of two `return`s is not the empty
computation. -/
theorem par_pure_pure_ne_bot [Finite Loc] [Nonempty Loc] (v₀ : Val) (t₀ : ℚ)
    (a : A) (b : B) :
    (pure a : Comp cRules Loc Val A).par (pure b : Comp cRules Loc Val B) ≠ ⊥ := by
  intro h
  have := par_pure_pure_nonempty (Loc := Loc) (Val := Val) v₀ t₀ a b
  rw [h] at this
  exact absurd this (by simp)

/-- The two threads' local messages are disjoint, vacuously here: neither
`return` contributes any. -/
theorem par_pure_pure_own [Finite Loc] [Nonempty Loc] (v₀ : Val) (t₀ : ℚ) :
    (stutterPair (initialMem (Loc := Loc) (Val := Val) v₀ t₀)).own = ∅ := by
  ext ν
  simp [Chro.own, listOwn, Transition.own]

end Isotope.Elgot.RA
