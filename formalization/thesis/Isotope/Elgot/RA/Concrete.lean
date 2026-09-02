import Isotope.Elgot.RA.Monad

/-!
# The model tower: Null, Generating, Concrete

Dvir, Kammar and Lahav (`release-acquire`) obtain a tower of models by varying
the closure-rule set (journal Table 1, p.29; §7.2–§7.4):

* the **Null model** `N`, at `★ = ∅` (§7.2, p.27);
* the **Generating model** `G`, at `★ = 𝔤 = {Ls, Ex, Cn}` (§7.3, p.30);
* the **Concrete model** `C`, at `★ = 𝔤𝔠 = 𝔤 ∪ 𝔠` (§7.4, p.34) — the ESOP
  version calls this model `M`.

(The **Abstract model** `A`, at `★ = 𝔤𝔠𝔞`, needs the rule group `𝔞`, which is
not formalized; see the honest boundary in `Isotope/Elgot/RA.lean`.)

## What this file establishes

The paper's `G X ⊇ C X ⊇ A X` (journal §8.2, p.41), stated there without
argument, is `closure_mono_rules` of `Isotope/Elgot/RA/Closure.lean` and needs
nothing else.

* `Concrete.pure_bind` and `Concrete.bind_pure`, the two unit laws for the
  Concrete model.  These are half of the paper's Proposition 7.7 ("`C` is a
  monad"; ESOP Proposition 6.6), which is **stated without proof**: the paper's
  only supporting argument anywhere, Example 8.6 (journal p.41), treats
  associativity alone, and no unit law is argued for any model.  So these two
  theorems are **original work, not a port**.  Associativity for `C` is proved
  in `Isotope/Elgot/RA/Assoc.lean`, completing Proposition 7.7.

* `not_bind_pure` — the Null and Generating models are **not** monads, because
  right neutrality fails.  This is the paper's own remark at journal p.30 (ESOP
  p.26): "`(return_N r >>= return_N) ≠ return_N r`, because only the traces from
  the left side of the inequation have two transitions".  The paper gives this
  one sentence; the proof below is ours, and rests on
  `Refines.length_eq`: no `𝔤` rule changes the number of transitions.
-/

universe u

namespace Isotope.Elgot.RA

variable {Loc Val : Type} {A B : Type u}

/-! ## The Concrete model `C` -/

namespace Concrete

/-- **Left Neutrality for the Concrete model `C`** — half of the paper's
Proposition 7.7 (ESOP Proposition 6.6), which is stated without proof.
**Original work.** -/
theorem pure_bind (r : A) (f : A → Comp gcRules Loc Val B) :
    (Pure.pure r : Comp gcRules Loc Val A) >>= f = f r :=
  Comp.left_neutrality cRules_subset_gcRules gcRules_subset_gcTiAbRules r f

/-- **Right Neutrality for the Concrete model `C`** — the other half of the
paper's Proposition 7.7 (ESOP Proposition 6.6).  **Original work.** -/
theorem bind_pure (P : Comp gcRules Loc Val A) : P >>= Pure.pure = P :=
  Comp.right_neutrality cRules_subset_gcRules gcRules_subset_gcTiAbRules P

end Concrete

/-! ## Neither the Null model nor the Generating model is a monad

Journal p.30 (ESOP p.26).  We reproduce the paper's counterexample: binding
`return r` with `return` doubles the number of transitions, and no rule of `𝔤`
can undo that. -/

/-- Every trace in the `𝔤`-closure of `return r` has a one-transition
chronicle. -/
theorem length_of_mem_closure_pureGen {R : RuleSet} (hR : R ⊆ gRules) (r : A)
    {τ : PreTrace Loc Val A} (h : τ ∈ closure R (pureGen r)) :
    τ.ch.toList.length = 1 := by
  obtain ⟨τ₀, hτ₀, hr⟩ := h
  obtain ⟨κ, μ, -, -, rfl⟩ := hτ₀
  rw [← hr.length_eq hR]
  simp

/-- **The Null and Generating models are not monads**: right neutrality fails
for every `R ⊆ 𝔤`.  This is the paper's remark at journal p.30 ("only the
traces from the left side of the inequation have two transitions"), which it
states in one sentence and does not prove. -/
theorem not_bind_pure {R : RuleSet} (hR : R ⊆ gRules) [Finite Loc] [Nonempty Loc]
    (v₀ : Val) (t₀ : ℚ) (r : A) :
    ((Pure.pure r : Comp R Loc Val A) >>= Pure.pure) ≠ Pure.pure r := by
  intro hEq
  set κ : View Loc := fun _ ↦ t₀ with hκ
  set μ : Memory Loc Val := initialMem v₀ t₀ with hμ
  set τ : PreTrace Loc Val A := ⟨κ, Chro.single ⟨μ, μ⟩, κ, r⟩ with hτdef
  have hτ : τ ∈ pureGen (Loc := Loc) (Val := Val) r :=
    ⟨κ, μ, initialMem_wellFormed v₀ t₀, pointsDownInto_initialMem v₀ t₀, rfl⟩
  have hseam : τ.ch.c ⊆ τ.ch.o := by rw [hτdef]; simp
  have hmem : τ.seam τ hseam ∈ ((Pure.pure r : Comp R Loc Val A) >>= Pure.pure).traces := by
    refine subset_closure ⟨τ, τ, hseam, subset_closure hτ, ?_, le_refl _, rfl⟩
    exact subset_closure (show τ ∈ pureGen τ.ret from hτ)
  rw [hEq] at hmem
  have h1 : (τ.seam τ hseam).ch.toList.length = 1 :=
    length_of_mem_closure_pureGen hR r hmem
  have h2 : (τ.seam τ hseam).ch.toList.length = 2 := by
    rw [PreTrace.seam_ch, Chro.append_toList, List.length_append, hτdef]
    simp
  omega

end Isotope.Elgot.RA
