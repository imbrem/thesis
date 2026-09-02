import Isotope.Elgot.Brookes.SeqCst.FullAbstraction

/-!
# Brookes's separating example, worked out

> "Similarly, consider the commands `x := 0` and `x := 0; x := 0`.  It is easy to
> see that `T[x := 0] ⊆ T[x := 0; x := 0]`, and this inclusion is proper.  The
> trace `([x = 1],[x = 0])([x = 1],[x = 0])` is possible for `x := 0; x := 0` but
> not for `x := 0`.  These two commands can be distinguished by running them in
> parallel with the command `await x = 0 then x := 1`."
> — Brookes, journal p. 152.

This file discharges that example verbatim, at one boolean location, and checks
that the context the general construction produces is the one he names:
`sep [(μ₀, μ₁)]` is `[−] ∥ (await IS_{μ₀} then MAKE_{μ₁}; skip)`, that is,
`[−] ∥ await x = 0 then x := 1`.

Its point is to certify that the full-abstraction theorem is not vacuous: the
denotational order really is strict somewhere, and the separating context really
does separate.
-/

namespace Isotope.Elgot.Brookes

universe u

namespace SeqCst

namespace Example

/-- The state in which `x` is `0`. -/
def μ₀ : Store Unit Bool := fun _ ↦ false

/-- The state in which `x` is `1`. -/
def μ₁ : Store Unit Bool := fun _ ↦ true

theorem μ₁_ne_μ₀ : μ₁ ≠ μ₀ := fun h ↦ by simpa [μ₀, μ₁] using congrFun h ()

/-- `x := 0`. -/
def c0 : Com Unit Bool := .assign () (.const false)

/-- `x := 0; x := 0`. -/
def c00 : Com Unit Bool := .seq c0 c0

/-- Brookes's trace `([x=1],[x=0])([x=1],[x=0])`. -/
def α : Trace (Store Unit Bool × Store Unit Bool) := [(μ₁, μ₀), (μ₁, μ₀)]

/-- Assigning `0` to the only location overwrites the whole state. -/
theorem update_const_false (μ : Store Unit Bool) :
    Function.update μ () ((Exp.const false : Exp Unit Bool).eval μ) = μ₀ := by
  funext v; cases v; simp [Exp.eval, μ₀]

/-- At a one-element location type, `x := 0` denotes the atomic transition to
`μ₀` from anywhere. -/
theorem den_c0 : den c0 = atom fun _ ν ↦ ν = μ₀ := by
  rw [c0, den_assign]
  simp only [update_const_false]

theorem mem_den_c0 (μ : Store Unit Bool) (x : PUnit) : ([(μ, μ₀)], x) ∈ den c0 := by
  rw [den_c0]; exact mem_atom_iff.2 ⟨μ, μ₀, rfl, .refl⟩

/-- A single-pair trace cannot refine to a two-pair trace unless one of the two
pairs is a stutter: the block decomposition leaves one block empty. -/
theorem eq_of_refines_two {S : Type u} {μ ν a b c d : S}
    (h : (rewriting S).Refines [(μ, ν)] [(a, b), (c, d)]) : a = b ∨ c = d := by
  obtain ⟨b₁, t₂, h₁, hc₁, hk₁⟩ := (chunk_iff_refines.2 h).cons_inv rfl
  obtain ⟨b₂, t₃, h₂, hc₂, hk₂⟩ := hk₁.cons_inv rfl
  obtain rfl := hk₂.nil_inv rfl
  rw [h₂, List.append_nil] at h₁
  have hlen : b₁.length + b₂.length = 1 := by
    have := congrArg List.length h₁
    simpa using this.symm
  rcases Nat.eq_zero_or_pos b₁.length with hb | hb
  · obtain rfl := List.eq_nil_of_length_eq_zero hb
    exact Or.inl hc₁.nil_inv
  · have : b₂.length = 0 := by omega
    obtain rfl := List.eq_nil_of_length_eq_zero this
    exact Or.inr hc₂.nil_inv

/-- The trace is possible for `x := 0; x := 0`. -/
theorem mem_α_c00 (x : PUnit) : (α, x) ∈ den c00 := by
  rw [c00, den_seq]
  exact mem_bind _ _ (mem_den_c0 μ₁ PUnit.unit) (mem_den_c0 μ₁ x)

/-- The trace is not possible for `x := 0`. -/
theorem not_mem_α_c0 (x : PUnit) : (α, x) ∉ den c0 := by
  rw [den_c0]
  intro h
  obtain ⟨μ, ν, -, hr⟩ := mem_atom_iff.1 h
  rcases eq_of_refines_two hr with h' | h' <;> exact μ₁_ne_μ₀ h'

/-- `T[x := 0] ⊆ T[x := 0; x := 0]`. -/
theorem den_c0_le_c00 : den c0 ≤ den c00 := by
  apply le_of_mem
  intro t x ht
  rw [den_c0] at ht
  obtain ⟨μ, ν, rfl, hr⟩ := mem_atom_iff.1 ht
  rw [c00, den_seq]
  refine mem_of_refines (mem_bind _ _ (mem_den_c0 μ PUnit.unit) (mem_den_c0 μ₀ x)) ?_
  exact (Relation.ReflTransGen.single (Step.mumble μ μ₀ μ₀ [])).trans hr

/-- The inclusion is proper. -/
theorem den_c00_not_le_c0 : ¬ den c00 ≤ den c0 :=
  fun h ↦ not_mem_α_c0 PUnit.unit (h (mem_α_c00 PUnit.unit))

/-- The interruptions of `α`: `α = zip μ₁ [(μ₀, μ₁)] μ₀`.  So the separating
context the construction produces is
`[−] ∥ (await IS_{μ₀} then MAKE_{μ₁}; skip)` — Brookes's
`[−] ∥ await x = 0 then x := 1`. -/
theorem α_eq_zip : α = zip μ₁ [(μ₀, μ₁)] μ₀ := rfl

/-- The context observes `x := 0; x := 0` at `(μ₁, μ₀)`. -/
theorem obs_sep_c00 : Obs ((sep [(μ₀, μ₁)]).plug c00) μ₁ μ₀ :=
  (obs_sep_iff c00 [(μ₀, μ₁)] μ₁ μ₀).2 (mem_α_c00 PUnit.unit)

/-- The context does not observe `x := 0` at `(μ₁, μ₀)`. -/
theorem not_obs_sep_c0 : ¬ Obs ((sep [(μ₀, μ₁)]).plug c0) μ₁ μ₀ :=
  fun h ↦ not_mem_α_c0 PUnit.unit ((obs_sep_iff c0 [(μ₀, μ₁)] μ₁ μ₀).1 h)

/-- **`x := 0` and `x := 0; x := 0` are contextually distinguishable**, by the
context Brookes names.  In particular the full-abstraction theorem is not
vacuous. -/
theorem not_ctxLe_c00_c0 : ¬ CtxLe c00 c0 :=
  fun h ↦ not_obs_sep_c0 (h (sep [(μ₀, μ₁)]) μ₁ μ₀ obs_sep_c00)

/-- ... and they are not contextually equivalent. -/
theorem not_ctxEq : ¬ CtxEq c0 c00 := fun h ↦ not_ctxLe_c00_c0 h.2

end Example

end SeqCst

end Isotope.Elgot.Brookes
