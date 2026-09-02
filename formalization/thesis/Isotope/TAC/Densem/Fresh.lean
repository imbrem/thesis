import Isotope.TAC.Densem.Convert

/-! # Freshness of canonical SSA versions

The syntax-directed converter tags every instruction definition with its block
and position.  This file discharges the local freshness premise used by the
straight-line semantic simulation without assuming an infinite name supply.
-/

namespace Isotope.TAC.Densem.Convert

open Isotope.TAC.Classical
open Isotope.TAC.Classical.Convert

universe u v w

/-- Every instruction version currently reachable at program point `i` in
`bid` was produced at an earlier instruction of that block.  Versions from
other blocks and incoming external/phi versions are unconstrained. -/
def Before (bid : BlockId κ) (i : Nat)
    (current : Isotope.TAC.Classical.Convert.Env ν κ) : Prop :=
  ∀ x b j slot source, current x = Version.instr b j slot source →
    b ≠ bid ∨ j < i

theorem before_startEnv (ν : Type u) (bid : BlockId κ) :
    Before bid 0 (startEnv (Var := ν) bid) := by
  intro x b j slot source h
  cases bid <;> simp [startEnv] at h

theorem Before.insert [DecidableEq ν]
    {bid : BlockId κ} {i tagIndex : Nat}
    {current : Isotope.TAC.Classical.Convert.Env ν κ}
    (h : Before bid i current) (x : ν) (slot : Nat) (hj : tagIndex < i) :
    Before bid i (update current x (Version.instr bid tagIndex slot x)) := by
  intro y b k s source hy
  by_cases e : y = x
  · subst y
    simp [update] at hy
    rcases hy with ⟨rfl, rfl, rfl, rfl⟩
    exact Or.inr hj
  · simp [update, e] at hy
    rcases h y b k s source hy with hb | hk
    · exact Or.inl hb
    · exact Or.inr hk

theorem Before.mono {bid : BlockId κ} {i j : Nat}
    {current : Isotope.TAC.Classical.Convert.Env ν κ}
    (h : Before bid i current) (hij : i ≤ j) : Before bid j current := by
  intro x b k slot source heq
  rcases h x b k slot source heq with hb | hk
  · exact Or.inl hb
  · exact Or.inr (Nat.lt_of_lt_of_le hk hij)

theorem Before.fresh [DecidableEq ν]
    {bid : BlockId κ} {i slot : Nat}
    {current : Isotope.TAC.Classical.Convert.Env ν κ}
    (h : Before bid i current) (x : ν) :
    ∀ y, y ≠ x → current y ≠ Version.instr bid i slot x := by
  intro y _ heq
  rcases h y bid i slot x heq with hbid | hi
  · exact hbid rfl
  · exact (Nat.lt_irrefl i) hi

theorem freshFor_of_before [DecidableEq ν]
    (bid : BlockId κ) (i : Nat)
    (current : Isotope.TAC.Classical.Convert.Env ν κ)
    (xs : List (Instr ν φ)) (h : Before bid i current) :
    FreshFor bid i current xs := by
  induction xs generalizing i current with
  | nil => trivial
  | cons hd rest ih =>
      cases hd with
      | assign x rhs =>
          have hs : Before bid (i + 1) current := h.mono (Nat.le_succ i)
          have hu := hs.insert x 0 (Nat.lt_succ_self i)
          exact ⟨h.fresh x, ih (i := i + 1)
            (current := update current x (Version.instr bid i 0 x))
            hu⟩
      | assignPair x y rhs =>
          have hx := h.fresh (slot := 0) x
          have hs : Before bid (i + 1) current := h.mono (Nat.le_succ i)
          have h1 := hs.insert x 0 (Nat.lt_succ_self i)
          have hy : ∀ z, z ≠ y →
              update current x (Version.instr bid i 0 x) z ≠
                Version.instr bid i 1 y := by
            intro z hz heq
            by_cases ezx : z = x
            · subst z
              simp [update] at heq
            · simp [update, ezx] at heq
              exact h.fresh (slot := 1) y z hz heq
          have h2 := h1.insert y 1 (Nat.lt_succ_self i)
          exact ⟨hx, hy, ih (i := i + 1)
            (current := update (update current x (Version.instr bid i 0 x)) y
              (Version.instr bid i 1 y)) h2⟩

/-- Canonical conversion is fresh in every source block. -/
theorem freshFor_startEnv [DecidableEq ν]
    (bid : BlockId κ) (xs : List (Instr ν φ)) :
    FreshFor bid 0 (startEnv bid) xs :=
  freshFor_of_before bid 0 (startEnv bid) xs (before_startEnv ν bid)

end Isotope.TAC.Densem.Convert
