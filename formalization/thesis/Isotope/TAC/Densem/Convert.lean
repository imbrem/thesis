import Isotope.TAC.Classical.Convert
import Isotope.TAC.Densem.Phi

/-! # Executable correctness of classical SSA conversion -/

namespace Isotope.TAC.Densem.Convert

open Isotope.TAC.Classical
open Isotope.TAC.Classical.Convert
open Isotope.TAC.Densem.Classical.Executable

universe u v w q

/-- A version environment names, in the target store, the current value of
each source variable. -/
def EnvRel (current : Isotope.TAC.Classical.Convert.Env ν κ) (source : Densem.Env M ν)
    (target : Densem.Env M (Version ν κ)) : Prop :=
  ∀ x, target (current x) = source x

/-- Environment agreement restricted to variables relevant to the next
program point. -/
def EnvRelOn (needed : List ν) (current : Isotope.TAC.Classical.Convert.Env ν κ)
    (source : Densem.Env M ν) (target : Densem.Env M (Version ν κ)) : Prop :=
  ∀ x ∈ needed, target (current x) = source x

def Coverage (vars : List ν) (source : Isotope.TAC.Classical.CFG ν φ κ) : Prop :=
  (∀ x ∈ blockSourceVars source.entry, x ∈ vars) ∧
    ∀ p ∈ source.blocks, ∀ x ∈ blockSourceVars p.2, x ∈ vars

theorem sourceVars_coverage [DecidableEq ν]
    (source : Isotope.TAC.Classical.CFG ν φ κ) :
    Coverage (sourceVars source) source := by
  constructor
  · intro x hx
    exact (mem_sourceVars source x).2 (.inl hx)
  · intro p hp x hx
    exact (mem_sourceVars source x).2 (.inr ⟨p, hp, hx⟩)

theorem EnvRel.on
    {current : Isotope.TAC.Classical.Convert.Env ν κ}
    {source : Densem.Env M ν} {target : Densem.Env M (Version ν κ)}
    (h : EnvRel current source target) (needed : List ν) :
    EnvRelOn needed current source target := by
  intro x _
  exact h x

theorem value_sim (M : Densem.Model φ) (current : Isotope.TAC.Classical.Convert.Env ν κ)
    (source : Densem.Env M ν) (target : Densem.Env M (Version ν κ))
    (h : EnvRel current source target) (a : Isotope.TAC.Classical.Value ν) :
    valueDenote M target (renameValue current a) =
      valueDenote M source a := by
  induction a with
  | var x => exact h x
  | unit => rfl
  | pair l r il ir => simp [renameValue, valueDenote, il, ir]

theorem operand_sim (M : Densem.Model φ) (current : Isotope.TAC.Classical.Convert.Env ν κ)
    (source : Densem.Env M ν) (target : Densem.Env M (Version ν κ))
    (h : EnvRel current source target) (a : Isotope.TAC.Classical.Operand ν φ) :
    operandDenote M target (renameOperand current a) =
      operandDenote M source a := by
  cases a <;> simp [renameOperand, operandDenote, value_sim M current source target h]

theorem terminator_sim (M : Densem.Model φ) (current : Isotope.TAC.Classical.Convert.Env ν κ)
    (source : Densem.Env M ν) (target : Densem.Env M (Version ν κ))
    (h : EnvRel current source target) (t : Isotope.TAC.Classical.Terminator ν φ κ) :
    terminatorDenote M target (renameTerminator current t) =
      terminatorDenote M source t := by
  induction t with
  | br => rfl
  | ret => simp [renameTerminator, terminatorDenote,
      value_sim M current source target h]
  | cond c l r il ir =>
      simp [renameTerminator, terminatorDenote,
        operand_sim M current source target h, il, ir]

theorem envRel_update [DecidableEq ν] [DecidableEq κ]
    (current : Isotope.TAC.Classical.Convert.Env ν κ)
    (source : Densem.Env M ν) (target : Densem.Env M (Version ν κ))
    (h : EnvRel current source target) (x : ν) (vx : Version ν κ) (a : M.Val) :
    (∀ y, y ≠ x → current y ≠ vx) →
    EnvRel (update current x vx) (Densem.Env.set source x a)
      (Densem.Env.set target vx a) := by
  intro hfresh
  intro y
  by_cases e : y = x
  · subst y; simp [update, Densem.Env.set]
  · simp only [update, Densem.Env.set, e, if_false, hfresh y e]
    exact h y

/-- The local freshness condition needed by the semantic simulation. It states
exactly that each syntax-generated destination is absent from the reaching
version environment before it is installed. -/
def FreshFor [DecidableEq ν] (bid : BlockId κ) :
    Nat → Isotope.TAC.Classical.Convert.Env ν κ →
      List (Instr ν φ) → Prop
  | _, _, [] => True
  | i, current, .assign x _ :: rest =>
      let dst := Version.instr bid i 0 x
      (∀ y, y ≠ x → current y ≠ dst) ∧
        FreshFor bid (i + 1) (update current x dst) rest
  | i, current, .assignPair x y _ :: rest =>
      let dx := Version.instr bid i 0 x
      let dy := Version.instr bid i 1 y
      (∀ z, z ≠ x → current z ≠ dx) ∧
      (∀ z, z ≠ y → update current x dx z ≠ dy) ∧
        FreshFor bid (i + 1) (update (update current x dx) y dy) rest

/-- Straight-line conversion simulates every successful source execution and
returns stores related by the compiler's final reaching environment. -/
theorem body_sim [DecidableEq ν] [DecidableEq κ]
    (M : Densem.Model φ) (bid : BlockId κ) (i : Nat)
    (current : Isotope.TAC.Classical.Convert.Env ν κ)
    (xs : List (Instr ν φ)) (t : Isotope.TAC.Classical.Terminator ν φ κ)
    (source source' : Densem.Env M ν)
    (target : Densem.Env M (Version ν κ)) (exit : Densem.Exit κ M.Val)
    (hrel : EnvRel current source target) (hfresh : FreshFor bid i current xs)
    (hsource : bodyDenote M xs source t = some (source', exit)) :
    ∃ target',
      bodyDenote M (body bid i current xs).1 target
          (renameTerminator (body bid i current xs).2 t) = some (target', exit) ∧
        EnvRel (body bid i current xs).2 source' target' := by
  induction xs generalizing i current source target with
  | nil =>
      simp only [bodyDenote, body] at hsource ⊢
      rw [terminator_sim M current source target hrel]
      cases ht : terminatorDenote M source t with
      | none => simp [ht] at hsource
      | some e =>
        simp only [ht, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsource
        rcases hsource with ⟨rfl, rfl⟩
        exact ⟨target, by simp [ht], hrel⟩
  | cons instr rest ih =>
      cases instr with
      | assign x rhs =>
          simp only [bodyDenote] at hsource
          cases hv : operandDenote M source rhs with
          | none => simp [hv] at hsource
          | some a =>
              simp only [hv, Option.bind_some] at hsource
              rcases hfresh with ⟨hdst, hrest⟩
              have hop := operand_sim M current source target hrel rhs
              simp only [body, bodyDenote]
              rw [hop, hv]
              exact ih (i + 1) (update current x (Version.instr bid i 0 x))
                (Densem.Env.set source x a)
                (Densem.Env.set target (Version.instr bid i 0 x) a)
                (envRel_update current source target hrel x _ a hdst) hrest hsource
      | assignPair x y rhs =>
          simp only [bodyDenote] at hsource
          cases hv : operandDenote M source rhs with
          | none => simp [hv] at hsource
          | some a =>
            cases hp : M.split a with
            | none => simp [hv, hp] at hsource
            | some p =>
              rcases p with ⟨ax, ay⟩
              simp [hv, hp] at hsource
              rcases hfresh with ⟨hdx, hdy, hrest⟩
              have hop := operand_sim M current source target hrel rhs
              simp only [body, bodyDenote]
              rw [hop, hv]
              simp [hp]
              have hx := envRel_update current source target hrel x
                (Version.instr bid i 0 x) ax hdx
              have hxy := envRel_update
                (update current x (Version.instr bid i 0 x))
                (Densem.Env.set source x ax)
                (Densem.Env.set target (Version.instr bid i 0 x) ax)
                hx y (Version.instr bid i 1 y) ay hdy
              exact ih (i + 1)
                (update (update current x (Version.instr bid i 0 x)) y
                  (Version.instr bid i 1 y))
                ((Densem.Env.set source x ax).set y ay)
                ((Densem.Env.set target (Version.instr bid i 0 x) ax).set
                  (Version.instr bid i 1 y) ay) hxy hrest hsource

end Isotope.TAC.Densem.Convert
