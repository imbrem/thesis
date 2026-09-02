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

end Isotope.TAC.Densem.Convert
