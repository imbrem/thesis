import Isotope.TAC.Densem.Convert

/-! # Local monadic correctness of canonical TAC-to-SSA renaming

These lemmas are the effectful counterpart of the executable simulations in
`Densem.Convert`.  They deliberately stop at control-flow iteration: the
whole-CFG theorem additionally has to package the invariant that every
reachable converted store represents a total source store.
-/

namespace Isotope.TAC.Densem.Convert.Monadic

open Isotope.TAC.Classical
open Isotope.TAC.Classical.Convert

universe u v

variable {ν : Type u} {κ : Type} {φ : Type v} {m : Type → Type}
variable (M : Isotope.TAC.Densem.Monadic.Model φ m)

abbrev MEnv := Isotope.TAC.Densem.Monadic.Env M

/-- A converted store represents a source store through the reaching-version
environment at the current program point. -/
def EnvRel (current : Isotope.TAC.Classical.Convert.Env ν κ)
    (source : MEnv M ν) (target : MEnv M (Version ν κ)) : Prop :=
  ∀ x, target (current x) = source x

theorem value_denote [Monad m] [LawfulMonad m]
    (current : Isotope.TAC.Classical.Convert.Env ν κ)
    (source : MEnv M ν) (target : MEnv M (Version ν κ))
    (hrel : EnvRel (M := M) current source target)
    (a : Isotope.TAC.Classical.Value ν) :
    Isotope.TAC.Densem.Monadic.Value.denote M target
        (Isotope.TAC.Densem.Classical.value (renameValue current a)) =
      Isotope.TAC.Densem.Monadic.Value.denote M source
        (Isotope.TAC.Densem.Classical.value a) := by
  induction a with
  | var x =>
      simp only [renameValue, Isotope.TAC.Densem.Classical.value,
        Isotope.TAC.Densem.Monadic.Value.denote]
      rw [hrel x]
  | unit => rfl
  | pair left right ihl ihr =>
      simp only [renameValue, Isotope.TAC.Densem.Classical.value,
        Isotope.TAC.Densem.Monadic.Value.denote]
      rw [ihl, ihr]

theorem operand_denote [Monad m] [LawfulMonad m]
    (current : Isotope.TAC.Classical.Convert.Env ν κ)
    (source : MEnv M ν) (target : MEnv M (Version ν κ))
    (hrel : EnvRel (M := M) current source target)
    (a : Isotope.TAC.Classical.Operand ν φ) :
    Isotope.TAC.Densem.Monadic.Operand.denote M target
        (Isotope.TAC.Densem.Classical.operand (renameOperand current a)) =
      Isotope.TAC.Densem.Monadic.Operand.denote M source
        (Isotope.TAC.Densem.Classical.operand a) := by
  cases a <;>
    simp only [renameOperand, Isotope.TAC.Densem.Classical.operand,
      Isotope.TAC.Densem.Monadic.Operand.denote] <;>
    rw [value_denote M current source target hrel]

theorem terminator_denote [Monad m] [LawfulMonad m]
    (current : Isotope.TAC.Classical.Convert.Env ν κ)
    (source : MEnv M ν) (target : MEnv M (Version ν κ))
    (hrel : EnvRel (M := M) current source target)
    (t : Isotope.TAC.Classical.Terminator ν φ κ) :
    Isotope.TAC.Densem.Monadic.Terminator.denote M target
        (Isotope.TAC.Densem.Classical.terminator (renameTerminator current t)) =
      Isotope.TAC.Densem.Monadic.Terminator.denote M source
        (Isotope.TAC.Densem.Classical.terminator (κ := κ) t) := by
  induction t with
  | br => rfl
  | ret a =>
      simp only [renameTerminator, Isotope.TAC.Densem.Classical.terminator,
        Isotope.TAC.Densem.Monadic.Terminator.denote]
      rw [value_denote M current source target hrel]
  | cond c left right ihl ihr =>
      simp only [renameTerminator, Isotope.TAC.Densem.Classical.terminator,
        Isotope.TAC.Densem.Monadic.Terminator.denote]
      rw [operand_denote M current source target hrel]
      apply bind_congr
      intro b
      cases b
      · exact ihr
      · exact ihl

end Isotope.TAC.Densem.Convert.Monadic
