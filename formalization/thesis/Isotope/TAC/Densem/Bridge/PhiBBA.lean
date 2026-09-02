import Isotope.TAC.Bridge.PhiBBA
import Isotope.TAC.Densem.Phi

/-! # Semantics of block-argument SSA

The operational meaning of a block-argument CFG is obtained by the canonical
edge-argument-to-phi elaboration.  This fixes the predecessor convention for
parallel edges once and for all: it is exactly the textual convention used by
`Bridge.PhiBBA.CFG.toPhi`.  The executable and complete-Elgot interpretations
therefore descend along the normalized phi/BBA equivalence, rather than merely
being related at the syntax level.
-/

namespace Isotope.TAC.Densem.BBA

namespace B
abbrev CFG := Isotope.TAC.Bridge.PhiBBA.CFG
end B

namespace P
abbrev CFG := Isotope.TAC.Classical.CFG
end P

universe u v w q

/-- Executable semantics of flat SSA with block arguments.  Edge arguments
are elaborated to predecessor-indexed phi rows before execution. -/
def runFuel [DecidableEq ν] [DecidableEq κ] (M : Model φ)
    (g : B.CFG ν φ κ) (fuel : Nat) (ρ : Env M ν) : Option M.Val :=
  Phi.runFuel M (Isotope.TAC.Bridge.PhiBBA.CFG.toPhi g) fuel ρ

/-- Relational graph of executable block-argument semantics. -/
def Denotes [DecidableEq ν] [DecidableEq κ] (M : Model φ)
    (g : B.CFG ν φ κ) (fuel : Nat) (ρ : Env M ν) (a : M.Val) : Prop :=
  runFuel M g fuel ρ = some a

@[simp] theorem runFuel_toPhi [DecidableEq ν] [DecidableEq κ]
    (M : Model φ) (g : B.CFG ν φ κ) (fuel : Nat) (ρ : Env M ν) :
    runFuel M g fuel ρ =
      Phi.runFuel M (Isotope.TAC.Bridge.PhiBBA.CFG.toPhi g) fuel ρ := rfl

/-- Moving normalized phi operands onto source edges preserves every bounded
execution, including failure and fuel exhaustion. -/
theorem runFuel_ofPhi [DecidableEq ν] [DecidableEq κ]
    (M : Model φ) (g : P.CFG ν φ κ)
    (hg : Isotope.TAC.Bridge.PhiBBA.CFG.PhiNormalized g)
    (bba : B.CFG ν φ κ)
    (h : Isotope.TAC.Bridge.PhiBBA.CFG.ofPhi g = some bba)
    (fuel : Nat) (ρ : Env M ν) :
    runFuel M bba fuel ρ = Phi.runFuel M g fuel ρ := by
  rw [runFuel, Isotope.TAC.Bridge.PhiBBA.CFG.toPhi_ofPhi hg h]

/-- Executable denotation is constant across the exact normalized
phi/block-argument equivalence. -/
theorem normalizedEquiv_runFuel [DecidableEq ν] [DecidableEq κ]
    (M : Model φ)
    (g : {g : P.CFG ν φ κ //
      Isotope.TAC.Bridge.PhiBBA.CFG.PhiNormalized g})
    (fuel : Nat) (ρ : Env M ν) :
    runFuel M (Isotope.TAC.Bridge.PhiBBA.CFG.normalizedEquiv g).1 fuel ρ =
      Phi.runFuel M g.1 fuel ρ := by
  let bba := Classical.choose g.property
  have hbba := (Classical.choose_spec g.property).1
  change runFuel M bba fuel ρ = Phi.runFuel M g.1 fuel ρ
  exact runFuel_ofPhi M g.1 g.property bba hbba fuel ρ

theorem normalizedEquiv_denotes [DecidableEq ν] [DecidableEq κ]
    (M : Model φ)
    (g : {g : P.CFG ν φ κ //
      Isotope.TAC.Bridge.PhiBBA.CFG.PhiNormalized g})
    (fuel : Nat) (ρ : Env M ν) (a : M.Val) :
    Denotes M (Isotope.TAC.Bridge.PhiBBA.CFG.normalizedEquiv g).1 fuel ρ a ↔
      Phi.runFuel M g.1 fuel ρ = some a := by
  unfold Denotes
  rw [normalizedEquiv_runFuel]

namespace Monadic

/-- Complete-Elgot semantics of flat SSA with block arguments. -/
def denote [Monad m] [Isotope.Elgot.Iterate m] [DecidableEq ν] [DecidableEq κ]
    (M : Isotope.TAC.Densem.Monadic.Model φ m)
    (g : B.CFG ν φ κ) (ρ : Isotope.TAC.Densem.Monadic.Env M ν) : m M.Val :=
  Phi.Monadic.denote M (Isotope.TAC.Bridge.PhiBBA.CFG.toPhi g) ρ

@[simp] theorem denote_toPhi [Monad m] [Isotope.Elgot.Iterate m]
    [DecidableEq ν] [DecidableEq κ]
    (M : Isotope.TAC.Densem.Monadic.Model φ m)
    (g : B.CFG ν φ κ) (ρ : Isotope.TAC.Densem.Monadic.Env M ν) :
    denote M g ρ =
      Phi.Monadic.denote M (Isotope.TAC.Bridge.PhiBBA.CFG.toPhi g) ρ := rfl

/-- Moving normalized phi operands onto edges commutes exactly with complete-
Elgot iteration. -/
theorem denote_ofPhi [Monad m] [Isotope.Elgot.Iterate m]
    [DecidableEq ν] [DecidableEq κ]
    (M : Isotope.TAC.Densem.Monadic.Model φ m)
    (g : P.CFG ν φ κ)
    (hg : Isotope.TAC.Bridge.PhiBBA.CFG.PhiNormalized g)
    (bba : B.CFG ν φ κ)
    (h : Isotope.TAC.Bridge.PhiBBA.CFG.ofPhi g = some bba)
    (ρ : Isotope.TAC.Densem.Monadic.Env M ν) :
    denote M bba ρ = Phi.Monadic.denote M g ρ := by
  rw [denote, Isotope.TAC.Bridge.PhiBBA.CFG.toPhi_ofPhi hg h]

theorem normalizedEquiv_denote [Monad m] [Isotope.Elgot.Iterate m]
    [DecidableEq ν] [DecidableEq κ]
    (M : Isotope.TAC.Densem.Monadic.Model φ m)
    (g : {g : P.CFG ν φ κ //
      Isotope.TAC.Bridge.PhiBBA.CFG.PhiNormalized g})
    (ρ : Isotope.TAC.Densem.Monadic.Env M ν) :
    denote M (Isotope.TAC.Bridge.PhiBBA.CFG.normalizedEquiv g).1 ρ =
      Phi.Monadic.denote M g.1 ρ := by
  let bba := Classical.choose g.property
  have hbba := (Classical.choose_spec g.property).1
  change denote M bba ρ = Phi.Monadic.denote M g.1 ρ
  exact denote_ofPhi M g.1 g.property bba hbba ρ

end Monadic

end Isotope.TAC.Densem.BBA
