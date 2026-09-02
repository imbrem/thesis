import Isotope.TAC.Densem.ConvertCFG
import Isotope.TAC.Densem.Lookup

/-! # Terminating-run preservation for canonical TAC-to-SSA conversion -/

namespace Isotope.TAC.Densem.Convert

open Isotope.TAC.Classical
open Isotope.TAC.Classical.Convert
open Isotope.TAC.Densem.Classical.Executable

variable {ν φ κ : Type} {M : Densem.Model φ}

def BlockPresent (g : Isotope.TAC.Classical.CFG ν φ κ)
    (bid : BlockId κ) : Prop :=
  bid = .entry ∨ ∃ label ∈ g.labels, bid = .named label

theorem successor_of_exit [DecidableEq κ]
    (g : Isotope.TAC.Classical.CFG ν φ κ)
    (pred : BlockId κ) (b : Isotope.TAC.Classical.Block ν φ κ)
    (label : κ) (hlookup : g.lookup pred = some b)
    (hvalid : ExitValid b (.branch label : Densem.Exit κ α)) :
    (.named label : BlockId κ) ∈ g.successors pred := by
  unfold Isotope.TAC.Classical.CFG.successors
  rw [hlookup]
  exact List.mem_map.mpr ⟨label, hvalid, rfl⟩

/-- Every terminating source continuation is reproduced by the converted SSA
graph, with the same returned value. -/
theorem continue_terminating [DecidableEq ν] [DecidableEq κ]
    (M : Densem.Model φ) (g : Isotope.TAC.Classical.CFG ν φ κ)
    (fuel : Nat) (pred : BlockId κ)
    (predBlock : Isotope.TAC.Classical.Block ν φ κ)
    (source : Densem.Env M ν) (target : Densem.Env M (Version ν κ))
    (exit : Densem.Exit κ M.Val) (result : M.Val)
    (hlookup : g.lookup pred = some predBlock)
    (hpresent : BlockPresent g pred) (htotal : Total source)
    (hrel : EnvRelOn (sourceVars g) (endEnv pred predBlock) source target)
    (hvalid : ExitValid predBlock exit)
    (hrun : sourceContinue M g fuel source exit = some result) :
    Isotope.TAC.Densem.Phi.continueFuel M (convert g) fuel target pred exit =
      some result := by
  induction fuel generalizing pred predBlock source target exit with
  | zero =>
      cases exit with
      | «return» a => simpa [sourceContinue, Isotope.TAC.Densem.Phi.continueFuel] using hrun
      | branch label => simp [sourceContinue] at hrun
  | succ fuel ih =>
      cases exit with
      | «return» a => simpa [sourceContinue, Isotope.TAC.Densem.Phi.continueFuel] using hrun
      | branch label =>
          simp only [sourceContinue] at hrun
          simp only [Isotope.TAC.Densem.Phi.continueFuel]
          rw [lookup_convert]
          cases hb : Isotope.TAC.Densem.Phi.lookup g label with
          | none => simp [hb] at hrun
          | some block =>
              simp only [hb, Option.map_some, Option.bind_some] at hrun ⊢
              cases hd : blockDenote M source block with
              | none => simp [hd] at hrun
              | some p =>
                  rcases p with ⟨source', nextExit⟩
                  have hrun' : sourceContinue M g fuel source' nextExit = some result := by
                    simpa [hb, hd] using hrun
                  have hcfgLookup : g.lookup (.named label) = some block := by
                    rw [← Isotope.TAC.Densem.Lookup.phi_lookup_eq g label]
                    exact hb
                  have hblock := Isotope.TAC.Densem.Lookup.mem_blocks_of_named_lookup g hcfgLookup
                  have hpred : pred ∈ predecessors g (.named label) :=
                    (mem_predecessors g pred (.named label)).2
                      ⟨successor_of_exit g pred predBlock label hlookup hvalid, hpresent⟩
                  rcases enter_named_sim M g label pred predBlock block source source'
                      target nextExit hpred hlookup hblock htotal hrel hd with
                    ⟨target', henter, hrel'⟩
                  change (do
                    let (target'', exit'') ← Isotope.TAC.Densem.Phi.enter M target pred
                      (convertBlock g (sourceVars g) (.named label) block)
                    Isotope.TAC.Densem.Phi.continueFuel M (convert g) fuel target''
                      (.named label) exit'') = some result
                  rw [henter]
                  have htotal' := body_total M block.body block.terminator source source'
                    nextExit htotal hd
                  have hvalid' := body_exit_valid M block source source' nextExit hd
                  have hpresent' : BlockPresent g (.named label) := .inr
                    ⟨label,
                      Isotope.TAC.Densem.Lookup.label_mem_of_named_lookup g hcfgLookup,
                      rfl⟩
                  exact ih (.named label) block source' target' nextExit hcfgLookup
                    hpresent' htotal' hrel' hvalid' hrun'

/-- Canonical SSA conversion preserves every terminating bounded execution
from a total source store. -/
theorem runFuel_terminating [DecidableEq ν] [DecidableEq κ]
    (M : Densem.Model φ) (g : Isotope.TAC.Classical.CFG ν φ κ)
    (fuel : Nat) (source : Densem.Env M ν) (result : M.Val)
    (htotal : Total source)
    (hrun : sourceRunFuel M g fuel source = some result) :
    Isotope.TAC.Densem.Phi.runFuel M (convert g) fuel
        (externalEnv (M := M) (κ := κ) source) = some result := by
  cases fuel with
  | zero => simp [sourceRunFuel] at hrun
  | succ fuel =>
      simp only [sourceRunFuel] at hrun
      simp only [Isotope.TAC.Densem.Phi.runFuel]
      cases hd : blockDenote M source g.entry with
      | none => simp [hd] at hrun
      | some p =>
          rcases p with ⟨source', exit⟩
          simp only [hd, Option.bind_some] at hrun
          rcases enter_entry_sim M g source source' exit hd with
            ⟨target', hentry, hrel⟩
          rw [hentry]
          exact continue_terminating M g fuel .entry g.entry source' target' exit result
            rfl (.inl rfl)
            (body_total M g.entry.body g.entry.terminator source source' exit htotal hd)
            hrel (body_exit_valid M g.entry source source' exit hd) hrun

end Isotope.TAC.Densem.Convert
