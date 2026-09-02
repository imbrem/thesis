import Isotope.TAC.Densem.ConvertRun
import Isotope.TAC.Densem.ConvertReverse

/-! # Exact bounded-denotation preservation for canonical SSA conversion -/

namespace Isotope.TAC.Densem.Convert

open Isotope.TAC.Classical
open Isotope.TAC.Classical.Convert
open Isotope.TAC.Densem.Classical.Executable

variable {ν φ κ : Type} {M : Densem.Model φ}

theorem continue_reflecting [DecidableEq ν] [DecidableEq κ]
    (M : Densem.Model φ) (g : Isotope.TAC.Classical.CFG ν φ κ)
    (fuel : Nat) (pred : BlockId κ)
    (predBlock : Isotope.TAC.Classical.Block ν φ κ)
    (source : Densem.Env M ν) (target : Densem.Env M (Version ν κ))
    (exit : Densem.Exit κ M.Val) (result : M.Val)
    (hlookup : g.lookup pred = some predBlock)
    (hpresent : BlockPresent g pred) (htotal : Total source)
    (hrel : EnvRelOn (sourceVars g) (endEnv pred predBlock) source target)
    (hvalid : ExitValid predBlock exit)
    (hrun : Isotope.TAC.Densem.Phi.continueFuel M (convert g) fuel target pred exit =
      some result) :
    sourceContinue M g fuel source exit = some result := by
  induction fuel generalizing pred predBlock source target exit with
  | zero =>
      cases exit with
      | «return» a =>
          simpa [sourceContinue, Isotope.TAC.Densem.Phi.continueFuel] using hrun
      | branch label => simp [Isotope.TAC.Densem.Phi.continueFuel] at hrun
  | succ fuel ih =>
      cases exit with
      | «return» a =>
          simpa [sourceContinue, Isotope.TAC.Densem.Phi.continueFuel] using hrun
      | branch label =>
          simp only [Isotope.TAC.Densem.Phi.continueFuel] at hrun
          rw [lookup_convert] at hrun
          cases hb : Isotope.TAC.Densem.Phi.lookup g label with
          | none => simp [hb] at hrun
          | some block =>
              simp only [hb, Option.map_some, Option.bind_some] at hrun
              cases he : Isotope.TAC.Densem.Phi.enter M target pred
                  (convertBlock g (sourceVars g) (.named label) block) with
              | none => simp [he] at hrun
              | some p =>
                  rcases p with ⟨target', nextExit⟩
                  have hrun' : Isotope.TAC.Densem.Phi.continueFuel M (convert g) fuel
                      target' (.named label) nextExit = some result := by
                    simpa [hb, he] using hrun
                  have hcfgLookup : g.lookup (.named label) = some block := by
                    rw [← Isotope.TAC.Densem.Lookup.phi_lookup_eq g label]
                    exact hb
                  have hblock :=
                    Isotope.TAC.Densem.Lookup.mem_blocks_of_named_lookup g hcfgLookup
                  have hpred : pred ∈ predecessors g (.named label) :=
                    (mem_predecessors g pred (.named label)).2
                      ⟨successor_of_exit g pred predBlock label hlookup hvalid, hpresent⟩
                  rcases enter_named_reverse M g label pred predBlock block source target
                      target' nextExit hpred hlookup hblock htotal hrel he with
                    ⟨source', hsource, hrel'⟩
                  have htotal' := body_total M block.body block.terminator source source'
                    nextExit htotal hsource
                  have hvalid' := body_exit_valid M block source source' nextExit hsource
                  have hpresent' : BlockPresent g (.named label) := .inr
                    ⟨label,
                      Isotope.TAC.Densem.Lookup.label_mem_of_named_lookup g hcfgLookup,
                      rfl⟩
                  have hrec := ih (.named label) block source' target' nextExit
                    hcfgLookup hpresent' htotal' hrel' hvalid' hrun'
                  change (do
                    let nextBlock ← Isotope.TAC.Densem.Phi.lookup g label
                    let (source'', exit'') ← blockDenote M source nextBlock
                    sourceContinue M g fuel source'' exit'') = some result
                  simpa [hb, hsource] using hrec

theorem runFuel_reflecting [DecidableEq ν] [DecidableEq κ]
    (M : Densem.Model φ) (g : Isotope.TAC.Classical.CFG ν φ κ)
    (fuel : Nat) (source : Densem.Env M ν) (result : M.Val)
    (htotal : Total source)
    (hrun : Isotope.TAC.Densem.Phi.runFuel M (convert g) fuel
      (externalEnv (M := M) (κ := κ) source) = some result) :
    sourceRunFuel M g fuel source = some result := by
  cases fuel with
  | zero => simp [Isotope.TAC.Densem.Phi.runFuel] at hrun
  | succ fuel =>
      simp only [Isotope.TAC.Densem.Phi.runFuel] at hrun
      cases he : Isotope.TAC.Densem.Phi.enter M
          (externalEnv (M := M) (κ := κ) source) .entry (convert g).entry with
      | none => simp [he] at hrun
      | some p =>
          rcases p with ⟨target', exit⟩
          have hrun' : Isotope.TAC.Densem.Phi.continueFuel M (convert g) fuel
              target' .entry exit = some result := by
            simpa [he] using hrun
          rcases enter_entry_reverse M g source target' exit he with
            ⟨source', hsource, hrel⟩
          have hrec := continue_reflecting M g fuel .entry g.entry source' target'
            exit result rfl (.inl rfl)
            (body_total M g.entry.body g.entry.terminator source source' exit htotal hsource)
            hrel (body_exit_valid M g.entry source source' exit hsource) hrun'
          simp only [sourceRunFuel, hsource, Option.bind_some]
          exact hrec

/-- The canonical structural SSA rewrite has exactly the same bounded
executable denotation as its source TAC graph, on total source stores. -/
theorem runFuel_convert_eq [DecidableEq ν] [DecidableEq κ]
    (M : Densem.Model φ) (g : Isotope.TAC.Classical.CFG ν φ κ)
    (fuel : Nat) (source : Densem.Env M ν) (htotal : Total source) :
    Isotope.TAC.Densem.Phi.runFuel M (convert g) fuel
        (externalEnv (M := M) (κ := κ) source) = sourceRunFuel M g fuel source := by
  cases hs : sourceRunFuel M g fuel source with
  | some result => exact runFuel_terminating M g fuel source result htotal hs
  | none =>
      cases ht : Isotope.TAC.Densem.Phi.runFuel M (convert g) fuel
          (externalEnv (M := M) (κ := κ) source) with
      | none => rfl
      | some result =>
          have := runFuel_reflecting M g fuel source result htotal ht
          rw [hs] at this
          contradiction

theorem sourceContinue_eq_classical [DecidableEq ν] [DecidableEq κ]
    (M : Densem.Model φ) (g : Isotope.TAC.Classical.CFG ν φ κ)
    (fuel : Nat) (source : Densem.Env M ν) (exit : Densem.Exit κ M.Val) :
    sourceContinue M g fuel source exit = continueFuel M g fuel source exit := by
  induction fuel generalizing source exit with
  | zero => cases exit <;> rfl
  | succ fuel ih =>
      cases exit with
      | «return» => rfl
      | branch label =>
          simp only [sourceContinue, continueFuel]
          change (do
            let b ← Isotope.TAC.Densem.Phi.lookup g label
            let (source', nextExit) ← blockDenote M source b
            sourceContinue M g fuel source' nextExit) = _
          change _ = (do
            let b ← lookup g label
            let (source', nextExit) ← blockDenote M source b
            continueFuel M g fuel source' nextExit)
          have hl : Isotope.TAC.Densem.Phi.lookup g label = lookup g label := rfl
          rw [hl]
          cases hb : lookup g label with
          | none => simp [hb]
          | some b =>
              cases hd : blockDenote M source b with
              | none => simp [hb, hd]
              | some p =>
                  rcases p with ⟨source', nextExit⟩
                  simpa [hb, hd] using ih source' nextExit

theorem sourceRunFuel_eq_classical [DecidableEq ν] [DecidableEq κ]
    (M : Densem.Model φ) (g : Isotope.TAC.Classical.CFG ν φ κ)
    (fuel : Nat) (source : Densem.Env M ν) :
    sourceRunFuel M g fuel source = cfgRunFuel M g fuel source := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp only [sourceRunFuel, cfgRunFuel]
      cases hd : blockDenote M source g.entry with
      | none => rfl
      | some p =>
          rcases p with ⟨source', exit⟩
          exact sourceContinue_eq_classical M g fuel source' exit

/-- Main executable correctness statement against the pre-existing classical
TAC densem: conversion to SSA preserves the complete bounded observation,
including failure or fuel exhaustion. -/
theorem runFuel_convert_eq_classical [DecidableEq ν] [DecidableEq κ]
    (M : Densem.Model φ) (g : Isotope.TAC.Classical.CFG ν φ κ)
    (fuel : Nat) (source : Densem.Env M ν) (htotal : Total source) :
    Isotope.TAC.Densem.Phi.runFuel M (convert g) fuel
        (externalEnv (M := M) (κ := κ) source) = cfgRunFuel M g fuel source :=
  (runFuel_convert_eq M g fuel source htotal).trans
    (sourceRunFuel_eq_classical M g fuel source)

end Isotope.TAC.Densem.Convert
