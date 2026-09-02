import Isotope.TAC.Densem.Fresh

/-! # Whole-CFG correctness of canonical TAC-to-SSA conversion -/

namespace Isotope.TAC.Densem.Convert

open Isotope.TAC.Classical
open Isotope.TAC.Classical.Convert
open Isotope.TAC.Densem.Classical.Executable

variable {ν φ κ : Type} {M : Densem.Model φ}

/-- Source environments used for a closed TAC run assign every syntactic
variable.  The converter deliberately treats the finite source-variable
universe as the external interface, so this is its semantic precondition. -/
def Total (source : Densem.Env M ν) : Prop := ∀ x, ∃ a, source x = some a

/-- Lift a source store into the external namespace of structural SSA names. -/
def externalEnv (source : Densem.Env M ν) : Densem.Env M (Version ν κ)
  | .external x => source x
  | .phi _ _ | .instr _ _ _ _ => none

@[simp] theorem externalEnv_external (source : Densem.Env M ν) (x : ν) :
    externalEnv (M := M) (κ := κ) source (.external x) = source x := rfl

theorem external_envRelOn (vars : List ν) (source : Densem.Env M ν) :
    EnvRelOn vars (startEnv (.entry : BlockId κ)) source
      (externalEnv (M := M) (κ := κ) source) := by
  intro x _
  rfl

theorem Total.set [DecidableEq ν] {source : Densem.Env M ν}
    (h : Total source) (x : ν) (a : M.Val) :
    Total (Densem.Env.set source x a) := by
  intro y
  by_cases e : y = x
  · subst y; exact ⟨a, by simp [Densem.Env.set]⟩
  · rcases h y with ⟨v, hv⟩
    exact ⟨v, by simpa [Densem.Env.set, e] using hv⟩

theorem body_total [DecidableEq ν]
    (M : Densem.Model φ) (xs : List (Isotope.TAC.Classical.Instr ν φ))
    (t : Isotope.TAC.Classical.Terminator ν φ κ)
    (source source' : Densem.Env M ν)
    (exit : Densem.Exit κ M.Val) (htotal : Total source)
    (hden : bodyDenote M xs source t = some (source', exit)) :
    Total source' := by
  induction xs generalizing source with
  | nil =>
      simp only [bodyDenote] at hden
      cases h : terminatorDenote M source t <;> simp [h] at hden
      rcases hden with ⟨rfl, rfl⟩
      exact htotal
  | cons ins rest ih =>
      cases ins with
      | assign x rhs =>
          simp only [bodyDenote] at hden
          cases h : operandDenote M source rhs with
          | none => simp [h] at hden
          | some a =>
              simp only [h, Option.bind_some] at hden
              exact ih (source := Densem.Env.set source x a) (htotal.set x a) hden
      | assignPair x y rhs =>
          simp only [bodyDenote] at hden
          cases h : operandDenote M source rhs with
          | none => simp [h] at hden
          | some a =>
              cases hs : M.split a with
              | none => simp [h, hs] at hden
              | some p =>
                  rcases p with ⟨ax, ay⟩
                  simp [h, hs] at hden
                  exact ih
                    (source := (Densem.Env.set source x ax).set y ay)
                    ((htotal.set x ax).set y ay) hden

/-- The list lookup used by phi semantics commutes with canonical conversion. -/
theorem lookup_convert [DecidableEq ν] [DecidableEq κ]
    (source : Isotope.TAC.Classical.CFG ν φ κ) (label : κ) :
    Phi.lookup (convert source) label =
      (Phi.lookup source label).map
        (convertBlock source (sourceVars source) (.named label)) := by
  unfold Phi.lookup convert cfg
  let f := fun p : κ × Isotope.TAC.Classical.Block ν φ κ =>
    (p.1, convertBlock source (sourceVars source) (.named p.1) p.2)
  have go : ∀ xs : List (κ × Isotope.TAC.Classical.Block ν φ κ),
      ((xs.map f).find? fun p => p.1 = label).map Prod.snd =
        ((xs.find? fun p => p.1 = label).map Prod.snd).map
          (convertBlock source (sourceVars source) (.named label)) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons p ps ih =>
        simp only [List.map_cons, List.find?_cons]
        by_cases h : p.1 = label
        · subst label
          simp [f]
        · simp [f, h]
          simpa [Function.comp_def] using ih
  exact go source.blocks

/-- Source execution after leaving a block.  This is the phi-free TAC
counterpart of `Phi.continueFuel`. -/
def sourceContinue [DecidableEq ν] [DecidableEq κ]
    (M : Densem.Model φ) (g : Isotope.TAC.Classical.CFG ν φ κ) :
    Nat → Densem.Env M ν → Densem.Exit κ M.Val → Option M.Val
  | _, _, .return a => some a
  | 0, _, .branch _ => none
  | fuel + 1, ρ, .branch label => do
      let b ← Phi.lookup g label
      let (ρ', e) ← blockDenote M ρ b
      sourceContinue M g fuel ρ' e

def sourceRunFuel [DecidableEq ν] [DecidableEq κ]
    (M : Densem.Model φ) (g : Isotope.TAC.Classical.CFG ν φ κ) :
    Nat → Densem.Env M ν → Option M.Val
  | 0, _ => none
  | fuel + 1, ρ => do
      let (ρ', e) ← blockDenote M ρ g.entry
      sourceContinue M g fuel ρ' e

theorem lookup_some_mem [DecidableEq κ]
    {g : Isotope.TAC.Classical.CFG ν φ κ} {label : κ}
    {b : Isotope.TAC.Classical.Block ν φ κ}
    (h : Phi.lookup g label = some b) : (label, b) ∈ g.blocks := by
  unfold Phi.lookup at h
  rw [Option.map_eq_some_iff] at h
  rcases h with ⟨⟨foundLabel, foundBlock⟩, hp, rfl⟩
  have hlabel := List.find?_some hp
  have hmem := List.mem_of_find?_eq_some hp
  simp only [decide_eq_true_eq] at hlabel
  subst foundLabel
  exact hmem

/-- Entering a converted named block installs its simultaneous phis and then
simulates the source straight-line block. -/
theorem enter_named_sim [DecidableEq ν] [DecidableEq κ]
    (M : Densem.Model φ) (sourceCfg : Isotope.TAC.Classical.CFG ν φ κ)
    (label : κ) (pred : BlockId κ)
    (predBlock block : Isotope.TAC.Classical.Block ν φ κ)
    (source source' : Densem.Env M ν)
    (target : Densem.Env M (Version ν κ)) (exit : Densem.Exit κ M.Val)
    (hpred : pred ∈ predecessors sourceCfg (.named label))
    (hpredBlock : sourceCfg.lookup pred = some predBlock)
    (hblock : (label, block) ∈ sourceCfg.blocks)
    (htotal : Total source)
    (hrel : EnvRelOn (sourceVars sourceCfg) (endEnv pred predBlock) source target)
    (hsource : blockDenote M source block = some (source', exit)) :
    ∃ target',
      Phi.enter M target pred
          (convertBlock sourceCfg (sourceVars sourceCfg) (.named label) block) =
        some (target', exit) ∧
      EnvRelOn (sourceVars sourceCfg) (endEnv (.named label) block) source' target' := by
  let values : ν → M.Val := fun x => Classical.choose (htotal x)
  have hsourceValue : ∀ x, source x = some (values x) := by
    intro x
    exact Classical.choose_spec (htotal x)
  have hvalues : ∀ x ∈ sourceVars sourceCfg,
      target (endEnv pred predBlock x) = some (values x) := by
    intro x hx
    rw [hrel x hx, hsourceValue x]
  have ha := assignments_convert sourceCfg (sourceVars sourceCfg) label pred predBlock
    target values hpred hpredBlock hvalues
  have hstart := installed_phi_envRelOn (sourceVars sourceCfg)
    (sourceVars_nodup sourceCfg) label values target
  have hbody : bodyDenote M block.body source block.terminator =
      some (source', exit) := hsource
  rcases body_sim_on M (sourceVars sourceCfg) (.named label) 0
      (startEnv (.named label)) block.body block.terminator source source'
      (Phi.install target
        ((sourceVars sourceCfg).map fun x => (Version.phi label x, values x))) exit
      (by
        intro x hx
        rw [hstart x hx, hsourceValue x])
      (freshFor_startEnv (.named label) block.body)
      (by
        intro ins hi x hx
        exact block_use_mem_sourceVars sourceCfg hblock hi hx)
      (by
        intro x hx
        exact (mem_sourceVars sourceCfg x).2
          (.inr ⟨(label, block), hblock,
            terminator_use_mem_blockSourceVars block hx⟩))
      hbody with ⟨target', htarget, hrel'⟩
  refine ⟨target', ?_, hrel'⟩
  unfold Phi.enter
  simp only [convertBlock]
  rw [ha]
  exact htarget

end Isotope.TAC.Densem.Convert
