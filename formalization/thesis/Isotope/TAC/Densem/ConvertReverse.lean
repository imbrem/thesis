import Isotope.TAC.Densem.ConvertCFG

/-! # Reflection of successful converted TAC executions -/

namespace Isotope.TAC.Densem.Convert

open Isotope.TAC.Classical
open Isotope.TAC.Classical.Convert
open Isotope.TAC.Densem.Classical.Executable

variable {ν φ κ : Type} {M : Densem.Model φ}

/-- Reverse scoped straight-line simulation.  A successful execution of a
converted body reflects to a source execution with the same control-flow
exit; the resulting stores retain the compiler environment relation. -/
theorem body_sim_on_reverse [DecidableEq ν] [DecidableEq κ]
    (M : Densem.Model φ) (needed : List ν) (bid : BlockId κ) (i : Nat)
    (current : Isotope.TAC.Classical.Convert.Env ν κ)
    (xs : List (Instr ν φ)) (t : Isotope.TAC.Classical.Terminator ν φ κ)
    (source : Densem.Env M ν)
    (target target' : Densem.Env M (Version ν κ))
    (exit : Densem.Exit κ M.Val)
    (hrel : EnvRelOn needed current source target)
    (hfresh : FreshFor bid i current xs)
    (hins : ∀ ins ∈ xs, ∀ x ∈ ins.uses, x ∈ needed)
    (hterm : ∀ x ∈ t.uses, x ∈ needed)
    (htarget : bodyDenote M (body bid i current xs).1 target
        (renameTerminator (body bid i current xs).2 t) = some (target', exit)) :
    ∃ source', bodyDenote M xs source t = some (source', exit) ∧
      EnvRelOn needed (body bid i current xs).2 source' target' := by
  induction xs generalizing i current source target target' with
  | nil =>
      simp only [bodyDenote, body] at htarget ⊢
      rw [terminator_sim_on M needed current source target hrel t hterm] at htarget
      cases ht : terminatorDenote M source t with
      | none => simp [ht] at htarget
      | some e =>
          simp only [ht, Option.map_some, Option.some.injEq, Prod.mk.injEq] at htarget
          rcases htarget with ⟨rfl, rfl⟩
          exact ⟨source, by simp [ht], hrel⟩
  | cons instr rest ih =>
      have htail : ∀ ins ∈ rest, ∀ x ∈ ins.uses, x ∈ needed := by
        intro ins hi x hx
        exact hins ins (List.mem_cons_of_mem instr hi) x hx
      cases instr with
      | assign x rhs =>
          rcases hfresh with ⟨hdst, hrest⟩
          have hop := operand_sim_on M needed current source target hrel rhs
            (fun y hy => hins (.assign x rhs) (by simp) y hy)
          simp only [body, bodyDenote] at htarget
          rw [hop] at htarget
          cases hv : operandDenote M source rhs with
          | none => simp [hv] at htarget
          | some a =>
              simp only [hv, Option.bind_some] at htarget
              have hnext := envRelOn_update needed current source target hrel x
                (Version.instr bid i 0 x) a hdst
              rcases ih (i + 1) (update current x (Version.instr bid i 0 x))
                  (Densem.Env.set source x a)
                  (Densem.Env.set target (Version.instr bid i 0 x) a) target'
                  hnext hrest htail htarget with ⟨source', hs, hr⟩
              exact ⟨source', by simp [bodyDenote, hv, hs], hr⟩
      | assignPair x y rhs =>
          rcases hfresh with ⟨hdx, hdy, hrest⟩
          have hop := operand_sim_on M needed current source target hrel rhs
            (fun z hz => hins (.assignPair x y rhs) (by simp) z hz)
          simp only [body, bodyDenote] at htarget
          rw [hop] at htarget
          cases hv : operandDenote M source rhs with
          | none => simp [hv] at htarget
          | some a =>
              cases hp : M.split a with
              | none => simp [hv, hp] at htarget
              | some p =>
                  rcases p with ⟨ax, ay⟩
                  simp [hv, hp] at htarget
                  have hx := envRelOn_update needed current source target hrel x
                    (Version.instr bid i 0 x) ax hdx
                  have hxy := envRelOn_update needed
                    (update current x (Version.instr bid i 0 x))
                    (Densem.Env.set source x ax)
                    (Densem.Env.set target (Version.instr bid i 0 x) ax)
                    hx y (Version.instr bid i 1 y) ay hdy
                  rcases ih (i + 1)
                      (update (update current x (Version.instr bid i 0 x)) y
                        (Version.instr bid i 1 y))
                      ((Densem.Env.set source x ax).set y ay)
                      ((Densem.Env.set target (Version.instr bid i 0 x) ax).set
                        (Version.instr bid i 1 y) ay) target'
                      hxy hrest htail htarget with ⟨source', hs, hr⟩
                  exact ⟨source', by simp [bodyDenote, hv, hp, hs], hr⟩

/-- Reverse simulation for a converted named block, including simultaneous
phi installation. -/
theorem enter_named_reverse [DecidableEq ν] [DecidableEq κ]
    (M : Densem.Model φ) (g : Isotope.TAC.Classical.CFG ν φ κ)
    (label : κ) (pred : BlockId κ)
    (predBlock block : Isotope.TAC.Classical.Block ν φ κ)
    (source : Densem.Env M ν) (target target' : Densem.Env M (Version ν κ))
    (exit : Densem.Exit κ M.Val)
    (hpred : pred ∈ predecessors g (.named label))
    (hpredBlock : g.lookup pred = some predBlock)
    (hblock : (label, block) ∈ g.blocks)
    (htotal : Total source)
    (hrel : EnvRelOn (sourceVars g) (endEnv pred predBlock) source target)
    (htarget : Isotope.TAC.Densem.Phi.enter M target pred
        (convertBlock g (sourceVars g) (.named label) block) = some (target', exit)) :
    ∃ source', blockDenote M source block = some (source', exit) ∧
      EnvRelOn (sourceVars g) (endEnv (.named label) block) source' target' := by
  let values : ν → M.Val := fun x => Classical.choose (htotal x)
  have hsourceValue : ∀ x, source x = some (values x) := fun x =>
    Classical.choose_spec (htotal x)
  have hvalues : ∀ x ∈ sourceVars g,
      target (endEnv pred predBlock x) = some (values x) := by
    intro x hx
    rw [hrel x hx, hsourceValue x]
  have ha := assignments_convert g (sourceVars g) label pred predBlock target values
    hpred hpredBlock hvalues
  have hstart := installed_phi_envRelOn (sourceVars g) (sourceVars_nodup g)
    label values target
  unfold Isotope.TAC.Densem.Phi.enter at htarget
  simp only [convertBlock] at htarget
  rw [ha] at htarget
  rcases body_sim_on_reverse M (sourceVars g) (.named label) 0
      (startEnv (.named label)) block.body block.terminator source
      (Isotope.TAC.Densem.Phi.install target
        ((sourceVars g).map fun x => (Version.phi label x, values x))) target' exit
      (by
        intro x hx
        rw [hstart x hx, hsourceValue x])
      (freshFor_startEnv (.named label) block.body)
      (by
        intro ins hi x hx
        exact block_use_mem_sourceVars g hblock hi hx)
      (by
        intro x hx
        exact (mem_sourceVars g x).2
          (.inr ⟨(label, block), hblock, terminator_use_mem_blockSourceVars block hx⟩))
      htarget with ⟨source', hs, hr⟩
  exact ⟨source', hs, hr⟩

/-- Reverse simulation of the phi-free converted entry block. -/
theorem enter_entry_reverse [DecidableEq ν] [DecidableEq κ]
    (M : Densem.Model φ) (g : Isotope.TAC.Classical.CFG ν φ κ)
    (source : Densem.Env M ν) (target' : Densem.Env M (Version ν κ))
    (exit : Densem.Exit κ M.Val)
    (htarget : Isotope.TAC.Densem.Phi.enter M
        (externalEnv (M := M) (κ := κ) source) .entry (convert g).entry =
          some (target', exit)) :
    ∃ source', blockDenote M source g.entry = some (source', exit) ∧
      EnvRelOn (sourceVars g) (endEnv .entry g.entry) source' target' := by
  have hrel := external_envRelOn (M := M) (κ := κ) (sourceVars g) source
  have hb : bodyDenote M (body .entry 0 (startEnv .entry) g.entry.body).1
      (externalEnv (M := M) (κ := κ) source)
      (renameTerminator (body .entry 0 (startEnv .entry) g.entry.body).2
        g.entry.terminator) = some (target', exit) := by
    simpa [Isotope.TAC.Densem.Phi.enter, convert, convertBlock] using htarget
  rcases body_sim_on_reverse M (sourceVars g) .entry 0 (startEnv .entry)
      g.entry.body g.entry.terminator source
      (externalEnv (M := M) (κ := κ) source) target' exit hrel
      (freshFor_startEnv .entry g.entry.body)
      (by
        intro ins hi x hx
        exact entry_use_mem_sourceVars g hi hx)
      (by
        intro x hx
        exact (mem_sourceVars g x).2
          (.inl (terminator_use_mem_blockSourceVars g.entry hx))) hb with
    ⟨source', hs, hr⟩
  exact ⟨source', hs, hr⟩

end Isotope.TAC.Densem.Convert
