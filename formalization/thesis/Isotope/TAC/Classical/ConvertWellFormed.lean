import Isotope.TAC.Classical.Convert

/-! # Well-formedness of structurally fresh classical SSA conversion -/

namespace Isotope.TAC.Classical.Convert

open Isotope.TAC.Classical

universe u v w
variable {Var : Type u} {Op : Type v} {Label : Type w}

private theorem renameValue_uses_eq (ρ : Env Var Label) (v : Value Var) :
    (renameValue ρ v).uses = v.uses.map ρ := by
  induction v with
  | var => rfl
  | unit => rfl
  | pair l r il ir => simp [renameValue, Value.uses, il, ir]

private theorem renameOperand_uses_eq (ρ : Env Var Label) (o : Operand Var Op) :
    (renameOperand ρ o).uses = o.uses.map ρ := by
  cases o <;> simp [renameOperand, Operand.uses, renameValue_uses_eq]

private theorem renameTerminator_uses_eq (ρ : Env Var Label)
    (t : Terminator Var Op Label) :
    (renameTerminator ρ t).uses = t.uses.map ρ := by
  induction t with
  | br => rfl
  | ret v => simp [renameTerminator, Terminator.uses, renameValue_uses_eq]
  | cond o l r il ir =>
      simp [renameTerminator, Terminator.uses, renameOperand_uses_eq, il, ir]

theorem entryTerminator_use_mem_sourceVars [DecidableEq Var]
    (source : CFG Var Op Label) {x : Var} (hx : x ∈ source.entry.terminator.uses) :
    x ∈ sourceVars source :=
  (mem_sourceVars source x).2 (.inl (terminator_use_mem_blockSourceVars source.entry hx))

theorem convert_entryPhis [DecidableEq Var] [DecidableEq Label]
    (source : CFG Var Op Label) :
    (convert source).PhisWellFormed ((sourceVars source).map Version.external)
      .entry (convert source).entry := by
  intro phi hphi
  simp [convert, cfg, convertBlock] at hphi

theorem convert_entryTerminator [DecidableEq Var] [DecidableEq Label]
    (source : CFG Var Op Label) :
    (convert source).TerminatorUsesWellScoped
      ((sourceVars source).map Version.external) .entry (convert source).entry := by
  intro v hv
  change v ∈ (renameTerminator (endEnv (.entry : BlockId Label) source.entry)
    source.entry.terminator).uses at hv
  rw [renameTerminator_uses_eq] at hv
  rcases List.mem_map.mp hv with ⟨x, hx, rfl⟩
  rcases endEnv_start_or_def (.entry : BlockId Label) source.entry x with h | h
  · left
    left
    rw [h]
    exact List.mem_map.mpr ⟨x, entryTerminator_use_mem_sourceVars source hx, rfl⟩
  · right
    change endEnv (.entry : BlockId Label) source.entry x ∈
      CFG.defs (convert source).entry
    simpa [convert, cfg, convertBlock, CFG.defs, CFG.instrDefs] using h

/-- The program-point obligations left after the conversion has established
global freshness and preserved the source control-flow graph.  Keeping this
predicate separate makes the precise remaining source-side obligation visible:
ordinary uses must be available at their converted program point, while phi
uses are checked at the end of the indicated predecessor. -/
structure UseScoping [DecidableEq Var] [DecidableEq Label]
    (source : CFG Var Op Label) : Prop where
  entryBody : (convert source).BodyUsesWellScoped
    ((sourceVars source).map Version.external) .entry (convert source).entry
  entryTerminator : (convert source).TerminatorUsesWellScoped
    ((sourceVars source).map Version.external) .entry (convert source).entry
  entryPhis : (convert source).PhisWellFormed
    ((sourceVars source).map Version.external) .entry (convert source).entry
  blockBody (label block) (h : (convert source).lookup (.named label) = some block) :
    (convert source).BodyUsesWellScoped ((sourceVars source).map Version.external)
      (.named label) block
  blockTerminator (label block)
      (h : (convert source).lookup (.named label) = some block) :
    (convert source).TerminatorUsesWellScoped
      ((sourceVars source).map Version.external) (.named label) block
  blockPhis (label block) (h : (convert source).lookup (.named label) = some block) :
    (convert source).PhisWellFormed ((sourceVars source).map Version.external)
      (.named label) block

theorem externalVersions_nodup [DecidableEq Var] (source : CFG Var Op Label) :
    ((sourceVars source).map (Version.external : Var → Version Var Label)).Nodup := by
  have go : ∀ xs : List Var, xs.Nodup →
      (xs.map (Version.external : Var → Version Var Label)).Nodup := by
    intro xs hx
    induction xs with
    | nil => simp
    | cons x xs ih =>
        rw [List.nodup_cons] at hx
        simp only [List.map_cons, List.nodup_cons]
        exact ⟨by simpa using hx.1, ih hx.2⟩
  exact go (sourceVars source) (sourceVars_nodup source)

theorem externalVersions_fresh [DecidableEq Var] [DecidableEq Label]
    (source : CFG Var Op Label) :
    List.Disjoint ((sourceVars source).map Version.external) (convert source).allDefs := by
  simp only [List.Disjoint]
  intro v hv hd
  rcases List.mem_map.mp hv with ⟨x, -, rfl⟩
  exact external_not_cfg_def source (sourceVars source) x hd

/-- All non-scoping clauses of classical SSA well-formedness follow from the
structural conversion.  `UseScoping` records exactly the remaining
program-point argument, without hiding it in a freshness axiom. -/
theorem convert_wellFormed [DecidableEq Var] [DecidableEq Label]
    (source : CFG Var Op Label) (hlabels : source.uniqueLabels)
    (htargets : source.targetsExist) (hscope : UseScoping source) :
    (convert source).WellFormed ((sourceVars source).map Version.external) where
  externalsNodup := externalVersions_nodup source
  externalsFresh := externalVersions_fresh source
  uniqueLabels := cfg_uniqueLabels source (sourceVars source) hlabels
  targetsExist := cfg_targetsExist source (sourceVars source) htargets
  singleAssignment := convert_singleAssignment source hlabels
  entryBody := hscope.entryBody
  entryTerminator := hscope.entryTerminator
  entryPhis := hscope.entryPhis
  blockBody := hscope.blockBody
  blockTerminator := hscope.blockTerminator
  blockPhis := hscope.blockPhis

end Isotope.TAC.Classical.Convert
