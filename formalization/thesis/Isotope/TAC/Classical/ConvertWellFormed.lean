import Isotope.TAC.Classical.Convert

/-! # Well-formedness of structurally fresh classical SSA conversion -/

namespace Isotope.TAC.Classical.Convert

open Isotope.TAC.Classical

universe u v w
variable {Var : Type u} {Op : Type v} {Label : Type w}

private theorem update_restricted_invariant [DecidableEq Var]
    (vars : List Var) (ρ : Env Var Label) (base prior : List (Version Var Label))
    (y : Var) (dst : Version Var Label)
    (hρ : ∀ x ∈ vars, ρ x ∈ base ∨ ρ x ∈ prior) :
    ∀ x ∈ vars, update ρ y dst x ∈ base ∨ update ρ y dst x ∈ dst :: prior := by
  intro x hx
  by_cases hxy : x = y
  · subst x
    exact .inr (by simp [update])
  · rcases hρ x hx with h | h
    · exact .inl (by simpa [update, hxy] using h)
    · exact .inr (List.mem_cons_of_mem dst (by simpa [update, hxy] using h))

private theorem updatePair_restricted_invariant [DecidableEq Var]
    (vars : List Var) (ρ : Env Var Label) (base prior : List (Version Var Label))
    (y z : Var) (dy dz : Version Var Label)
    (hρ : ∀ x ∈ vars, ρ x ∈ base ∨ ρ x ∈ prior) :
    ∀ x ∈ vars, update (update ρ y dy) z dz x ∈ base ∨
      update (update ρ y dy) z dz x ∈ dy :: dz :: prior := by
  intro x hx
  by_cases hxz : x = z
  · subst x
    exact .inr (by simp [update])
  · by_cases hxy : x = y
    · subst x
      exact .inr (by simp [update, hxz])
    · rcases hρ x hx with h | h
      · exact .inl (by simpa [update, hxz, hxy] using h)
      · exact .inr (List.mem_cons_of_mem dy
          (List.mem_cons_of_mem dz (by simpa [update, hxz, hxy] using h)))

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

theorem blockTerminator_use_mem_sourceVars [DecidableEq Var]
    (source : CFG Var Op Label) {label : Label} {b : Block Var Op Label}
    (hb : (label, b) ∈ source.blocks) {x : Var} (hx : x ∈ b.terminator.uses) :
    x ∈ sourceVars source :=
  (mem_sourceVars source x).2
    (.inr ⟨(label, b), hb, terminator_use_mem_blockSourceVars b hx⟩)

theorem convert_namedTerminator [DecidableEq Var] [DecidableEq Label]
    (source : CFG Var Op Label) (label : Label) (b : Block Var Op Label)
    (hb : (label, b) ∈ source.blocks) :
    (convert source).TerminatorUsesWellScoped
      ((sourceVars source).map Version.external) (.named label)
      (convertBlock source (sourceVars source) (.named label) b) := by
  intro v hv
  change v ∈ (renameTerminator (endEnv (.named label) b) b.terminator).uses at hv
  rw [renameTerminator_uses_eq] at hv
  rcases List.mem_map.mp hv with ⟨x, hx, rfl⟩
  rcases endEnv_start_or_def (.named label) b x with h | h
  · right
    change endEnv (.named label) b x ∈
      CFG.defs (convertBlock source (sourceVars source) (.named label) b)
    rw [h]
    apply List.mem_append_left
    change Version.phi label x ∈ (phis source (sourceVars source) label).map Phi.dst
    simp [phis, blockTerminator_use_mem_sourceVars source hb hx]
  · right
    change endEnv (.named label) b x ∈
      CFG.defs (convertBlock source (sourceVars source) (.named label) b)
    exact List.mem_append_right _ h

private theorem mem_incoming [DecidableEq Var] [DecidableEq Label]
    (source : CFG Var Op Label) (bid : BlockId Label) (x : Var)
    {inc : Incoming (Version Var Label) Label} (hinc : inc ∈ incoming source bid x) :
    ∃ pred b, pred ∈ predecessors source bid ∧ source.lookup pred = some b ∧
      inc = ⟨pred, .var (endEnv pred b x)⟩ := by
  rw [incoming, List.mem_filterMap] at hinc
  rcases hinc with ⟨pred, hpred, hp⟩
  cases hb : blockAt source pred with
  | none => simp [hb] at hp
  | some b =>
      simp only [hb, Option.map_some, Option.some.injEq] at hp
      exact ⟨pred, b, hpred, hb, hp.symm⟩

theorem convert_namedPhis [DecidableEq Var] [DecidableEq Label]
    (source : CFG Var Op Label) (label : Label) (hlabels : source.uniqueLabels) :
    (convert source).PhisWellFormed ((sourceVars source).map Version.external)
      (.named label)
      (convertBlock source (sourceVars source) (.named label)
        ((source.lookup (.named label)).getD source.entry)) := by
  intro phi hphi
  change phi ∈ phis source (sourceVars source) label at hphi
  rw [phis, List.mem_map] at hphi
  rcases hphi with ⟨x, hx, rfl⟩
  refine ⟨incoming_predecessors_nodup source (.named label) x hlabels, ?_⟩
  intro inc hinc
  rcases mem_incoming source (.named label) x hinc with
    ⟨pred, b, hpred, hb, rfl⟩
  change BlockId.named label ∈ (convert source).successors pred ∧ _
  refine ⟨?_, ?_⟩
  · change BlockId.named label ∈
      (cfg source (sourceVars source)).successors pred
    rw [successors_cfg]
    exact (mem_predecessors source pred (.named label)).1 hpred |>.1
  · intro v hv
    simp only [Value.uses, List.mem_singleton] at hv
    subst v
    rcases endEnv_start_or_def pred b x with h | h
    · rw [h]
      cases pred with
      | entry =>
          left
          exact List.mem_map.mpr ⟨x, hx, rfl⟩
      | named predLabel =>
          right
          refine ⟨convertBlock source (sourceVars source) (.named predLabel) b, ?_⟩
          left
          constructor
          · change (convert source).lookup (.named predLabel) = _
            simpa [convert, hb] using
              (lookup_cfg source (sourceVars source) (.named predLabel))
          ·
            change Version.phi predLabel x ∈
              CFG.defs (convertBlock source (sourceVars source) (.named predLabel) b)
            apply List.mem_append_left
            change Version.phi predLabel x ∈
              (phis source (sourceVars source) predLabel).map Phi.dst
            simp only [phis, List.map_map, Function.comp_apply]
            change Version.phi predLabel x ∈
              (sourceVars source).map (Version.phi predLabel)
            exact List.mem_map.mpr ⟨x, hx, rfl⟩
    · right
      refine ⟨convertBlock source (sourceVars source) pred b, ?_⟩
      left
      constructor
      · change (convert source).lookup pred = _
        simpa [convert, hb] using (lookup_cfg source (sourceVars source) pred)
      ·
        change endEnv pred b x ∈ CFG.defs
          (convertBlock source (sourceVars source) pred b)
        cases pred with
        | entry => simpa [convertBlock, CFG.defs, CFG.instrDefs] using h
        | named l =>
            change endEnv (.named l) b x ∈
              (phis source (sourceVars source) l).map Phi.dst ++
                (body (.named l) 0 (startEnv (.named l)) b.body).1.flatMap Instr.defs
            exact List.mem_append_right _ h

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
