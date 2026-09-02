import Isotope.TAC.Bridge.PhiBBA
import Isotope.TAC.Classical.Convert
import Mathlib.Data.List.Nodup

/-! # Canonical SSA conversion lands in normalized phi form -/

namespace Isotope.TAC.Bridge.PhiBBA.Convert

open Isotope.TAC.Classical
open Isotope.TAC.Classical.Convert

universe u v w
variable {Var : Type u} {Op : Type v} {Label : Type w}
variable [DecidableEq Var] [DecidableEq Label]

private theorem lookup_eq_some_of_mem_of_unique
    {blocks : List (Label × Classical.Block Var Op Label)}
    (hlabels : (blocks.map Prod.fst).Nodup)
    {label : Label} {block : Classical.Block Var Op Label}
    (hmem : (label, block) ∈ blocks) : blocks.lookup label = some block := by
  induction blocks with
  | nil => simp at hmem
  | cons head tail ih =>
      rcases head with ⟨headLabel, headBlock⟩
      rw [List.map_cons, List.nodup_cons] at hlabels
      rw [List.mem_cons] at hmem
      rcases hmem with hmem | hmem
      · cases hmem
        simp [List.lookup]
      · have hne : label ≠ headLabel := by
          intro heq
          subst label
          exact hlabels.1 (List.mem_map.mpr ⟨(headLabel, block), hmem, rfl⟩)
        have hbeq : (label == headLabel) = false := by simp [hne]
        simp [List.lookup, hbeq, ih hlabels.2 hmem]

theorem successors_named_of_mem
    {source : Classical.CFG Var Op Label} (hlabels : source.uniqueLabels)
    {label : Label} {block : Classical.Block Var Op Label}
    (hmem : (label, block) ∈ source.blocks) :
    source.successors (.named label) = block.terminator.targets.map BlockId.named := by
  unfold Classical.CFG.successors Classical.CFG.lookup
  change (match source.blocks.lookup label with
    | none => []
    | some block => block.terminator.targets.map BlockId.named) = _
  rw [lookup_eq_some_of_mem_of_unique hlabels hmem]

/-- The converter and the BBA bridge enumerate predecessors in the same
entry-then-textual-block order. -/
theorem predecessors_eq_phiPredecessors
    (source : Classical.CFG Var Op Label) (hlabels : source.uniqueLabels)
    (target : Label) :
    predecessors source (.named target) =
      PhiBBA.CFG.phiPredecessors (convert source) target := by
  unfold predecessors PhiBBA.CFG.phiPredecessors
  rw [show (convert source).entry.terminator.targets =
    source.entry.terminator.targets by
      simp [convert, cfg, convertBlock, renameTerminator_targets]]
  rw [show (convert source).blocks = source.blocks.map (fun pair =>
    (pair.1, convertBlock source (sourceVars source) (.named pair.1) pair.2)) by rfl]
  simp only [List.flatMap_map, Function.comp_apply]
  unfold Classical.CFG.labels
  rw [List.map_map]
  rw [List.filter_cons]
  have hentry : decide (BlockId.named target ∈ source.successors .entry) =
      decide (target ∈ source.entry.terminator.targets) := by
    simp [Classical.CFG.successors, Classical.CFG.lookup]
  rw [hentry]
  have aux : ∀ xs : List (Label × Classical.Block Var Op Label),
      (∀ pair, pair ∈ xs → pair ∈ source.blocks) →
      (xs.map (BlockId.named ∘ Prod.fst)).filter
          (fun src => .named target ∈ source.successors src) =
        xs.flatMap (fun pair =>
          if target ∈ (convertBlock source (sourceVars source)
              (.named pair.1) pair.2).terminator.targets then
            [.named pair.1]
          else []) := by
    intro xs hsubset
    induction xs with
    | nil => rfl
    | cons head tail ih =>
        rcases head with ⟨label, block⟩
        rw [List.map_cons, List.filter_cons, List.flatMap_cons]
        have hmem := hsubset (label, block) List.mem_cons_self
        simp only [Function.comp_apply, Prod.fst]
        have hsucc := successors_named_of_mem hlabels hmem
        by_cases ht : target ∈ block.terminator.targets
        · have hleft : BlockId.named target ∈ source.successors (.named label) := by
            rw [hsucc]
            exact List.mem_map.mpr ⟨target, ht, rfl⟩
          simp only [hleft, decide_true, if_true, convertBlock,
            renameTerminator_targets, ht, List.singleton_append]
          have iht := ih (fun pair hp => hsubset pair
            (List.Mem.tail (label, block) hp))
          simpa only [convertBlock, renameTerminator_targets] using
            congrArg (List.cons (.named label)) iht
        · have hleft : BlockId.named target ∉ source.successors (.named label) := by
            rw [hsucc]
            simpa using ht
          simp only [hleft, decide_false, if_false, convertBlock,
            renameTerminator_targets, ht, List.nil_append]
          have iht := ih (fun pair hp => hsubset pair
            (List.Mem.tail (label, block) hp))
          simpa only [convertBlock, renameTerminator_targets] using iht
  have haux := aux source.blocks (fun _ h => h)
  by_cases ht : target ∈ source.entry.terminator.targets <;> simp [ht, haux]

theorem phiEdgeKeys_convert (source : Classical.CFG Var Op Label) :
    PhiBBA.CFG.phiEdgeKeys (convert source) = PhiBBA.CFG.phiEdgeKeys source := by
  simp only [PhiBBA.CFG.phiEdgeKeys, convert, cfg, convertBlock,
    renameTerminator_targets, List.flatMap_map, Function.comp_apply]

private theorem mem_of_lookup_eq_some
    {blocks : List (Label × Classical.Block Var Op Label)}
    {label : Label} {block : Classical.Block Var Op Label}
    (h : blocks.lookup label = some block) : (label, block) ∈ blocks := by
  rcases List.lookup_eq_some_iff.mp h with ⟨before, after, rfl, _⟩
  simp

theorem targetsDefined_convert (source : Classical.CFG Var Op Label)
    (hlabels : source.uniqueLabels) (htargets : source.targetsExist) :
    PhiBBA.CFG.PhiTargetsDefined (convert source) := by
  intro target hreached
  have hsourceReached : target ∈ source.entry.terminator.targets ∨
      ∃ label block, (label, block) ∈ source.blocks ∧
        target ∈ block.terminator.targets := by
    rcases hreached with hentry | ⟨label, convertedBlock, hblock, ht⟩
    · left
      simpa [convert, cfg, convertBlock, renameTerminator_targets] using hentry
    · rw [show (convert source).blocks = source.blocks.map (fun pair =>
          (pair.1, convertBlock source (sourceVars source) (.named pair.1) pair.2)) by rfl]
        at hblock
      rcases List.mem_map.mp hblock with ⟨pair, hpair, heq⟩
      rcases pair with ⟨sourceLabel, sourceBlock⟩
      simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      exact Or.inr ⟨sourceLabel, sourceBlock, hpair, by
        simpa [convertBlock, renameTerminator_targets] using ht⟩
  obtain ⟨sourceId, hsuccessor⟩ :
      ∃ sourceId, BlockId.named target ∈ source.successors sourceId := by
    rcases hsourceReached with hentry | ⟨label, block, hblock, ht⟩
    · refine ⟨.entry, ?_⟩
      simp [Classical.CFG.successors, Classical.CFG.lookup, hentry]
    · refine ⟨.named label, ?_⟩
      rw [successors_named_of_mem hlabels hblock]
      exact List.mem_map.mpr ⟨target, ht, rfl⟩
  obtain ⟨targetBlock, hlookup⟩ := htargets sourceId _ hsuccessor
  change source.blocks.lookup target = some targetBlock at hlookup
  have htargetMem := mem_of_lookup_eq_some hlookup
  let convertedTarget := convertBlock source (sourceVars source) (.named target) targetBlock
  refine ⟨convertedTarget, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨(target, targetBlock), htargetMem, rfl⟩
  · intro other hother
    rw [show (convert source).blocks = source.blocks.map (fun pair =>
        (pair.1, convertBlock source (sourceVars source) (.named pair.1) pair.2)) by rfl]
      at hother
    rcases List.mem_map.mp hother with ⟨pair, hpair, heq⟩
    rcases pair with ⟨otherLabel, otherBlock⟩
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, heq⟩
    have hotherLookup := lookup_eq_some_of_mem_of_unique hlabels hpair
    rw [hlookup] at hotherLookup
    cases hotherLookup
    exact heq.symm

theorem incoming_predecessors_eq (source : Classical.CFG Var Op Label)
    (hlabels : source.uniqueLabels) (bid : BlockId Label) (x : Var) :
    (incoming source bid x).map Incoming.predecessor = predecessors source bid := by
  unfold incoming
  have aux : ∀ xs : List (BlockId Label),
      (∀ pred, pred ∈ xs → pred ∈ predecessors source bid) →
      (xs.filterMap fun pred => (blockAt source pred).map fun block =>
        (⟨pred, .var (endEnv pred block x)⟩ : Incoming (Version Var Label) Label)).map
          Incoming.predecessor = xs := by
    intro xs hsubset
    induction xs with
    | nil => rfl
    | cons pred tail ih =>
        have hpred := (mem_predecessors source pred bid).1
          (hsubset pred List.mem_cons_self)
        obtain ⟨block, hlookup⟩ : ∃ block, blockAt source pred = some block := by
          rcases hpred.2 with rfl | ⟨label, hlabel, rfl⟩
          · exact ⟨source.entry, rfl⟩
          · rcases List.mem_map.mp hlabel with ⟨pair, hpair, heq⟩
            rcases pair with ⟨foundLabel, foundBlock⟩
            simp only at heq
            subst foundLabel
            exact ⟨foundBlock, lookup_eq_some_of_mem_of_unique hlabels hpair⟩
        simp only [List.filterMap_cons, hlookup, Option.map_some, List.map_cons]
        rw [ih (fun q hq => hsubset q (List.Mem.tail pred hq))]
  exact aux (predecessors source bid) (fun _ h => h)

/-- Canonical conversion satisfies the bridge's independent structural
normalization conditions.  Parallel source/target occurrences are excluded
explicitly because classical phi rows index predecessors rather than edge
occurrences. -/
theorem convert_structurallyNormalized (source : Classical.CFG Var Op Label)
    (hlabels : source.uniqueLabels) (htargets : source.targetsExist)
    (hparallel : (PhiBBA.CFG.phiEdgeKeys source).Nodup) :
    PhiBBA.CFG.PhiStructurallyNormalized (convert source) := by
  refine ⟨rfl, ?_, targetsDefined_convert source hlabels htargets, ?_, ?_⟩
  · simpa [Classical.CFG.labels, convert, cfg, Function.comp_def] using hlabels
  · intro label convertedBlock hconvertedBlock
    rw [show (convert source).blocks = source.blocks.map (fun pair =>
        (pair.1, convertBlock source (sourceVars source) (.named pair.1) pair.2)) by rfl]
      at hconvertedBlock
    rcases List.mem_map.mp hconvertedBlock with ⟨pair, hpair, heq⟩
    rcases pair with ⟨sourceLabel, sourceBlock⟩
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    constructor
    · change ((phis source (sourceVars source) sourceLabel).map Phi.dst).Nodup
      have hvars := sourceVars_nodup source
      simpa [phis] using List.Nodup.map
        (fun _ _ h => (Version.phi.inj h).2) hvars
    · intro phi hphi
      change phi ∈ phis source (sourceVars source) sourceLabel at hphi
      unfold phis at hphi
      rcases List.mem_map.mp hphi with ⟨x, hx, rfl⟩
      have hpred := incoming_predecessors_eq source hlabels
        (.named sourceLabel) x
      have heq := predecessors_eq_phiPredecessors source hlabels sourceLabel
      constructor
      · exact hpred.trans heq
      · rw [hpred]
        exact predecessors_nodup source (.named sourceLabel) hlabels
  · rw [phiEdgeKeys_convert]
    exact hparallel

theorem convert_normalized (source : Classical.CFG Var Op Label)
    (hlabels : source.uniqueLabels) (htargets : source.targetsExist)
    (hparallel : (PhiBBA.CFG.phiEdgeKeys source).Nodup) :
    PhiBBA.CFG.PhiNormalized (convert source) :=
  PhiBBA.CFG.PhiStructurallyNormalized.normalized
    (convert_structurallyNormalized source hlabels htargets hparallel)

/-- Canonical converted SSA is an element of the phi side of the normalized
phi/BBA equivalence. -/
def convertNormalized (source : Classical.CFG Var Op Label)
    (hlabels : source.uniqueLabels) (htargets : source.targetsExist)
    (hparallel : (PhiBBA.CFG.phiEdgeKeys source).Nodup) :
    {cfg : Classical.CFG (Version Var Label) Op Label // PhiBBA.CFG.PhiNormalized cfg} :=
  ⟨convert source, convert_normalized source hlabels htargets hparallel⟩

end Isotope.TAC.Bridge.PhiBBA.Convert
