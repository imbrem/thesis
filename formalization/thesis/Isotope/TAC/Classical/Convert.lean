import Isotope.TAC.Classical.WellFormed

/-! # A structurally fresh classical SSA conversion foundation -/

namespace Isotope.TAC.Classical.Convert

universe u v w

open Isotope.TAC.Classical

/-- Versions are generated from syntax sites, never by an assumed fresh-name oracle. -/
inductive Version (Var : Type u) (Label : Type w) where
  | external (source : Var)
  | phi (block : Label) (source : Var)
  | instr (block : BlockId Label) (index slot : Nat) (source : Var)
deriving DecidableEq, Repr

variable {Var : Type u} {Op : Type v} {Label : Type w}

namespace Version

def source : Version Var Label → Var
  | .external x | .phi _ x | .instr _ _ _ x => x

@[simp] theorem source_external (x : Var) : source (.external x : Version Var Label) = x := rfl
@[simp] theorem source_phi (l : Label) (x : Var) : source (.phi l x : Version Var Label) = x := rfl
@[simp] theorem source_instr (b : BlockId Label) (i s : Nat) (x : Var) :
    source (.instr b i s x : Version Var Label) = x := rfl

end Version

abbrev Env (Var : Type u) (Label : Type w) := Var → Version Var Label

def startEnv (bid : BlockId Label) : Env Var Label
  | x => match bid with
    | .entry => .external x
    | .named label => .phi label x

def renameValue (ρ : Env Var Label) : Value Var → Value (Version Var Label)
  | .var x => .var (ρ x)
  | .unit => .unit
  | .pair l r => .pair (renameValue ρ l) (renameValue ρ r)

def renameOperand (ρ : Env Var Label) : Operand Var Op → Operand (Version Var Label) Op
  | .value x => .value (renameValue ρ x)
  | .app f x => .app f (renameValue ρ x)
  | .inl x => .inl (renameValue ρ x)
  | .inr x => .inr (renameValue ρ x)
  | .abort x => .abort (renameValue ρ x)

def renameTerminator (ρ : Env Var Label) :
    Terminator Var Op Label → Terminator (Version Var Label) Op Label
  | .br l => .br l
  | .ret v => .ret (renameValue ρ v)
  | .cond o l r => .cond (renameOperand ρ o)
      (renameTerminator ρ l) (renameTerminator ρ r)

def update (ρ : Env Var Label) [DecidableEq Var] (x : Var)
    (v : Version Var Label) : Env Var Label := fun y => if y = x then v else ρ y

/-- Convert a straight-line body, returning its reaching-version environment. -/
def body [DecidableEq Var] (bid : BlockId Label) :
    Nat → Env Var Label → List (Instr Var Op) →
      List (Instr (Version Var Label) Op) × Env Var Label
  | _, ρ, [] => ([], ρ)
  | i, ρ, .assign x rhs :: tail =>
      let dst := Version.instr bid i 0 x
      let rest := body bid (i + 1) (update ρ x dst) tail
      (.assign dst (renameOperand ρ rhs) :: rest.1, rest.2)
  | i, ρ, .assignPair x y rhs :: tail =>
      let dx := Version.instr bid i 0 x
      let dy := Version.instr bid i 1 y
      let ρ' := update (update ρ x dx) y dy
      let rest := body bid (i + 1) ρ' tail
      (.assignPair dx dy (renameOperand ρ rhs) :: rest.1, rest.2)

def endEnv [DecidableEq Var] (bid : BlockId Label) (b : Block Var Op Label) : Env Var Label :=
  (body bid 0 (startEnv bid) b.body).2

/-- The environment returned by a converted body contains either the incoming
version or a destination actually defined by that converted body. -/
theorem body_end_eq_or_mem [DecidableEq Var] (bid : BlockId Label)
    (i : Nat) (ρ : Env Var Label) (xs : List (Instr Var Op)) (x : Var) :
    (body bid i ρ xs).2 x = ρ x ∨
      (body bid i ρ xs).2 x ∈ (body bid i ρ xs).1.flatMap Instr.defs := by
  induction xs generalizing i ρ with
  | nil => exact .inl rfl
  | cons hd tl ih =>
      cases hd with
      | assign y rhs =>
          let dst := Version.instr bid i 0 y
          rcases ih (i + 1) (update ρ y dst) with h | h
          · by_cases e : x = y
            · subst x
              apply Or.inr
              simp only [body, List.flatMap_cons, List.mem_append]
              apply Or.inl
              simpa [Instr.defs, update, dst] using h
            · exact .inl (by simpa [body, update, e] using h)
          · exact .inr (by simp only [body, List.flatMap_cons, Instr.defs,
              List.mem_append]; exact .inr h)
      | assignPair y z rhs =>
          let dy := Version.instr bid i 0 y
          let dz := Version.instr bid i 1 z
          let ρ' := update (update ρ y dy) z dz
          rcases ih (i + 1) ρ' with h | h
          · by_cases ez : x = z
            · subst x
              apply Or.inr
              simp only [body, List.flatMap_cons, List.mem_append]
              apply Or.inl
              simp only [Instr.defs, List.mem_cons, List.mem_singleton]
              exact Or.inr (by simpa [ρ', update, dz] using h)
            · by_cases ey : x = y
              · subst x
                apply Or.inr
                simp only [body, List.flatMap_cons, List.mem_append]
                apply Or.inl
                simp only [Instr.defs, List.mem_cons, List.mem_singleton]
                exact Or.inl (by simpa [ρ', update, dy, ez] using h)
              · exact .inl (by simpa [body, update, ρ', ez, ey] using h)
          · exact .inr (by simp only [body, List.flatMap_cons, Instr.defs,
              List.mem_append]; exact .inr h)

theorem endEnv_start_or_def [DecidableEq Var] (bid : BlockId Label)
    (b : Block Var Op Label) (x : Var) :
    endEnv bid b x = startEnv bid x ∨
      endEnv bid b x ∈ (body bid 0 (startEnv bid) b.body).1.flatMap Instr.defs :=
  body_end_eq_or_mem bid 0 (startEnv bid) b.body x

def predecessors [DecidableEq Label] (cfg : CFG Var Op Label) (bid : BlockId Label) :
    List (BlockId Label) :=
  .entry :: cfg.labels.map BlockId.named |>.filter fun src => bid ∈ cfg.successors src

def blockAt [DecidableEq Label] (cfg : CFG Var Op Label) (bid : BlockId Label) :
    Option (Block Var Op Label) := cfg.lookup bid

def incoming [DecidableEq Var] [DecidableEq Label] (cfg : CFG Var Op Label)
    (bid : BlockId Label) (x : Var) : List (Incoming (Version Var Label) Label) :=
  (predecessors cfg bid).filterMap fun pred => (blockAt cfg pred).map fun b =>
    ⟨pred, .var (endEnv pred b x)⟩

def phis [DecidableEq Var] [DecidableEq Label] (cfg : CFG Var Op Label)
    (vars : List Var) (label : Label) : List (Phi (Version Var Label) Label) :=
  vars.map fun x => ⟨.phi label x, incoming cfg (.named label) x⟩

def convertBlock [DecidableEq Var] [DecidableEq Label] (cfg : CFG Var Op Label)
    (vars : List Var) (bid : BlockId Label) (b : Block Var Op Label) :
    Block (Version Var Label) Op Label :=
  let converted := body bid 0 (startEnv bid) b.body
  { phis := match bid with | .entry => [] | .named l => phis cfg vars l
    body := converted.1
    terminator := renameTerminator converted.2 b.terminator }

def cfg [DecidableEq Var] [DecidableEq Label] (source : CFG Var Op Label)
    (vars : List Var) : CFG (Version Var Label) Op Label :=
  { entry := convertBlock source vars .entry source.entry
    blocks := source.blocks.map fun p => (p.1, convertBlock source vars (.named p.1) p.2) }

@[simp] theorem renameTerminator_targets (ρ : Env Var Label)
    (t : Terminator Var Op Label) : (renameTerminator ρ t).targets = t.targets := by
  induction t with
  | br => rfl
  | ret => rfl
  | cond o l r il ir => simp [renameTerminator, Terminator.targets, il, ir]

private theorem lookup_map_blocks [DecidableEq Var] [DecidableEq Label]
    (source : CFG Var Op Label) (vars : List Var) (label : Label) :
    ((source.blocks.map fun p =>
      (p.1, convertBlock source vars (.named p.1) p.2)).lookup label) =
      (source.blocks.lookup label).map (convertBlock source vars (.named label)) := by
  induction source.blocks with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.lookup]
      split
      · rename_i h
        have he : label = head.1 := LawfulBEq.eq_of_beq h
        subst label
        simp [h]
      · rename_i h
        simpa [h] using ih

theorem lookup_cfg [DecidableEq Var] [DecidableEq Label]
    (source : CFG Var Op Label) (vars : List Var) (bid : BlockId Label) :
    (cfg source vars).lookup bid =
      (source.lookup bid).map (convertBlock source vars bid) := by
  cases bid with
  | entry => rfl
  | named label => exact lookup_map_blocks source vars label

theorem successors_cfg [DecidableEq Var] [DecidableEq Label]
    (source : CFG Var Op Label) (vars : List Var) (bid : BlockId Label) :
    (cfg source vars).successors bid = source.successors bid := by
  rw [CFG.successors, CFG.successors, lookup_cfg]
  cases h : source.lookup bid with
  | none => simp [h]
  | some b => simp [h, convertBlock]

theorem cfg_uniqueLabels [DecidableEq Var] [DecidableEq Label]
    (source : CFG Var Op Label) (vars : List Var) (h : source.uniqueLabels) :
    (cfg source vars).uniqueLabels := by
  simpa [CFG.uniqueLabels, CFG.labels, cfg, Function.comp_def] using h

theorem cfg_targetsExist [DecidableEq Var] [DecidableEq Label]
    (source : CFG Var Op Label) (vars : List Var) (h : source.targetsExist) :
    (cfg source vars).targetsExist := by
  intro b target ht
  rw [successors_cfg] at ht
  rcases h b target ht with ⟨block, hb⟩
  refine ⟨convertBlock source vars target block, ?_⟩
  rw [lookup_cfg, hb]
  rfl

theorem renameValue_uses_source (ρ : Env Var Label)
    (hρ : ∀ x, (ρ x).source = x) (v : Value Var) :
    (renameValue ρ v).uses.map Version.source = v.uses := by
  induction v with
  | var x => simp [renameValue, Value.uses, hρ]
  | unit => rfl
  | pair l r il ir => simp [renameValue, Value.uses, il, ir]

theorem renameOperand_uses_source (ρ : Env Var Label)
    (hρ : ∀ x, (ρ x).source = x) (o : Operand Var Op) :
    (renameOperand ρ o).uses.map Version.source = o.uses := by
  cases o <;> simp [renameOperand, Operand.uses, renameValue_uses_source ρ hρ]

theorem body_destinations_instr (bid : BlockId Label) [DecidableEq Var]
    (i : Nat) (ρ : Env Var Label) (xs : List (Instr Var Op)) :
    ∀ d ∈ (body bid i ρ xs).1.flatMap Instr.defs,
      ∃ j slot x, d = Version.instr bid j slot x := by
  induction xs generalizing i ρ with
  | nil => simp [body]
  | cons hd tl ih =>
      cases hd <;> simp only [body, List.flatMap_cons, Instr.defs,
        List.mem_append, List.mem_cons, List.not_mem_nil]
      · intro d h
        rcases h with (h | h)
        · rcases h with (h | h)
          · exact ⟨i, 0, _, h⟩
          · contradiction
        · exact ih _ _ d h
      · intro d h
        rcases h with (h | h)
        · rcases h with (h | h)
          · exact ⟨i, 0, _, h⟩
          · rcases h with (h | h)
            · exact ⟨i, 1, _, h⟩
            · contradiction
        · exact ih _ _ d h

theorem body_destination_index_ge (bid : BlockId Label) [DecidableEq Var]
    (i : Nat) (ρ : Env Var Label) (xs : List (Instr Var Op)) :
    ∀ d ∈ (body bid i ρ xs).1.flatMap Instr.defs,
      ∀ j slot x, d = Version.instr bid j slot x → i ≤ j := by
  induction xs generalizing i ρ with
  | nil => simp [body]
  | cons hd tl ih =>
      cases hd <;> simp only [body, List.flatMap_cons, Instr.defs,
        List.mem_append, List.mem_cons, List.not_mem_nil]
      · intro d h j slot x hd
        rcases h with (h | h)
        · rcases h with (h | h)
          · cases h; cases hd; exact Nat.le_refl _
          · contradiction
        · exact Nat.le_trans (Nat.le_add_right i 1) (ih _ _ d h j slot x hd)
      · intro d h j slot x hd
        rcases h with (h | h)
        · rcases h with (h | h)
          · cases h; cases hd; exact Nat.le_refl _
          · rcases h with (h | h)
            · cases h; cases hd; exact Nat.le_refl _
            · contradiction
        · exact Nat.le_trans (Nat.le_add_right i 1) (ih _ _ d h j slot x hd)

theorem body_defs_nodup (bid : BlockId Label) [DecidableEq Var] [DecidableEq Label]
    (i : Nat) (ρ : Env Var Label) (xs : List (Instr Var Op)) :
    ((body bid i ρ xs).1.flatMap Instr.defs).Nodup := by
  induction xs generalizing i ρ with
  | nil => simp [body]
  | cons hd tl ih =>
      cases hd with
      | assign x rhs =>
          simp only [body, List.flatMap_cons, Instr.defs, List.singleton_append]
          apply List.nodup_cons.mpr
          constructor
          · intro h
            rcases body_destinations_instr bid (i + 1) _ _ _ h with ⟨j, s, y, e⟩
            have hj := body_destination_index_ge bid (i + 1) _ _ _ h j s y e
            cases e
            omega
          · exact ih _ _
      | assignPair x y rhs =>
          simp only [body, List.flatMap_cons, Instr.defs, List.cons_append,
            List.singleton_append]
          apply List.nodup_cons.mpr
          constructor
          · simp only [List.mem_cons]
            intro h
            rcases h with (h | h)
            · cases h
            · rcases body_destinations_instr bid (i + 1) _ _ _ h with ⟨j, s, z, e⟩
              have hj := body_destination_index_ge bid (i + 1) _ _ _ h j s z e
              cases e
              omega
          · apply List.nodup_cons.mpr
            constructor
            · intro h
              rcases body_destinations_instr bid (i + 1) _ _ _ h with ⟨j, s, z, e⟩
              have hj := body_destination_index_ge bid (i + 1) _ _ _ h j s z e
              cases e
              omega
            · exact ih _ _
theorem phi_destinations_source [DecidableEq Var] [DecidableEq Label]
    (source : CFG Var Op Label) (vars : List Var) (label : Label) :
    (phis source vars label).map (fun p => p.dst.source) = vars := by
  unfold phis
  rw [List.map_map]
  simpa [Function.comp_def, Version.source]

def Version.owner : Version Var Label → Option (BlockId Label)
  | .external _ => none
  | .phi l _ => some (.named l)
  | .instr b _ _ _ => some b

@[simp] theorem body_destination_owner (bid : BlockId Label) [DecidableEq Var]
    (i : Nat) (ρ : Env Var Label) (xs : List (Instr Var Op))
    {d : Version Var Label} (h : d ∈ (body bid i ρ xs).1.flatMap Instr.defs) :
    d.owner = some bid := by
  rcases body_destinations_instr bid i ρ xs d h with ⟨j, s, x, rfl⟩
  rfl

theorem phi_defs_nodup [DecidableEq Var] [DecidableEq Label]
    (source : CFG Var Op Label) {vars : List Var} (hvars : vars.Nodup)
    (label : Label) : ((phis source vars label).map Phi.dst).Nodup := by
  unfold phis
  rw [List.map_map]
  change (vars.map (Version.phi label)).Nodup
  induction vars with
  | nil => simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hvars
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih hvars.2⟩
      intro h
      rcases List.mem_map.mp h with ⟨y, hy, eq⟩
      exact hvars.1 ((Version.phi.inj eq).2 ▸ hy)

theorem convertedBlock_defs_nodup [DecidableEq Var] [DecidableEq Label]
    (source : CFG Var Op Label) {vars : List Var} (hvars : vars.Nodup)
    (bid : BlockId Label) (b : Block Var Op Label) :
    (CFG.defs (convertBlock source vars bid b)).Nodup := by
  cases bid with
  | entry => simpa [convertBlock, CFG.defs, CFG.instrDefs] using
      body_defs_nodup (.entry : BlockId Label) 0 (startEnv .entry) b.body
  | named label =>
      rw [show CFG.defs (convertBlock source vars (.named label) b) =
        (phis source vars label).map Phi.dst ++
          (body (.named label) 0 (startEnv (.named label)) b.body).1.flatMap Instr.defs by
            rfl]
      rw [List.nodup_append]
      refine ⟨phi_defs_nodup source hvars label,
        body_defs_nodup (.named label) 0 (startEnv (.named label)) b.body, ?_⟩
      intro p hp d hd eq
      unfold phis at hp
      rw [List.mem_map] at hp
      rcases hp with ⟨q, hq, rfl⟩
      rcases List.mem_map.mp hq with ⟨x, _, rfl⟩
      rcases body_destinations_instr (.named label) 0
        (startEnv (.named label)) b.body d hd with ⟨j, s, y, ed⟩
      cases ed
      cases eq

theorem external_not_convertedBlock_def [DecidableEq Var] [DecidableEq Label]
    (source : CFG Var Op Label) (vars : List Var) (bid : BlockId Label)
    (b : Block Var Op Label) (x : Var) :
    Version.external x ∉ CFG.defs (convertBlock source vars bid b) := by
  cases bid with
  | entry =>
      intro h
      have := body_destination_owner (.entry : BlockId Label) 0 (startEnv .entry) b.body h
      contradiction
  | named label =>
      simp only [convertBlock, CFG.defs, CFG.instrDefs, List.mem_append,
        List.mem_map]
      intro h
      rcases h with h | h
      · rcases h with ⟨p, hp, eq⟩
        unfold phis at hp
        rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
        cases eq
      · have := body_destination_owner (.named label) 0 (startEnv (.named label)) b.body h
        contradiction

@[simp] theorem convertedBlock_def_owner [DecidableEq Var] [DecidableEq Label]
    (source : CFG Var Op Label) (vars : List Var) (bid : BlockId Label)
    (b : Block Var Op Label) {d : Version Var Label}
    (h : d ∈ CFG.defs (convertBlock source vars bid b)) : d.owner = some bid := by
  cases bid with
  | entry => exact body_destination_owner .entry 0 (startEnv .entry) b.body h
  | named label =>
      change d ∈ (phis source vars label).map Phi.dst ++
        (body (.named label) 0 (startEnv (.named label)) b.body).1.flatMap Instr.defs at h
      rcases List.mem_append.mp h with h | h
      · unfold phis at h
        rcases List.mem_map.mp h with ⟨p, hp, rfl⟩
        rcases List.mem_map.mp hp with ⟨x, _, rfl⟩
        rfl
      · exact body_destination_owner (.named label) 0 (startEnv (.named label)) b.body h

private def blockDefs [DecidableEq Var] [DecidableEq Label]
    (source : CFG Var Op Label) (vars : List Var)
    (blocks : List (Label × Block Var Op Label)) : List (Version Var Label) :=
  blocks.flatMap fun p => CFG.defs (convertBlock source vars (.named p.1) p.2)

private theorem blockDefs_nodup [DecidableEq Var] [DecidableEq Label]
    (source : CFG Var Op Label) {vars : List Var} (hvars : vars.Nodup)
    (blocks : List (Label × Block Var Op Label))
    (hlabels : (blocks.map Prod.fst).Nodup) :
    (blockDefs source vars blocks).Nodup := by
  induction blocks with
  | nil => simp [blockDefs]
  | cons head tail ih =>
      rw [List.map_cons, List.nodup_cons] at hlabels
      rw [show blockDefs source vars (head :: tail) =
        CFG.defs (convertBlock source vars (.named head.1) head.2) ++
          blockDefs source vars tail by rfl, List.nodup_append]
      refine ⟨convertedBlock_defs_nodup source hvars _ _, ih hlabels.2, ?_⟩
      intro a ha b hb eq
      have hoa := convertedBlock_def_owner source vars (.named head.1) head.2 ha
      rcases List.mem_flatMap.mp hb with ⟨p, hp, hbp⟩
      have hob := convertedBlock_def_owner source vars (.named p.1) p.2 hbp
      subst b
      rw [hoa] at hob
      have hl : head.1 = p.1 := BlockId.named.inj (Option.some.inj hob)
      exact hlabels.1 (List.mem_map.mpr ⟨p, hp, hl.symm⟩)

/-- Site tagging makes the complete converted flat CFG globally single-assignment. -/
theorem cfg_singleAssignment [DecidableEq Var] [DecidableEq Label]
    (source : CFG Var Op Label) {vars : List Var} (hvars : vars.Nodup)
    (hlabels : source.uniqueLabels) : (cfg source vars).singleAssignment := by
  unfold CFG.singleAssignment
  rw [show CFG.allDefs (cfg source vars) =
    CFG.defs (convertBlock source vars .entry source.entry) ++
      blockDefs source vars source.blocks by
        unfold cfg CFG.allDefs blockDefs
        rw [List.flatMap_map], List.nodup_append]
  refine ⟨convertedBlock_defs_nodup source hvars .entry source.entry,
    blockDefs_nodup source hvars source.blocks hlabels, ?_⟩
  intro a ha b hb eq
  have hoa := convertedBlock_def_owner source vars .entry source.entry ha
  rcases List.mem_flatMap.mp hb with ⟨p, hp, hbp⟩
  have hob := convertedBlock_def_owner source vars (.named p.1) p.2 hbp
  subst b
  rw [hoa] at hob
  cases Option.some.inj hob.symm

theorem external_not_cfg_def [DecidableEq Var] [DecidableEq Label]
    (source : CFG Var Op Label) (vars : List Var) (x : Var) :
    Version.external x ∉ CFG.allDefs (cfg source vars) := by
  intro h
  rw [show CFG.allDefs (cfg source vars) =
    CFG.defs (convertBlock source vars .entry source.entry) ++
      blockDefs source vars source.blocks by
        unfold cfg CFG.allDefs blockDefs
        rw [List.flatMap_map]] at h
  rcases List.mem_append.mp h with h | h
  · exact external_not_convertedBlock_def source vars .entry source.entry x h
  · rcases List.mem_flatMap.mp h with ⟨p, hp, hd⟩
    exact external_not_convertedBlock_def source vars (.named p.1) p.2 x hd

def instrSourceVars (i : Instr Var Op) : List Var := i.defs ++ i.uses

def phiSourceVars (p : Phi Var Label) : List Var :=
  p.dst :: p.incoming.flatMap fun i => i.value.uses

def blockSourceVars (b : Block Var Op Label) : List Var :=
  b.phis.flatMap phiSourceVars ++ b.body.flatMap instrSourceVars ++ b.terminator.uses

private def dedup [DecidableEq α] : (xs : List α) → {ys : List α // ys.Nodup}
  | [] => ⟨[], by simp⟩
  | x :: xs =>
      let tail := dedup xs
      if h : x ∈ tail.1 then tail else ⟨x :: tail.1, List.nodup_cons.mpr ⟨h, tail.2⟩⟩

private theorem mem_dedup [DecidableEq α] (x : α) (xs : List α) :
    x ∈ (dedup xs).1 ↔ x ∈ xs := by
  induction xs generalizing x with
  | nil => simp [dedup]
  | cons y ys ih =>
      simp only [dedup]
      split <;> simp_all

/-- The finite source-variable universe mentioned anywhere in the input CFG. -/
def sourceVars [DecidableEq Var] (source : CFG Var Op Label) : List Var :=
  (dedup (blockSourceVars source.entry ++
    source.blocks.flatMap fun p => blockSourceVars p.2)).1

theorem sourceVars_nodup [DecidableEq Var] (source : CFG Var Op Label) :
    (sourceVars source).Nodup :=
  (dedup (blockSourceVars source.entry ++
    source.blocks.flatMap fun p => blockSourceVars p.2)).2

theorem mem_sourceVars [DecidableEq Var] (source : CFG Var Op Label) (x : Var) :
    x ∈ sourceVars source ↔
      x ∈ blockSourceVars source.entry ∨
        ∃ p ∈ source.blocks, x ∈ blockSourceVars p.2 := by
  rw [sourceVars, mem_dedup, List.mem_append, List.mem_flatMap]

theorem instr_use_mem_blockSourceVars [DecidableEq Var]
    (b : Block Var Op Label) {i : Instr Var Op} (hi : i ∈ b.body)
    {x : Var} (hx : x ∈ i.uses) : x ∈ blockSourceVars b := by
  unfold blockSourceVars instrSourceVars
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨i, hi, List.mem_append_right _ hx⟩

theorem terminator_use_mem_blockSourceVars (b : Block Var Op Label)
    {x : Var} (hx : x ∈ b.terminator.uses) : x ∈ blockSourceVars b := by
  exact List.mem_append_right _ hx

theorem entry_use_mem_sourceVars [DecidableEq Var] (source : CFG Var Op Label)
    {i : Instr Var Op} (hi : i ∈ source.entry.body) {x : Var} (hx : x ∈ i.uses) :
    x ∈ sourceVars source :=
  (mem_sourceVars source x).2 (.inl (instr_use_mem_blockSourceVars source.entry hi hx))

theorem block_use_mem_sourceVars [DecidableEq Var] (source : CFG Var Op Label)
    {label : Label} {b : Block Var Op Label} (hb : (label, b) ∈ source.blocks)
    {i : Instr Var Op} (hi : i ∈ b.body) {x : Var} (hx : x ∈ i.uses) :
    x ∈ sourceVars source :=
  (mem_sourceVars source x).2 (.inr ⟨(label, b), hb,
    instr_use_mem_blockSourceVars b hi hx⟩)

/-- Canonical total-environment conversion using all variables mentioned by the source. -/
def convert [DecidableEq Var] [DecidableEq Label] (source : CFG Var Op Label) :
    CFG (Version Var Label) Op Label := cfg source (sourceVars source)

theorem convert_singleAssignment [DecidableEq Var] [DecidableEq Label]
    (source : CFG Var Op Label) (hlabels : source.uniqueLabels) :
    (convert source).singleAssignment :=
  cfg_singleAssignment source (sourceVars_nodup source) hlabels

theorem external_not_convert_def [DecidableEq Var] [DecidableEq Label]
    (source : CFG Var Op Label) (x : Var) :
    Version.external x ∉ CFG.allDefs (convert source) :=
  external_not_cfg_def source (sourceVars source) x

end Isotope.TAC.Classical.Convert
