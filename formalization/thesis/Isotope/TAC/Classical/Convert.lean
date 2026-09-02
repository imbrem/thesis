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

theorem phi_destinations_source [DecidableEq Var] [DecidableEq Label]
    (source : CFG Var Op Label) (vars : List Var) (label : Label) :
    (phis source vars label).map (fun p => p.dst.source) = vars := by
  unfold phis
  rw [List.map_map]
  simpa [Function.comp_def, Version.source]

end Isotope.TAC.Classical.Convert
