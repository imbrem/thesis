import Isotope.TAC.Bridge.ActualDomBBA
import Isotope.Elgot.Basic

/-! # Block-order invariant semantics of flat BBA control -/

namespace Isotope.TAC.Densem.BBAOrder

open Isotope.TAC.Bridge.PhiBBA
open Isotope.Elgot

universe u v w

variable {Var : Type v} {Op : Type w} {Label : Type u} {m : Type u → Type u}

def lookup [DecidableEq Label] (blocks : List (Label × Block Var Op Label))
    (label : Label) : Option (Block Var Op Label) :=
  (blocks.find? fun p => p.1 = label).map Prod.snd

private theorem lookup_perm [DecidableEq Label]
    {left right : List (Label × Block Var Op Label)}
    (hp : left.Perm right) (hl : (left.map Prod.fst).Nodup)
    (hr : (right.map Prod.fst).Nodup) (label : Label) :
    lookup left label = lookup right label := by
  induction hp with
  | nil => rfl
  | @cons pair left right hp ih =>
      simp only [List.map_cons, List.nodup_cons] at hl hr
      simp only [lookup, List.find?_cons]
      split
      · rfl
      · exact ih hl.2 hr.2
  | @swap first second tail =>
      simp only [List.map_cons, List.nodup_cons] at hl hr
      simp only [lookup, List.find?_cons]
      by_cases hf : first.1 = label
      · have hs : ¬second.1 = label := by
          intro hs
          apply hl.1
          simp [hf, hs]
        simp [hf, hs]
      · simp [hf]
  | @trans left middle right hp hq ihp ihq =>
      have hm : (middle.map Prod.fst).Nodup :=
        (hp.map Prod.fst).nodup_iff.mp hl
      exact (ihp hl hm).trans (ihq hm hr)

/-- A semantics for already-entered blocks.  It abstracts from instruction
details while retaining the complete-Elgot control semantics. -/
structure Model (Var : Type v) (Op : Type w) (Label : Type u)
    (m : Type u → Type u) where
  State : Type u
  Result : Type u
  run : Block Var Op Label → State → m (Result ⊕ (State × Label))

-- Missing labels are supplied explicitly, so this semantics does not impose
-- a distinguished failure effect on the ambient monad.
def stepWith [Monad m] [DecidableEq Label]
    (M : Model Var Op Label m) (missing : m (M.Result ⊕ (M.State × Label)))
    (cfg : CFG Var Op Label) : M.State × Label → m (M.Result ⊕ (M.State × Label))
  | (state, label) =>
      match lookup cfg.blocks label with
      | some block => M.run block state
      | none => missing

def denoteWith [Monad m] [Iterate m] [DecidableEq Label]
    (M : Model Var Op Label m) (missing : m (M.Result ⊕ (M.State × Label)))
    (cfg : CFG Var Op Label) (initial : M.State) : m M.Result := do
  match ← M.run cfg.entry initial with
  | .inl result => pure result
  | .inr next => iter (stepWith M missing cfg) next

theorem stepWith_eq_of_perm [Monad m] [DecidableEq Label]
    (M : Model Var Op Label m) (missing : m (M.Result ⊕ (M.State × Label)))
    {left right : CFG Var Op Label}
    (hp : left.blocks.Perm right.blocks)
    (hl : (left.blocks.map Prod.fst).Nodup)
    (hr : (right.blocks.map Prod.fst).Nodup) :
    stepWith M missing left = stepWith M missing right := by
  funext state
  cases state with
  | mk state label => simp [stepWith, lookup_perm hp hl hr label]

theorem denoteWith_eq_of_perm [Monad m] [Iterate m] [DecidableEq Label]
    (M : Model Var Op Label m) (missing : m (M.Result ⊕ (M.State × Label)))
    {left right : CFG Var Op Label}
    (hentry : left.entry = right.entry)
    (hp : left.blocks.Perm right.blocks)
    (hl : (left.blocks.map Prod.fst).Nodup)
    (hr : (right.blocks.map Prod.fst).Nodup) (initial : M.State) :
    denoteWith M missing left initial = denoteWith M missing right initial := by
  unfold denoteWith
  rw [hentry, stepWith_eq_of_perm M missing hp hl hr]

namespace ActualChoice

namespace A
abbrev AVar := Isotope.TAC.Bridge.ActualDomBBA.Var
abbrev AOp := Isotope.TAC.Bridge.ActualDomBBA.Op
abbrev Address := Isotope.TAC.Bridge.ActualDomBBA.Address
abbrev DominanceWellFormed {Φ : Type u}
    (cfg : CFG (AVar Φ) (AOp Φ) Address) :=
  Isotope.TAC.Bridge.ActualDomBBA.LexicalDomTree.DominanceWellFormed cfg
noncomputable abbrev toActualCFG {Φ : Type u} :=
  Isotope.TAC.Bridge.ActualDomBBA.LexicalDomTree.toActualCFG (Phi := Φ)
end A

/-- Flat monadic control semantics of one checked dominator-tree choice. -/
noncomputable def denote {m : Type → Type} [Monad m] [Iterate m]
    (M : Model (A.AVar Φ) (A.AOp Φ) A.Address m)
    (missing : m (M.Result ⊕ (M.State × A.Address)))
    {cfg : CFG (A.AVar Φ) (A.AOp Φ) A.Address}
    (choice : A.DominanceWellFormed cfg)
    (initial : M.State) : m M.Result :=
  denoteWith M missing
    (A.toActualCFG choice.toReg) initial

/-- The denotation of a choice agrees with the original flat CFG; the proof
uses the address decoder's exact target agreement and only quotients textual
block order. -/
theorem denote_eq_cfg {m : Type → Type} [Monad m] [Iterate m]
    (M : Model (A.AVar Φ) (A.AOp Φ) A.Address m)
    (missing : m (M.Result ⊕ (M.State × A.Address)))
    {cfg : CFG (A.AVar Φ) (A.AOp Φ) A.Address}
    (choice : A.DominanceWellFormed cfg)
    (hcfg : (cfg.blocks.map Prod.fst).Nodup) (initial : M.State) :
    denote M missing choice initial = denoteWith M missing cfg initial := by
  have h := Isotope.TAC.Bridge.ActualDomBBA.LexicalDomTree.DominanceWellFormed.toCFG_toReg choice
  have hleft : ((A.toActualCFG choice.toReg).blocks.map
      Prod.fst).Nodup := (h.2.map Prod.fst).nodup_iff.mpr hcfg
  exact denoteWith_eq_of_perm M missing h.1 h.2 hleft hcfg initial

/-- Two independently checked dominator choices for the same uniquely labelled
flat CFG have exactly the same complete-Elgot denotation. -/
theorem denote_choice_irrelevant {m : Type → Type} [Monad m] [Iterate m]
    (M : Model (A.AVar Φ) (A.AOp Φ) A.Address m)
    (missing : m (M.Result ⊕ (M.State × A.Address)))
    {cfg : CFG (A.AVar Φ) (A.AOp Φ) A.Address}
    (left right : A.DominanceWellFormed cfg)
    (hcfg : (cfg.blocks.map Prod.fst).Nodup) (initial : M.State) :
    denote M missing left initial = denote M missing right initial := by
  rw [denote_eq_cfg M missing left hcfg initial,
    denote_eq_cfg M missing right hcfg initial]

end ActualChoice

end Isotope.TAC.Densem.BBAOrder
