/-! # Flat control flow and explicit dominator trees -/

namespace Isotope.TAC.Dominator

universe u

/-- A flat control-flow graph with a distinguished entry block. -/
structure CFG (Label : Type u) where
  entry : Label
  edge : Label → Label → Prop

namespace CFG

variable {Label : Type u} (G : CFG Label)

/-- A nonempty control-flow path, indexed by its endpoints. -/
inductive Path : Label → Label → Type u where
  | nil (a : Label) : Path a a
  | cons {a b c : Label} : G.edge a b → Path b c → Path a c

/-- A block occurs on a path, including either endpoint. -/
inductive Path.Contains (d : Label) : {a b : Label} → G.Path a b → Prop where
  | head {b} (p : G.Path d b) : Contains d p
  | tail {a b c} {e : G.edge a b} {p : G.Path b c} :
      Contains d p → Contains d (.cons e p)

/-- Standard entry-rooted graph dominance. -/
def Dominates (d b : Label) : Prop :=
  ∀ p : G.Path G.entry b, Path.Contains G d p

theorem dominates_entry (b : Label) : Dominates G G.entry b := by
  intro p
  exact .head p

end CFG

/-- Reflexive ancestor closure of an explicit parent function. -/
inductive Ancestor {Label : Type u} (parent : Label → Option Label) :
    Label → Label → Prop where
  | refl (a) : Ancestor parent a a
  | parent {a b c} : parent b = some a → Ancestor parent b c → Ancestor parent a c

/-- Evidence that a chosen parent function is precisely the graph's
dominator tree.  The final field is the choice-independent specification. -/
structure DominatorTree {Label : Type u} (G : CFG Label) where
  parent : Label → Option Label
  entry_root : parent G.entry = none
  parent_edge {b p : Label} : parent b = some p → G.edge p b
  characterizes : ∀ d b, Ancestor parent d b ↔ CFG.Dominates G d b

/-- Two dominator-tree choices agree when they induce the same lexical scope
(ancestor) relation. -/
def DominatorTree.Equivalent {Label : Type u} {G : CFG Label}
    (T U : DominatorTree G) : Prop :=
  ∀ d b, Ancestor T.parent d b ↔ Ancestor U.parent d b

theorem DominatorTree.equivalent_of_spec {Label : Type u} {G : CFG Label}
    (T U : DominatorTree G) : T.Equivalent U := by
  intro d b
  rw [T.characterizes, U.characterizes]

theorem DominatorTree.equivalent_refl {Label : Type u} {G : CFG Label}
    (T : DominatorTree G) : T.Equivalent T := by
  intro d b
  rfl

theorem DominatorTree.equivalent_symm {Label : Type u} {G : CFG Label}
    {T U : DominatorTree G} (h : T.Equivalent U) : U.Equivalent T := by
  intro d b
  exact (h d b).symm

theorem DominatorTree.equivalent_trans {Label : Type u} {G : CFG Label}
    {T U W : DominatorTree G} (hTU : T.Equivalent U) (hUW : U.Equivalent W) :
    T.Equivalent W := by
  intro d b
  exact (hTU d b).trans (hUW d b)

/-- A semantics-independent interface for algorithms choosing a dominator
tree.  Any two successful choices are observationally equivalent by
`equivalent_of_spec`. -/
class HasDominatorTree {Label : Type u} (G : CFG Label) where
  choose : DominatorTree G

end Isotope.TAC.Dominator
