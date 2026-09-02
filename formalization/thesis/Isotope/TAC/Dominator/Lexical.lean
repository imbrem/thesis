import Isotope.TAC.Dominator.Foundation
import Isotope.LambdaSSA.Syntax

/-! # Relating flat dominance and lexical lambda-SSA regions -/

namespace Isotope.TAC.Dominator

universe u v w

/-- Syntax-level data chosen when a flat, labelled CFG is organized as a
lexically scoped lambda-SSA region.  The erasure function is explicit because
the existing de Bruijn region syntax intentionally carries no block names. -/
structure LexicalOrganization (Label : Type u) (Φ : Type v)
    (erase : LambdaSSA.Region Φ → CFG Label)
    (G : CFG Label) (T : DominatorTree G) (r : LambdaSSA.Region Φ) where
  lexicalScope : Label → Label → Prop
  erases : erase r = G
  scope_iff_ancestor : ∀ d b, lexicalScope d b ↔ Ancestor T.parent d b

/-- Relational organization hides the particular lexical-scope predicate but
retains the explicit erasure and dominator witness. -/
def Organizes {Label : Type u} {Φ : Type v}
    (erase : LambdaSSA.Region Φ → CFG Label)
    (G : CFG Label) (T : DominatorTree G) (r : LambdaSSA.Region Φ) : Prop :=
  Nonempty (LexicalOrganization Label Φ erase G T r)

theorem LexicalOrganization.scope_iff_dominates
    {Label : Type u} {Φ : Type v}
    {erase : LambdaSSA.Region Φ → CFG Label}
    {G : CFG Label} {T : DominatorTree G} {r : LambdaSSA.Region Φ}
    (o : LexicalOrganization Label Φ erase G T r) (d b : Label) :
    o.lexicalScope d b ↔ CFG.Dominates G d b := by
  rw [o.scope_iff_ancestor, T.characterizes]

/-- Any two organizations of the same erased region, possibly using different
valid dominator-tree choices, induce extensionally identical lexical scope. -/
theorem LexicalOrganization.scope_choice_independent
    {Label : Type u} {Φ : Type v}
    {erase : LambdaSSA.Region Φ → CFG Label}
    {G : CFG Label} {T U : DominatorTree G} {r : LambdaSSA.Region Φ}
    (oT : LexicalOrganization Label Φ erase G T r)
    (oU : LexicalOrganization Label Φ erase G U r) :
    ∀ d b, oT.lexicalScope d b ↔ oU.lexicalScope d b := by
  intro d b
  rw [oT.scope_iff_dominates, oU.scope_iff_dominates]

/-- The erasure component of an organization is independent of its tree
choice. -/
theorem LexicalOrganization.erasure_unique
    {Label : Type u} {Φ : Type v}
    {erase : LambdaSSA.Region Φ → CFG Label}
    {G : CFG Label} {T U : DominatorTree G} {r : LambdaSSA.Region Φ}
    (oT : LexicalOrganization Label Φ erase G T r)
    (oU : LexicalOrganization Label Φ erase G U r) :
    oT.erases = oU.erases := by
  apply Subsingleton.elim

/-- A syntax-independent choice interface packages both a dominator tree and
one lexical organization of the region. -/
structure OrganizedRegion (Label : Type u) (Φ : Type v)
    (erase : LambdaSSA.Region Φ → CFG Label) (r : LambdaSSA.Region Φ) where
  tree : DominatorTree (erase r)
  organization : LexicalOrganization Label Φ erase (erase r) tree r

end Isotope.TAC.Dominator
