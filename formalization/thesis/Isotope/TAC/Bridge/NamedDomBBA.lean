import Isotope.TAC.Bridge.NamedLN
import Isotope.TAC.Bridge.ActualDomBBA

/-!
# Named and locally nameless presentations of actual dominator BBAs

This module connects the representation comparison maps to the paper's
entry/dominator decomposition and its lowering to an actual flat BBA.  Named
syntax is related through alpha-equivalence (equality after translation to
locally nameless syntax), rather than by claiming a syntactic inverse.
-/

namespace Isotope.TAC.Bridge.NamedDomBBA

open Isotope
open Isotope.TAC.Bridge

universe u v w

/-- Change only the free-variable interface of locally nameless terms. -/
def mapFreeTm (values : ν → ν') :
    {n : Nat} → Isotope.LambdaSSA.LocallyNameless.Tm ν Φ n →
      Isotope.LambdaSSA.LocallyNameless.Tm ν' Φ n
  | _, .fv x => .fv (values x)
  | _, .bv i => .bv i
  | _, .op f a => .op f (mapFreeTm values a)
  | _, .let₁ a b => .let₁ (mapFreeTm values a) (mapFreeTm values b)
  | _, .pair a b => .pair (mapFreeTm values a) (mapFreeTm values b)
  | _, .unit => .unit
  | _, .let₂ a b => .let₂ (mapFreeTm values a) (mapFreeTm values b)
  | _, .inl a => .inl (mapFreeTm values a)
  | _, .inr a => .inr (mapFreeTm values a)
  | _, .case e left right =>
      .case (mapFreeTm values e) (mapFreeTm values left) (mapFreeTm values right)
  | _, .abort a => .abort (mapFreeTm values a)

/-- Change the free value and label interfaces of a locally nameless region,
leaving every bound index untouched. -/
def mapFreeRegion (values : ν → ν') (labels : κ → κ') :
    {n l : Nat} → Isotope.LambdaSSA.LocallyNameless.Region ν κ Φ n l →
      Isotope.LambdaSSA.LocallyNameless.Region ν' κ' Φ n l
  | _, _, .br (.inl i) arg => .br (.inl i) (mapFreeTm values arg)
  | _, _, .br (.inr label) arg => .br (.inr (labels label)) (mapFreeTm values arg)
  | _, _, .case discr left right =>
      .case (mapFreeTm values discr)
        (mapFreeRegion values labels left) (mapFreeRegion values labels right)
  | _, _, .let₁ value body =>
      .let₁ (mapFreeTm values value) (mapFreeRegion values labels body)
  | _, _, .let₂ value body =>
      .let₂ (mapFreeTm values value) (mapFreeRegion values labels body)
  | _, _, .cfg arity entry blocks =>
      .cfg arity (mapFreeRegion values labels entry)
        (fun i => mapFreeRegion values labels (blocks i))

namespace LocallyNameless

/-- A locally nameless region presents a dominator tree when erasing its empty
free interfaces gives the region assembled by that tree. -/
structure Presents (r : LocallyNamelessBBA Empty Empty Φ n l)
    (tree : LambdaSSA.DomTree Φ) : Prop where
  addDom_eq : tree.addDom =
    Isotope.LambdaSSA.LocallyNameless.ToDeBruijn.eraseRegion r

/-- A proof-relevant decomposition supplies the corresponding presentation. -/
def presentsOfDecomposition (r : LocallyNamelessBBA Empty Empty Φ n l)
    (parsed : LambdaSSA.Decomposition
      (Isotope.LambdaSSA.LocallyNameless.ToDeBruijn.eraseRegion r)) :
    Presents r parsed.tree :=
  ⟨parsed.addDom_tree⟩

/-- Lower a locally nameless presentation through its explicit dominator
tree to the paper's actual flat block-with-arguments CFG. -/
noncomputable def toActualCFG (_r : LocallyNamelessBBA Empty Empty Φ n l)
    (tree : LambdaSSA.DomTree Φ) (_h : Presents _r tree) :
    PhiBBA.CFG (ActualDomBBA.Var Φ) (ActualDomBBA.Op Φ) ActualDomBBA.Address :=
  ActualDomBBA.LexicalDomTree.toActualCFG tree

/-- The locally nameless-to-flat square factors through de Bruijn erasure and
the `toEntry`/`toDom` decomposition. -/
@[simp] theorem toActualCFG_ofDecomposition
    (r : LocallyNamelessBBA Empty Empty Φ n l)
    (parsed : LambdaSSA.Decomposition
      (Isotope.LambdaSSA.LocallyNameless.ToDeBruijn.eraseRegion r)) :
    toActualCFG r parsed.tree (presentsOfDecomposition r parsed) =
      ActualDomBBA.LexicalDomTree.toActualCFG parsed.tree := rfl

/-- The scoped locally nameless representation itself round-trips exactly;
the flat lowering therefore forgets representation only after this exact
comparison map. -/
@[simp] theorem scoped_roundTrip (r : LocallyNamelessBBA Empty Empty Φ n l) :
    Isotope.LambdaSSA.LocallyNameless.ToDeBruijn.embedRegion
      (LocallyNamelessBBA.scoping r) = r :=
  LocallyNamelessBBA.embed_scoping r

end LocallyNameless

namespace Named

/-- Alpha-equivalence for named lexical SSA: binder spelling is forgotten by
the standard translation to locally nameless syntax. -/
def AlphaEq [DecidableEq ν] [DecidableEq κ]
    (left right : NamedBBA ν κ Φ) : Prop :=
  NamedBBA.toLocallyNamelessClosed left =
    NamedBBA.toLocallyNamelessClosed right

@[refl] theorem AlphaEq.refl [DecidableEq ν] [DecidableEq κ]
    (r : NamedBBA ν κ Φ) : AlphaEq r r := rfl

@[symm] theorem AlphaEq.symm [DecidableEq ν] [DecidableEq κ]
    {left right : NamedBBA ν κ Φ} (h : AlphaEq left right) :
    AlphaEq right left := Eq.symm h

@[trans] theorem AlphaEq.trans [DecidableEq ν] [DecidableEq κ]
    {first second third : NamedBBA ν κ Φ}
    (h₁ : AlphaEq first second) (h₂ : AlphaEq second third) :
    AlphaEq first third := Eq.trans h₁ h₂

/-- A named region presents a dominator tree after alpha-erasure.  The
locally nameless representative is explicit, so no false named syntactic
inverse is asserted. -/
structure Presentation [DecidableEq ν] [DecidableEq κ]
    (r : NamedBBA ν κ Φ) (tree : LambdaSSA.DomTree Φ) where
  representative : LocallyNamelessBBA Empty Empty Φ 0 0
  named_eq : NamedBBA.toLocallyNamelessClosed r =
    mapFreeRegion Empty.elim Empty.elim representative
  addDom_eq : tree.addDom =
    Isotope.LambdaSSA.LocallyNameless.ToDeBruijn.eraseRegion representative

/-- Build the named comparison triangle from the standard named-to-locally
nameless translation, a closed representative, and the paper's proof-relevant
decomposition. -/
def presentationOfDecomposition [DecidableEq ν] [DecidableEq κ]
    (r : NamedBBA ν κ Φ)
    (representative : LocallyNamelessBBA Empty Empty Φ 0 0)
    (named_eq : NamedBBA.toLocallyNamelessClosed r =
      mapFreeRegion Empty.elim Empty.elim representative)
    (parsed : LambdaSSA.Decomposition
      (Isotope.LambdaSSA.LocallyNameless.ToDeBruijn.eraseRegion representative)) :
    Presentation r parsed.tree where
  representative := representative
  named_eq := named_eq
  addDom_eq := parsed.addDom_tree

/-- Alpha-equivalent named programs have exactly the same locally nameless
presentation and hence may use the same dominator tree. -/
def Presentation.ofAlphaEq [DecidableEq ν] [DecidableEq κ]
    {left right : NamedBBA ν κ Φ} {tree : LambdaSSA.DomTree Φ}
    (hα : AlphaEq left right) (presentation : Presentation left tree) :
    Presentation right tree where
  representative := presentation.representative
  named_eq := Eq.trans (Eq.symm hα) presentation.named_eq
  addDom_eq := presentation.addDom_eq

/-- Lower a named presentation to the actual flat BBA determined by its
alpha-invariant dominator-tree representative. -/
noncomputable def Presentation.toActualCFG [DecidableEq ν] [DecidableEq κ]
    {r : NamedBBA ν κ Φ} {tree : LambdaSSA.DomTree Φ}
    (_presentation : Presentation r tree) :
    PhiBBA.CFG (ActualDomBBA.Var Φ) (ActualDomBBA.Op Φ) ActualDomBBA.Address :=
  ActualDomBBA.LexicalDomTree.toActualCFG tree

/-- The actual lowering is unchanged when a presentation is transported
across named alpha-equivalence. -/
@[simp] theorem Presentation.toActualCFG_ofAlphaEq
    [DecidableEq ν] [DecidableEq κ]
    {left right : NamedBBA ν κ Φ} {tree : LambdaSSA.DomTree Φ}
    (hα : AlphaEq left right) (presentation : Presentation left tree) :
    (presentation.ofAlphaEq hα).toActualCFG = presentation.toActualCFG := rfl

/-- The named-to-flat diagram commutes through the explicit closed locally
nameless representative and its `toEntry`/`toDom` decomposition. -/
@[simp] theorem Presentation.toActualCFG_eq
    [DecidableEq ν] [DecidableEq κ]
    {r : NamedBBA ν κ Φ} {tree : LambdaSSA.DomTree Φ}
    (presentation : Presentation r tree) :
    presentation.toActualCFG =
      ActualDomBBA.LexicalDomTree.toActualCFG tree := rfl

end Named

end Isotope.TAC.Bridge.NamedDomBBA
