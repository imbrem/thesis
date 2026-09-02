import Isotope.TAC.Bridge.LambdaSSA
import Isotope.LambdaSSA.Named.ToLocallyNameless
import Isotope.LambdaSSA.LocallyNameless.ToDeBruijn

/-! # Named and locally nameless lexical SSA bridges

The lexical BBA presentation is representation-polymorphic: the named and
locally nameless variants are precisely the corresponding lambda-SSA region
types.  The definitions below make those variants and their comparison maps
explicit without introducing a second, drifting copy of either syntax.
-/

namespace Isotope.TAC.Bridge

universe u v w

/-- Lexical BBA/SSA with named value and block binders. -/
abbrev NamedBBA (ν : Type u) (κ : Type v) (Φ : Type w) :=
  LambdaSSA.Named.Region ν κ Φ

/-- Lexical BBA/SSA with named free variables and labels and locally nameless
bound variables and labels. -/
abbrev LocallyNamelessBBA (ν : Type u) (κ : Type v) (Φ : Type w)
    (n l : Nat) := LambdaSSA.LocallyNameless.Region ν κ Φ n l

namespace NamedBBA

/-- Forget binder names in favour of local indices, retaining unresolved names
as free variables and labels. -/
def toLocallyNameless [DecidableEq ν] [DecidableEq κ]
    (values : LambdaSSA.Named.ToLocallyNameless.Scope ν n)
    (labels : LambdaSSA.Named.ToLocallyNameless.Scope κ l)
    (r : NamedBBA ν κ Φ) : LocallyNamelessBBA ν κ Φ n l :=
  LambdaSSA.Named.ToLocallyNameless.translateRegion values labels r

def toLocallyNamelessClosed [DecidableEq ν] [DecidableEq κ]
    (r : NamedBBA ν κ Φ) : LocallyNamelessBBA ν κ Φ 0 0 :=
  LambdaSSA.Named.ToLocallyNameless.translateRegionClosed r

@[simp] theorem toLocallyNameless_br [DecidableEq ν] [DecidableEq κ]
    (values : LambdaSSA.Named.ToLocallyNameless.Scope ν n)
    (labels : LambdaSSA.Named.ToLocallyNameless.Scope κ l)
    (label : κ) (arg : LambdaSSA.Named.Tm ν Φ) :
    toLocallyNameless values labels (.br label arg) =
      .br (labels.resolve label)
        (LambdaSSA.Named.ToLocallyNameless.translateTm values arg) := rfl

@[simp] theorem toLocallyNameless_cfg [DecidableEq ν] [DecidableEq κ]
    (values : LambdaSSA.Named.ToLocallyNameless.Scope ν n)
    (labels : LambdaSSA.Named.ToLocallyNameless.Scope κ l)
    (entry : NamedBBA ν κ Φ) (arity : Nat)
    (names : Fin arity → LambdaSSA.Named.Binder κ)
    (params : Fin arity → LambdaSSA.Named.Binder ν)
    (blocks : Fin arity → NamedBBA ν κ Φ) :
    toLocallyNameless values labels (.cfg entry arity names params blocks) =
      let labels' := LambdaSSA.Named.ToLocallyNameless.Scope.pushAll names labels
      .cfg arity
        (toLocallyNameless values labels' entry)
        (fun i => toLocallyNameless (.push (params i) values) labels' (blocks i)) := rfl

end NamedBBA

namespace LocallyNamelessBBA

/-- Erase the empty free-variable interfaces of a closed locally nameless BBA.
The result is the de Bruijn lexical BBA used by the TAC bridge. -/
def erase (r : LocallyNamelessBBA Empty Empty Φ n l) : LexicalBBA Φ :=
  LexicalBBA.ofLambdaSSA
    (LambdaSSA.LocallyNameless.ToDeBruijn.eraseRegion r)

@[simp] theorem erase_toLambdaSSA
    (r : LocallyNamelessBBA Empty Empty Φ n l) :
    (erase r).toLambdaSSA =
      LambdaSSA.LocallyNameless.ToDeBruijn.eraseRegion r := by
  simp [erase]

/-- A locally nameless BBA carries a proof that its erased de Bruijn region is
well scoped at the same value and label depths. -/
def scoping (r : LocallyNamelessBBA Empty Empty Φ n l) :
    LambdaSSA.LocallyNameless.ToDeBruijn.Region.Scoped n l
      (LambdaSSA.LocallyNameless.ToDeBruijn.eraseRegion r) :=
  LambdaSSA.LocallyNameless.ToDeBruijn.scopeRegion r

/-- Reconstruct locally nameless syntax from an explicitly scoped de Bruijn
lexical BBA. -/
def embed {r : LexicalBBA Φ}
    (h : LambdaSSA.LocallyNameless.ToDeBruijn.Region.Scoped n l
      r.toLambdaSSA) : LocallyNamelessBBA Empty Empty Φ n l :=
  LambdaSSA.LocallyNameless.ToDeBruijn.embedRegion h

@[simp] theorem erase_embed {r : LexicalBBA Φ}
    (h : LambdaSSA.LocallyNameless.ToDeBruijn.Region.Scoped n l
      r.toLambdaSSA) : erase (embed h) = r := by
  simp [erase, embed]

@[simp] theorem embed_scoping
    (r : LocallyNamelessBBA Empty Empty Φ n l) :
    LambdaSSA.LocallyNameless.ToDeBruijn.embedRegion (scoping r) = r := by
  simp [scoping]

end LocallyNamelessBBA

end Isotope.TAC.Bridge
