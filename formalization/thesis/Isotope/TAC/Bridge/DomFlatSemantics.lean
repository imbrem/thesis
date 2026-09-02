import Isotope.TAC.Bridge.TypedDomFlat
import Isotope.LambdaSSA.Semantics

/-! # Semantics of a flat CFG with a dominator-tree choice -/

namespace Isotope.TAC.Bridge.LambdaSSA

open Isotope.LambdaSSA

universe u v q r v₁ v₂ u₁ u₂

variable {Φ : Type q} {τ : Type u}
variable [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
variable [LambdaIter.HasTy Φ τ]
variable {Γ : VCtx τ} {L : LCtx τ}

/-- A dominance-well-formed flat CFG whose chosen lexicalization is typed.
The typing witness belongs to the tree, rather than to an accidentally chosen
linear order of the erased block collection. -/
structure TypedDominanceWellFormedFlat (Γ : VCtx τ) (L : LCtx τ) where
  flat : DominanceWellFormedFlat Φ
  typed : DomTree.HasType (Phi := Φ) (Ty := τ) Γ flat.tree L

namespace TypedDominanceWellFormedFlat

def region (program : TypedDominanceWellFormedFlat (Φ := Φ) Γ L) : Region Φ :=
  program.flat.toLambdaSSA

def regionHasType (program : TypedDominanceWellFormedFlat (Φ := Φ) Γ L) :
    Region.HasType Γ program.region L :=
  DomTree.addDom_hasType program.typed

/-- The missing congruence needed in addition to permutation of the erased
block list: the two choices must present the same lexical program, including
the coordinated reindexing of every branch target. -/
def LexicallyCongruent
    (left right : TypedDominanceWellFormedFlat (Φ := Φ) Γ L) : Prop :=
  left.region = right.region

theorem LexicallyCongruent.refl
    (program : TypedDominanceWellFormedFlat (Φ := Φ) Γ L) :
    LexicallyCongruent program program := rfl

theorem LexicallyCongruent.symm
    {left right : TypedDominanceWellFormedFlat (Φ := Φ) Γ L}
    (h : LexicallyCongruent left right) : LexicallyCongruent right left := Eq.symm h

theorem LexicallyCongruent.trans
    {left middle right : TypedDominanceWellFormedFlat (Φ := Φ) Γ L}
    (h₁ : LexicallyCongruent left middle) (h₂ : LexicallyCongruent middle right) :
    LexicallyCongruent left right := Eq.trans h₁ h₂

/-- A semantic sibling reordering consists of the existing permutation of the
tree presentation plus the presently separate, coordinated branch-target
congruence.  `DomTree.Reordered` alone intentionally does not rewrite labels,
so dropping `targets` here would be unsound. -/
structure CoherentReordering
    (left right : TypedDominanceWellFormedFlat (Φ := Φ) Γ L) : Prop where
  reordered : DomTree.Reordered left.flat.tree right.flat.tree
  targets : LexicallyCongruent left right

section Monadic

variable [LambdaIter.Subtyping.Semantics.TypeModel.{u, v} τ]
variable {ε : Type r} [LambdaIter.HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Isotope.Elgot.Iterate m] [Isotope.Elgot.LawfulElgotMonad m]
variable [LambdaIter.Subtyping.Semantics.InstructionModel Φ τ ε m]

/-- Direct complete-Elgot semantics of a typed flat CFG with a choice of
dominator tree. -/
noncomputable def denoteMonadic
    (program : TypedDominanceWellFormedFlat (Φ := Φ) Γ L) :
    Isotope.LambdaSSA.Semantics.Monadic.Env Γ →
      m (Isotope.LambdaSSA.Semantics.Monadic.LabelDen L) :=
  Isotope.LambdaSSA.Semantics.Monadic.Region.denote
    (ε := ε) (m := m) program.regionHasType

/-- Dominator-tree choice is semantically irrelevant once sibling permutation
is accompanied by the required branch-target reindexing. -/
theorem denoteMonadic_eq_of_lexicallyCongruent
    {left right : TypedDominanceWellFormedFlat (Φ := Φ) Γ L}
    (h : LexicallyCongruent left right) :
    denoteMonadic (ε := ε) (m := m) left = denoteMonadic (ε := ε) (m := m) right := by
  unfold denoteMonadic
  have hp : (⟨left.region, left.regionHasType⟩ :
      {r : Region Φ // Region.HasType Γ r L}) =
      ⟨right.region, right.regionHasType⟩ := Subtype.ext h
  exact congrArg (fun r : {r : Region Φ // Region.HasType Γ r L} =>
    Isotope.LambdaSSA.Semantics.Monadic.Region.denote
      (ε := ε) (m := m) r.2) hp

theorem CoherentReordering.denoteMonadic_eq
    {left right : TypedDominanceWellFormedFlat (Φ := Φ) Γ L}
    (h : CoherentReordering left right) :
    denoteMonadic (ε := ε) (m := m) left = denoteMonadic (ε := ε) (m := m) right :=
  denoteMonadic_eq_of_lexicallyCongruent h.targets

end Monadic

section Categorical

open CategoryTheory CategoryTheory.Limits
open LambdaIter.Subtyping.Semantics.Categorical

variable {V : Type u₁} {C : Type u₂}
variable [Category.{v₁} V] [Category.{v₂} C]
variable [CartesianMonoidalCategory V] [SymmetricCategory V]
variable [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
variable [HasFiniteCoproducts V] [HasFiniteCoproducts C]
variable [DistributiveTensor V] [DistributivePremonoidalCategory C]
variable [Iteration C] [ElgotCategory C]
variable (J : Functor V C) [StrongElgotFreydCategory J]
variable (M : TypeModel τ V)
variable [InstructionModel J M Φ]

/-- Categorical Freyd--Elgot semantics of the chosen lexicalization. -/
noncomputable def denoteCategorical
    (program : TypedDominanceWellFormedFlat (Φ := Φ) Γ L) :
    J.obj (Isotope.LambdaSSA.Semantics.Categorical.ctxObj M Γ) ⟶
      J.obj (Isotope.LambdaSSA.Semantics.Categorical.labelObj M L) :=
  Isotope.LambdaSSA.Semantics.Categorical.Region.denote
    J M program.regionHasType

theorem denoteCategorical_eq_of_lexicallyCongruent
    {left right : TypedDominanceWellFormedFlat (Φ := Φ) Γ L}
    (h : LexicallyCongruent left right) :
    denoteCategorical J M left = denoteCategorical J M right := by
  unfold denoteCategorical
  have hp : (⟨left.region, left.regionHasType⟩ :
      {r : Region Φ // Region.HasType Γ r L}) =
      ⟨right.region, right.regionHasType⟩ := Subtype.ext h
  exact congrArg (fun r : {r : Region Φ // Region.HasType Γ r L} =>
    Isotope.LambdaSSA.Semantics.Categorical.Region.denote J M
      r.2) hp

theorem CoherentReordering.denoteCategorical_eq
    {left right : TypedDominanceWellFormedFlat (Φ := Φ) Γ L}
    (h : CoherentReordering left right) :
    denoteCategorical J M left = denoteCategorical J M right :=
  denoteCategorical_eq_of_lexicallyCongruent J M h.targets

end Categorical

end TypedDominanceWellFormedFlat
end Isotope.TAC.Bridge.LambdaSSA
