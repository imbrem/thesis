import Isotope.LambdaIter.Subtyping.Semantics.Categorical
import Isotope.LambdaSeq.Categorical

/-!
# Categorical models of the freely generated type universe

`Models/Free.lean` shows that an interpretation `β : α → Type v` of the base
types of `Ty α` extends uniquely to a *set-valued* `TypeModel`.  This file is
its categorical analogue: an interpretation `base : α → V` of the base types
in **any** cartesian monoidal category `V` with finite coproducts extends to a
`Categorical.TypeModel (Ty α) V`, and that model is lawful.

This is what makes "λ-iter has a model in every Freyd category" a construction
rather than an assumption.  The repository previously had exactly one
categorical type model, `Semantics.Categorical.ofTypeModel`, which is hard-wired
to `V = Type v`; nothing produced a type model in a general value category.

Every type-former isomorphism here is `Iso.refl`, because `obj` is defined by
structural recursion so that `obj (A ⊗ B) = obj A ⊗ obj B` *definitionally*.
Consequently the six `LawfulTypeModel` laws are near-trivial, and the file
should be read as bookkeeping rather than as mathematics: the content is that
the bookkeeping closes with no side conditions on `V`.
-/

universe v₁ u₁ u

namespace Isotope.LambdaIter.Subtyping.Semantics.Categorical

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped MonoidalCategory

namespace Free

variable {α : Type u} {V : Type u₁} [Category.{v₁} V]

section Obj

variable [CartesianMonoidalCategory V] [HasFiniteCoproducts V]

/-- The object of `V` denoted by a freely generated type, given an
interpretation of the base types.  Type formers are interpreted by the
corresponding structure of `V` on the nose. -/
noncomputable def obj (base : α → V) : Ty α → V
  | .base a => base a
  | .tensor A B => obj base A ⊗ obj base B
  | .unit => 𝟙_ V
  | .coprod A B => obj base A ⨿ obj base B
  | .empty => ⊥_ V

@[simp] theorem obj_base (base : α → V) (a : α) : obj base (.base a) = base a := rfl

@[simp] theorem obj_tensor (base : α → V) (A B : Ty α) :
    obj base (.tensor A B) = obj base A ⊗ obj base B := rfl

@[simp] theorem obj_unit (base : α → V) : obj base (.unit : Ty α) = 𝟙_ V := rfl

@[simp] theorem obj_coprod (base : α → V) (A B : Ty α) :
    obj base (.coprod A B) = (obj base A ⨿ obj base B) := rfl

@[simp] theorem obj_empty (base : α → V) : obj base (.empty : Ty α) = ⊥_ V := rfl

/-- The morphism of `V` denoted by a proof-relevant subtyping derivation.  As
in the set-valued case, only the operations of the `Subtyping` interface are
interpreted: `empty` by the initial map and `unit` by the terminal map. -/
noncomputable def subty (base : α → V) :
    {A B : Ty α} → Ty.Subty A B → (obj base A ⟶ obj base B)
  | _, _, .refl _ => 𝟙 _
  | _, _, .trans f g => subty base f ≫ subty base g
  | _, _, .tensor f g => subty base f ⊗ₘ subty base g
  | _, _, .coprod f g => coprod.map (subty base f) (subty base g)
  | _, _, .empty _ => initial.to _
  | _, _, .unit _ => CartesianMonoidalCategory.toUnit _

/-- The categorical model of the freely generated universe determined by
`base`.  Every type-former isomorphism is the identity. -/
@[reducible] noncomputable def typeModel (base : α → V) : TypeModel (Ty α) V where
  obj := obj base
  tensorIso _ _ := Iso.refl _
  unitIso := Iso.refl _
  coprodIso _ _ := Iso.refl _
  emptyIsInitial := initialIsInitial
  subty := subty base

@[simp] theorem typeModel_obj (base : α → V) (A : Ty α) :
    (typeModel base).obj A = obj base A := rfl

@[simp] theorem typeModel_subty (base : α → V) {A B : Ty α} (d : Ty.Subty A B) :
    (typeModel base).subty d = subty base d := rfl

/-- **The free categorical model is lawful**, in every cartesian monoidal `V`
with finite coproducts.  No further hypotheses on `V` are needed. -/
theorem lawfulTypeModel (base : α → V) :
    LawfulTypeModel (Ty α) V (typeModel base) where
  subty_refl _ := rfl
  subty_trans _ _ := rfl
  subty_tensor _ _ := (Category.comp_id _).trans (Category.id_comp _).symm
  subty_coprod _ _ := (Category.comp_id _).trans (Category.id_comp _).symm
  subty_empty _ := initialIsInitial.hom_ext _ _
  subty_unit _ := Category.comp_id _

/-- Distinct subtyping derivations may still denote distinct coercions: the
free categorical model is deliberately *not* proof-irrelevant by construction.
It becomes so exactly when the ambient derivations are, which is what
`subtyProofIrrelevantOfSubsingleton` records on the set-valued side. -/
theorem subtyProofIrrelevant (base : α → V)
    (h : ∀ A B : Ty α, Subsingleton (Ty.Subty A B)) :
    SubtyProofIrrelevant (Ty α) V (typeModel base) where
  subty_eq {A B} f g := by
    letI := h A B
    rw [Subsingleton.elim f g]

end Obj

end Free

end Isotope.LambdaIter.Subtyping.Semantics.Categorical

namespace Isotope.LambdaSeq.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

/-- The λ-seq type model interface asks only for `obj` and `subty`: no
type-former isomorphisms and no coproducts on the value category.  So the same
two definitions give a λ-seq type model whenever `V` happens to have the
structure used to define them.

This is stated separately because λ-seq's `TypeModel` is a *different*, leaner
class than λ-iter's, not a specialization of it.  The hypotheses on `V` here
are inherited from `Free.obj`/`Free.subty`, i.e. from the *type universe*
`Ty α` and its subtyping interface, not from anything λ-seq's terms do: λ-seq
never builds or eliminates a sum, but `Ty α` still has `⊕` and `0`, and
`Subty.empty` still has to denote a map out of the interpretation of `0`. -/
@[reducible] noncomputable def freeTypeModel {α : Type u} {V : Type u₁} [Category.{v₁} V]
    [CartesianMonoidalCategory V] [Limits.HasFiniteCoproducts V] (base : α → V) :
    TypeModel (LambdaIter.Ty α) V where
  obj := LambdaIter.Subtyping.Semantics.Categorical.Free.obj base
  subty := LambdaIter.Subtyping.Semantics.Categorical.Free.subty base

end Isotope.LambdaSeq.Semantics.Categorical
