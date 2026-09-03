import Isotope.LambdaIter.Models.Monadic.Concrete
import Isotope.LambdaIter.Signature.Havoc

/-!
# Models of the havoc signature, and what total nondeterminism costs

`havoc : 1 → 1 ⊕ 1` is meant to denote a *total* nondeterministic choice: the
set of values it may return is the whole of `1 ⊕ 1`.  "The set of values it
may return" is not a notion an arbitrary monad has, so it is supplied by a
monad morphism into the powerset -- a `MonadHom m SetM` -- exactly the
structure of `Isotope/Elgot/Morphism.lean`.  `IsTotal φ c` then says that `c`,
collected along `φ`, is everything.

Three results:

* `havocSetModel_isTotal` -- the powerset model realises total nondeterminism,
  with `havoc` denoting `Set.univ`.  So does the countable powerset.
* `part_not_isTotal` -- **no** model of the havoc signature in `Part` does.
  Not "no natural one": every partial value has a subsingleton graph, and
  `1 ⊕ 1` has two elements.  Determinism is a property of the *monad*, and no
  choice of instruction denotation can escape it.
* `havocPure_not_isTotal` -- **no** model of the *pure* havoc signature does,
  in any monad at all and along any collecting morphism.  A pure instruction
  must satisfy `denoteInstr f a = pure (denotePureInstr f hf a)`, so it
  denotes an ordinary function, and a monad morphism sends `pure x` to the
  singleton `{x}`.  This is the semantic content of the syntactic fact that
  `letBeta` would let a pure `havoc` be duplicated.

The three together say precisely what the effect annotation buys: it is not
`Part` versus `Set` alone that decides whether `havoc` can be total, but the
*conjunction* of a nondeterministic monad and an impure annotation.
-/

namespace Isotope.LambdaIter.Monadic

open Isotope.Elgot
open Isotope.LambdaIter.Monadic.SeqModel

/-- The type universe of the havoc signature is the free one, so its formers
are injective. -/
instance : InjectiveFormers Sig.havoc.Ty :=
  inferInstanceAs (InjectiveFormers (Ty EmptyBase.{0}))

/-- The type universe of the mis-annotated havoc signature is the same one. -/
instance : InjectiveFormers Sig.havocPure.Ty :=
  inferInstanceAs (InjectiveFormers (Ty EmptyBase.{0}))

/-! ### Models -/

/-- **A model of the havoc signature in `m`**, with `havoc` denoting a chosen
computation `c` of a boolean.  The type interpretation is the free one; the
only new data is `c`. -/
def havocModel (m : Type → Type) [Monad m] (c : m (Unit ⊕ Unit)) :
    Model.{0, 0} Sig.havoc m where
  interp := freeInterp
  denoteInstr _ _ := c
  denotePureInstr f hf := absurd hf (by cases f; exact Sig.havoc_not_isPure)
  denoteInstr_pure f hf := absurd hf (by cases f; exact Sig.havoc_not_isPure)
  tensorEquiv _ _ := Equiv.refl _
  unitEquiv := Equiv.refl _
  coprodEquiv _ _ := Equiv.refl _
  emptyEquiv := Equiv.refl _

@[simp] theorem havocModel_denoteInstr (m : Type → Type) [Monad m]
    (c : m (Unit ⊕ Unit)) (f : Sig.havoc.Instr) (a : Unit) :
    (havocModel m c).denoteInstr f a = c := rfl

/-- **The powerset model of havoc**: `havoc` returns everything. -/
def havocSetModel : Model.{0, 0} Sig.havoc SetM :=
  havocModel SetM (Set.univ : Set (Unit ⊕ Unit))

/-- **The countable-powerset model of havoc**: the same, noting that a
two-element set is countable. -/
def havocCSetModel : Model.{0, 0} Sig.havoc Nondet.CSet :=
  havocModel Nondet.CSet ⟨(Set.univ : Set (Unit ⊕ Unit)), Set.countable_univ⟩

/-- The algebra of lambda-iter over the havoc signature carried by the
powerset. -/
def havocSetAlg : Alg.{0, 0} Sig.havoc := Alg.ofModel havocSetModel

/-- The algebra of lambda-iter over the havoc signature carried by the
countable powerset. -/
def havocCSetAlg : Alg.{0, 0} Sig.havoc := Alg.ofModel havocCSetModel

/-! ### Total nondeterminism -/

/-- A computation `c` is *totally nondeterministic*, as seen by a collecting
monad morphism `φ` into the powerset, when the set of values it may produce is
everything. -/
def IsTotal {m : Type → Type} [Monad m] {B : Type} (φ : MonadHom m SetM)
    (c : m B) : Prop := φ.app c = (Set.univ : Set B)

/-- A subsingleton collection is not total at a type with two distinct
elements. -/
theorem not_isTotal_of_subsingleton {m : Type → Type} [Monad m] {B : Type}
    (φ : MonadHom m SetM) (c : m B) (hs : (φ.app c : Set B).Subsingleton)
    {x y : B} (hxy : x ≠ y) : ¬ IsTotal φ c := by
  intro h
  exact hxy (hs (h ▸ Set.mem_univ x) (h ▸ Set.mem_univ y))

/-- The two booleans of a model are distinct, whatever the model. -/
theorem coprod_unit_ne {S : Sig.{0}} {m : Type → Type} [Monad m]
    (M : Model.{0, 0} S m) :
    ((M.coprodEquiv unit unit).symm (.inl (M.unitEquiv.symm ())) :
        M.interp (coprod unit unit)) ≠
      (M.coprodEquiv unit unit).symm (.inr (M.unitEquiv.symm ())) := fun h =>
  Sum.inl_ne_inr ((M.coprodEquiv unit unit).symm.injective h)

/-- **The powerset model realises total nondeterminism.** -/
theorem havocSetModel_isTotal :
    IsTotal (MonadHom.id SetM) (havocSetModel.denoteInstr HavocInstr.havoc ()) := rfl

/-- **The countable powerset realises total nondeterminism too**, collected
along the forgetful morphism `CSet → SetM`. -/
theorem havocCSetModel_isTotal :
    IsTotal CSet.toSetHom.toMonadHom
      (havocCSetModel.denoteInstr HavocInstr.havoc ()) := rfl

/-- **No model of the havoc signature in `Part` is totally nondeterministic.**
The obstruction is the monad, not the choice of denotation: every partial
value has a subsingleton graph, while the target type `1 ⊕ 1` has two
elements. -/
theorem part_not_isTotal (M : Model.{0, 0} Sig.havoc Part) (a : M.interp unit) :
    ¬ IsTotal Part.toSetHom.toMonadHom (M.denoteInstr HavocInstr.havoc a) :=
  not_isTotal_of_subsingleton _ _ (Part.toSet_subsingleton _) (coprod_unit_ne M)

/-- **No model of the mis-annotated havoc signature is totally
nondeterministic, in any monad and along any collecting morphism.**  Declaring
`havoc` pure forces it to denote an ordinary function, and a monad morphism
sends a returned value to a singleton.

This is the semantic counterpart of the syntactic fact that `letBeta` would
otherwise identify one coin flip with two. -/
theorem havocPure_not_isTotal {m : Type → Type} [Monad m]
    (M : Model.{0, 0} Sig.havocPure m) (φ : MonadHom m SetM)
    (a : M.interp unit) :
    ¬ IsTotal φ (M.denoteInstr HavocInstr.havoc a) := by
  refine not_isTotal_of_subsingleton φ _ ?_ (coprod_unit_ne M)
  rw [M.denoteInstr_pure HavocInstr.havoc Sig.havocPure_isPure a, φ.app_pure]
  intro x hx y hy
  exact hx.trans hy.symm

/-! ### A morphism between models of the havoc signature -/

/-- **The countable-powerset havoc algebra maps to the powerset one.**  Unlike
the morphisms of `Models/Monadic/Concrete.lean` this one has a non-trivial
instruction-compatibility obligation: the carrier of the countable full set is
the full set. -/
def havocCSetToSetAlgHom : havocCSetAlg ⟶ havocSetAlg :=
  Alg.homOfReinterpret havocCSetModel CSet.toSetHom
    (fun _ _ => (Set.univ : Set (Unit ⊕ Unit)))
    (fun f hf _ => absurd hf (by cases f; exact Sig.havoc_not_isPure))
    (fun _ _ => rfl)

end Isotope.LambdaIter.Monadic
