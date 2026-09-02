import Isotope.LambdaIter.Subtyping.Semantics.Models.Null

/-!
# The natural-number model

A single base type, `α := Unit`, interpreted by `Nat`.  The instruction
signature is the smallest set that makes the base type useful: the constant
zero, successor, addition, and the case eliminator `Nat → 1 ⊕ Nat` splitting
zero from a predecessor.  All four are pure.

## Relationship to the null model

Unlike the bitvector model, this one is **not** a disguised null model.  Every
type of the null universe denotes a finite type (`Null.fintypeInterp`), whereas
the base type here denotes `Nat`, which is infinite.  `natTy_not_null` records
this, so the natural-number model is strictly more expressive at the level of
types — which is exactly why the bitvector case is interesting and this one is
not.
-/

namespace Isotope.LambdaIter.Subtyping.Semantics

namespace NatModel

/-- A single base type. -/
abbrev NatTy : Type := LambdaIter.Ty Unit

/-- The interpretation of the single base type. -/
@[reducible] def base : Unit → Type := fun _ => Nat

/-- The base type, as a type of this universe. -/
abbrev natTy : NatTy := .base ()

/-- A small, closed signature of pure natural-number instructions. -/
inductive Instr : Type where
  /-- The constant zero. -/
  | zero
  /-- The successor function. -/
  | succ
  /-- Addition. -/
  | add
  /-- The eliminator: zero, or a predecessor. -/
  | case
  deriving DecidableEq, Repr

instance : LambdaIter.HasTy Instr NatTy where
  src
    | .zero => .unit
    | .succ => natTy
    | .add => .tensor natTy natTy
    | .case => natTy
  trg
    | .zero => natTy
    | .succ => natTy
    | .add => natTy
    | .case => .coprod .unit natTy

/-- Every natural-number instruction is pure. -/
instance : LambdaIter.HasEff Instr Eff where
  eff _ := Eff.pure

@[simp] theorem eff_eq (f : Instr) : (LambdaIter.instrEff f : Eff) = ⊥ := rfl

/-- The natural-number type model. -/
@[reducible] def typeModel : TypeModel.{0, 0} NatTy := Free.typeModel base

attribute [instance] typeModel

instance : LawfulTypeModel.{0, 0} NatTy := Free.lawfulTypeModel _

/-- The pure denotation of each instruction. -/
def denotePure : (f : Instr) →
    Free.interp base (LambdaIter.instrSrc f) → Free.interp base (LambdaIter.instrTrg f)
  | .zero, _ => (0 : Nat)
  | .succ, n => Nat.succ n
  | .add, p => Nat.add p.1 p.2
  | .case, n =>
      (Nat.casesOn (motive := fun _ => PUnit ⊕ Nat) (n : Nat)
        (Sum.inl PUnit.unit) (fun k => Sum.inr k))

/-- Every monad models the natural-number signature, purely. -/
instance instructionModel (m : Type → Type) [Monad m] :
    InstructionModel Instr NatTy Eff m where
  denote f a := pure (denotePure f a)
  denotePure f _ := denotePure f
  denote_pure _ _ _ := rfl

/-! ### The natural-number model is not a null model -/

/-- The base type denotes an infinite type. -/
theorem infinite_natTy : Infinite Nat := inferInstance

/-- **The natural-number universe is strictly richer than the null universe.**
No type of the null universe denotes a type isomorphic to `Nat`, because every
null type denotes a finite type. -/
theorem natTy_not_null (A : Null.NullTy) :
    IsEmpty (Free.interp Null.nullBase A ≃ Nat) := by
  constructor
  intro e
  haveI : Finite (Free.interp Null.nullBase A) := Finite.of_fintype _
  haveI : Finite Nat := Finite.of_equiv _ e
  exact (not_finite_iff_infinite.mpr (inferInstance : Infinite Nat)) this

end NatModel

end Isotope.LambdaIter.Subtyping.Semantics
