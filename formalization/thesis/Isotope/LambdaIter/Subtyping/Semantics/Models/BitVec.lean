import Isotope.LambdaIter.Subtyping.Semantics.Models.Null

/-!
# The bitvector model

Base types are widths, `α := Nat`, interpreted by `BitVec n`.  The instruction
signature is a deliberately small, closed set of pure bitvector operations:
constants, addition, bitwise and, bitwise not, and a zero test landing in
`bool = 1 ⊕ 1`.  All of them are pure, so `denotePure` is total and
`denote_pure` is definitional.

## Relationship to the null model

`BitVec n` is a finite type of cardinality `2 ^ n`, and so is the null-model
type `bool ^ n` where `bool = 1 ⊕ 1`.  `bitTy_equiv` exhibits the isomorphism,
so *at the level of types* the bitvector universe adds nothing to the null
universe.

That is the type half of the expected equivalence of the two **models**.  The
full statement — that the bitvector model is equivalent to the null model, so
that every bitvector program is interdefinable with a null-model program — also
needs the *instructions* to be expressible, i.e. a translation of `add`, `and`,
`not` and `eqz` into null-model terms together with a semantics-preservation
theorem.  That is **not** proved here; see the honest boundary in
`Models.lean`.
-/

namespace Isotope.LambdaIter.Subtyping.Semantics

universe v

namespace BitVecModel

/-- Base types are bitvector widths. -/
abbrev BvTy : Type := LambdaIter.Ty Nat

/-- The interpretation of base types: a width denotes its bitvectors. -/
@[reducible] def base : Nat → Type := fun n => BitVec n

/-- A small, closed signature of pure bitvector instructions. -/
inductive Instr : Type where
  /-- The constant `v`, of width `n`. -/
  | const (n : Nat) (v : BitVec n)
  /-- Addition at width `n`. -/
  | add (n : Nat)
  /-- Bitwise conjunction at width `n`. -/
  | and (n : Nat)
  /-- Bitwise negation at width `n`. -/
  | not (n : Nat)
  /-- Test for zero, landing in `bool`. -/
  | eqz (n : Nat)
  deriving DecidableEq

/-- The booleans of this universe, `1 ⊕ 1`. -/
abbrev boolTy : BvTy := .coprod .unit .unit

instance : LambdaIter.HasTy Instr BvTy where
  src
    | .const _ _ => .unit
    | .add n => .tensor (.base n) (.base n)
    | .and n => .tensor (.base n) (.base n)
    | .not n => .base n
    | .eqz n => .base n
  trg
    | .const n _ => .base n
    | .add n => .base n
    | .and n => .base n
    | .not n => .base n
    | .eqz _ => boolTy

/-- Every bitvector instruction is pure. -/
instance : LambdaIter.HasEff Instr Eff where
  eff _ := Eff.pure

@[simp] theorem eff_eq (f : Instr) : (LambdaIter.instrEff f : Eff) = ⊥ := rfl

/-- The bitvector type model. -/
@[reducible] def typeModel : TypeModel.{0, 0} BvTy := Free.typeModel base

attribute [instance] typeModel

instance : LawfulTypeModel.{0, 0} BvTy := Free.lawfulTypeModel _

/-- The pure denotation of each instruction. -/
def denotePure : (f : Instr) →
    Free.interp base (LambdaIter.instrSrc f) → Free.interp base (LambdaIter.instrTrg f)
  | .const _ v, _ => v
  | .add n, p => ((p.1 : BitVec n) + (p.2 : BitVec n) : BitVec n)
  | .and n, p => ((p.1 : BitVec n) &&& (p.2 : BitVec n) : BitVec n)
  | .not n, x => (~~~(x : BitVec n) : BitVec n)
  | .eqz n, x =>
      (if (x : BitVec n).toNat = 0 then Sum.inr PUnit.unit else Sum.inl PUnit.unit :
        PUnit ⊕ PUnit)

/-- Every monad models the bitvector signature, purely. -/
instance instructionModel (m : Type → Type) [Monad m] :
    InstructionModel Instr BvTy Eff m where
  denote f a := pure (denotePure f a)
  denotePure f _ := denotePure f
  denote_pure _ _ _ := rfl

/-! ### Every bitvector type is already a null-model type -/

/-- The null-model type standing for width `n`: an `n`-fold tensor of `bool`. -/
abbrev bitTy (n : Nat) : Null.NullTy := Null.pow Null.boolTy n

/-- `bool ^ n` in the null universe has `2 ^ n` elements. -/
theorem card_bitTy : (n : Nat) → Fintype.card (Free.interp Null.nullBase (bitTy n)) = 2 ^ n
  | 0 => rfl
  | n + 1 => by
      have ih := card_bitTy n
      show Fintype.card (Free.interp Null.nullBase Null.boolTy ×
        Free.interp Null.nullBase (bitTy n)) = 2 ^ (n + 1)
      rw [Fintype.card_prod, ih]
      show 2 * 2 ^ n = 2 ^ (n + 1)
      rw [pow_succ, Nat.mul_comm]

/-- `BitVec n` is by construction a wrapper around `Fin (2 ^ n)`. -/
def bitVecEquivFin (n : Nat) : BitVec n ≃ Fin (2 ^ n) where
  toFun := BitVec.toFin
  invFun := BitVec.ofFin
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The type half of the null/bitvector equivalence.**  The bitvectors of
width `n` are isomorphic to the null-model type `bool ^ n`, so the bitvector
universe adds no types the null universe does not already have. -/
theorem bitTy_equiv (n : Nat) :
    Nonempty (Free.interp Null.nullBase (bitTy n) ≃ BitVec n) :=
  ⟨(Fintype.equivFinOfCardEq (card_bitTy n)).trans (bitVecEquivFin n).symm⟩

end BitVecModel

end Isotope.LambdaIter.Subtyping.Semantics
