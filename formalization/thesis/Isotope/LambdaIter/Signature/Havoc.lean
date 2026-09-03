import Isotope.LambdaIter.Signature.Initial

/-!
# The havoc signature: one instruction for total nondeterminism

`havoc : 1 → 1 ⊕ 1` is the *demonic-free* choice: an instruction that may
return either boolean, with no way to predict which.  This file makes it a
first-class signature over the freely generated type universe of
`Signature/Empty.lean`.

## How should `havoc` be typed?

Three decisions, each forced.

* **Source `1`.**  The object language applies an instruction to a term of its
  source type, and `havoc` consumes nothing.  `1` is the type with exactly one
  closed value `()`, so `havoc ()` is the unique way to invoke it and the
  choice carries no input.  A source of `0` would make the instruction
  uninvocable; any larger source would smuggle in an argument the operation
  does not use.
* **Target `1 ⊕ 1`.**  A *two-way* choice is the smallest non-degenerate total
  nondeterminism: at `1` there is nothing to choose, and at any wider type the
  operation is a composite of binary choices.  Crucially `1 ⊕ 1` is definable
  in the *empty* type universe, so the havoc signature adds an instruction and
  nothing else -- no base type is needed, and every model of the empty
  signature extends to a candidate model of this one.
* **Impure.**  This is the substantive one.  The equational theory's `letBeta`
  axiom substitutes a *syntactically pure* term for its binder, so if `havoc`
  were pure the theory would prove

  ```
  let x = havoc () in ⟨x, x⟩  =  ⟨havoc (), havoc ()⟩
  ```

  identifying one coin flip with two.  The semantic shadow of this is exact:
  a `SeqModel` must supply `denotePureInstr` for every pure instruction, with
  `denoteInstr f a = pure (denotePureInstr f hf a)`, so a pure instruction is
  *forced* to denote a deterministic function.  `Sig.havocPure` below records
  the bad choice, and `Models/Monadic/Havoc.lean` proves that it admits no
  total-nondeterministic model **in any monad whatsoever** -- not merely in
  `Part`.  So the effect annotation is not decoration: it is what makes total
  nondeterminism expressible at all.

`EmptyEff` cannot be reused, since it is a singleton and every instruction
over it is pure.  Two effects are exactly what is needed, and no more.
-/

namespace Isotope.LambdaIter

/-- The instruction set of the havoc signature: one instruction. -/
inductive HavocInstr : Type
  /-- Return either boolean, unpredictably. -/
  | havoc
  deriving DecidableEq

/-- The effect annotations of the havoc signature: a pure effect and one
other.  Two elements are needed, since over a singleton effect set every
instruction is pure. -/
inductive HavocEff : Type
  /-- The designated pure effect. -/
  | pure
  /-- The effect of `havoc`. -/
  | nondet
  deriving DecidableEq

/-- `havoc` consumes a unit and produces a boolean. -/
instance instHasTyHavoc : HasTy HavocInstr EmptyTy.{0} where
  src _ := unit
  trg _ := EmptyTy.boolTy

/-- `havoc` is nondeterministic, hence not pure. -/
instance instHasEffHavoc : HasEff HavocInstr HavocEff where
  eff _ := .nondet

@[simp] theorem instrSrc_havoc :
    instrSrc (τ := EmptyTy.{0}) HavocInstr.havoc = unit := rfl

@[simp] theorem instrTrg_havoc :
    instrTrg (τ := EmptyTy.{0}) HavocInstr.havoc = EmptyTy.boolTy := rfl

/-- **The havoc signature**: the empty type universe, one nondeterministic
instruction `havoc : 1 → 1 ⊕ 1`, and a two-element effect set. -/
def Sig.havoc : Sig.{0} where
  Ty := EmptyTy.{0}
  formers := inferInstance
  Instr := HavocInstr
  Eff := HavocEff
  pureEff := .pure
  hasTy := inferInstance
  hasEff := inferInstance

/-- **The deliberately mis-annotated variant**, in which `havoc` is declared
pure.  It exists to be refuted: see `Models/Monadic/Havoc.lean`. -/
def Sig.havocPure : Sig.{0} where
  Ty := EmptyTy.{0}
  formers := inferInstance
  Instr := HavocInstr
  Eff := HavocEff
  pureEff := .nondet
  hasTy := inferInstance
  hasEff := inferInstance

/-- `havoc` is not pure in `Sig.havoc`. -/
theorem Sig.havoc_not_isPure :
    ¬ IsPure (Φ := Sig.havoc.Instr) Sig.havoc.pureEff HavocInstr.havoc := by
  intro h
  exact HavocEff.noConfusion h

/-- `havoc` *is* pure in `Sig.havocPure` -- which is exactly the problem. -/
theorem Sig.havocPure_isPure :
    IsPure (Φ := Sig.havocPure.Instr) Sig.havocPure.pureEff HavocInstr.havoc := rfl

/-- The unique signature morphism from the empty signature into the havoc
signature: the havoc signature is a genuine extension, not a reindexing. -/
def Sig.emptyToHavoc : Sig.empty.{0} ⟶ Sig.havoc := Sig.fromEmpty _

end Isotope.LambdaIter
