import Isotope.LambdaSeq.Equiv

/-!
# Basic metatheory of lambda-seq: reflexivity of the equational theory

`Isotope.LambdaSeq.LocallyNameless.Equiv` has `symm` and `trans` as
constructors but no `refl`: reflexivity holds only at the two variable leaves
`var` and `bvar`.  `Equiv.refl` below propagates it through the two congruence
rules, making `Equiv` an equivalence relation on typable terms of a fixed type
in a fixed bound context.

That is the sole prerequisite for the syntactic setoid of
`Isotope/LambdaSeq/Models/Setoid.lean`, and hence for the quotient, the
syntactic model and initiality.

The recursion eliminates the `Type`-valued `HasType` into the `Prop`-valued
`Equiv`, which is permitted.
-/

namespace Isotope.LambdaSeq.LocallyNameless

variable {τ : Type u} [LambdaIter.TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [LambdaIter.HasTy Φ τ]
variable {ε : Type r} [LambdaIter.HasEff Φ ε]
variable {Γ : Ctx ν τ}

namespace HasType

/-- The derivation of the innermost bound variable. -/
def newest {n : Nat} {β : BoundCtx τ n} {A : τ} :
    HasType Φ Γ (.snoc β A) (.bv 0) A := by
  simpa [LambdaIter.LocallyNameless.BoundCtx.get] using
    (HasType.bv (Φ := Φ) (Γ := Γ) (β := .snoc β A) (i := (0 : Fin (n + 1))))

end HasType

namespace Equiv

omit [LambdaIter.TypeFormers τ] in
/-- **Reflexivity of the lambda-seq equational theory at typable terms.**

`Equiv` has reflexivity only at the leaves `fv` and `bv`; the other two cases
come from the congruence rules for `op` and `let₁`.  Together with the `symm`
and `trans` constructors this makes `Equiv` an equivalence relation on typable
terms — the fact the syntactic setoid is built from. -/
theorem refl {pureEff : ε} {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {A : τ} :
    HasType Φ Γ β a A → Equiv pureEff Γ β a a A
  | .fv h => .var h
  | .bv => .bvar
  | .op ha => .op (refl ha)
  | .let₁ ha hb => .let₁ (refl ha) (refl hb)

end Equiv

end Isotope.LambdaSeq.LocallyNameless
