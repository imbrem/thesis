import Isotope.LambdaCase.TypingSubst
import Isotope.LambdaCase.Equiv

/-!
# Basic metatheory of lambda-case: variable derivations and reflexivity

Two small facts that the equational theory of lambda-case needs before it can
be quotiented, and which are not among its constructors.

* `HasType.newest` / `HasType.previous`: the typing derivations of the two
  innermost bound variables, with `BoundCtx.get` already computed away.
* `Equiv.refl`: **reflexivity of the equational theory at typable terms.**
  Unlike `Isotope.LambdaIter.LocallyNameless.Eqv`, the lambda-case theory
  `Isotope.LambdaCase.LocallyNameless.Equiv` has no `refl` constructor — only
  the three reflexivity *leaves* `var`, `bvar` and `unit`.  Reflexivity at a
  general term therefore has to be propagated through the congruence rules,
  which is exactly what the recursion below does.  This is the one prerequisite
  for the syntactic setoid of `Isotope/LambdaCase/Models/Setoid.lean`: without
  it there is no `Setoid`, hence no quotient and no syntactic model.

The recursion eliminates the `Type`-valued `HasType` into the `Prop`-valued
`Equiv`, which is permitted (large elimination into `Prop` is always allowed).

This file is deliberately separate from `Typing.lean`, `TypingSubst.lean` and
`Equiv.lean` so that a concurrently developed duplicate shows up as a
file-level conflict rather than a silent double definition.
-/

namespace Isotope.LambdaCase.LocallyNameless

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

/-- The derivation of the next-to-innermost bound variable. -/
def previous {n : Nat} {β : BoundCtx τ n} {A B : τ} :
    HasType Φ Γ (.snoc (.snoc β A) B) (.bv 1) A := by
  simpa [LambdaIter.LocallyNameless.BoundCtx.get] using
    (HasType.bv (Φ := Φ) (Γ := Γ) (β := .snoc (.snoc β A) B)
      (i := (1 : Fin (n + 2))))

end HasType

namespace Equiv

/-- **Reflexivity of the lambda-case equational theory at typable terms.**

`Equiv` has reflexivity only at the leaves `fv`, `bv` and `unit`; every other
case is obtained from the congruence rule for the corresponding term former.
Together with the `symm` and `trans` constructors this makes `Equiv` an
equivalence relation on typable terms of a fixed type in a fixed bound
context — the fact the syntactic setoid is built from. -/
theorem refl {pureEff : ε} {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {A : τ} :
    HasType Φ Γ β a A → Equiv pureEff Γ β a a A
  | .fv h => .var h
  | .bv => .bvar
  | .op ha => .op (refl ha)
  | .let₁ ha hb => .let₁ (refl ha) (refl hb)
  | .unit => .unit
  | .pair ha hb => .pair (refl ha) (refl hb)
  | .let₂ ha hc => .let₂ (refl ha) (refl hc)
  | .inl ha => .inl (refl ha)
  | .inr hb => .inr (refl hb)
  | .case he hl hr => .case (refl he) (refl hl) (refl hr)
  | .abort ha => .abort (refl ha)

end Equiv

end Isotope.LambdaCase.LocallyNameless
