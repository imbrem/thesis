import Isotope.LambdaCase.Subtyping.Semantics

/-!
# Identity semantics for lambda-case

The ordinary evaluator is the monadic semantics specialized to `Id`.  In
contrast, `Id` cannot support even an unconstrained total iteration operator
of the shape required by lambda-iter.
-/

namespace Isotope.LambdaCase.Subtyping.Subtyping.Semantics.Identity

open Isotope.LambdaCase.LocallyNameless

universe u v w q r

variable {τ : Type u} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
  [LambdaIter.Subtyping.Semantics.TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [LambdaIter.HasTy Φ τ]
variable {ε : Type r} [LambdaIter.HasEff Φ ε] [Bot ε]
variable [LambdaIter.Subtyping.Semantics.InstructionModel Φ τ ε Id]

/-- Direct evaluation of lambda-case terms into their interpreted Lean type. -/
def eval {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A) :
    CtxDen Γ → BoundDen β → TyDen A :=
  denote (ε := ε) (m := Id) h

/-- Direct evaluation is definitionally the identity-monad instance of the
generic monadic semantics. -/
theorem eval_eq_denote {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    eval (ε := ε) h γ ρ = denote (ε := ε) (m := Id) h γ ρ := rfl

end Isotope.LambdaCase.Subtyping.Subtyping.Semantics.Identity

namespace Isotope.Elgot

/-- `Id` has no total iteration operation of the complete-Elgot shape.  A
putative iterator applied to the endlessly recurring `PUnit` loop would have
to manufacture an inhabitant of `Empty`.

This is stronger than failure of the Elgot laws: the bare `Iterate Id` class
is already impossible. -/
theorem not_nonempty_iterate_id : ¬ Nonempty (Iterate (Id : Type → Type)) := by
  rintro ⟨iteration⟩
  let loop : Unit → Id (Empty ⊕ Unit) := fun _ => Sum.inr ()
  exact Empty.elim (iteration.iter loop ())

end Isotope.Elgot
