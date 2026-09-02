import Isotope.LambdaSSA.LocallyNameless.Syntax
import Isotope.LambdaIter.LocallyNameless.Context

namespace Isotope.LambdaSSA.LocallyNameless

abbrev FreeCtx (ν : Type u) (τ : Type v) := LambdaIter.Ctx ν τ
abbrev BoundCtx (τ : Type u) (n : Nat) := LambdaIter.LocallyNameless.BoundCtx τ n

/-- Internal CFG labels occupy the newest (lowest) indices, followed by the
already-bound surrounding labels. -/
def extendLabelCtx {arity : Nat} (δ : BoundCtx τ l) (R : Fin arity → τ) :
    BoundCtx τ (arity + l) :=
  LambdaIter.LocallyNameless.BoundCtx.ofFin (Fin.addCases R δ.get)

@[simp] theorem extendLabelCtx_get_castAdd (δ : BoundCtx τ l)
    {arity : Nat} (R : Fin arity → τ) (i : Fin arity) :
    (extendLabelCtx δ R).get (Fin.castAdd l i) = R i := by
  simp [extendLabelCtx]

end Isotope.LambdaSSA.LocallyNameless
