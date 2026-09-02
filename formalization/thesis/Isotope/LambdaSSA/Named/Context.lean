import Isotope.LambdaSSA.Named.Syntax
import Isotope.LambdaIter.Context

namespace Isotope.LambdaSSA.Named

abbrev VCtx (ν : Type u) (τ : Type v) := LambdaIter.Ctx ν τ
abbrev LCtx (κ : Type u) (τ : Type v) := LambdaIter.Ctx κ τ

/-- Simultaneously extend a label context.  Label `i` occupies de Bruijn
index `i`; if names repeat, the lower block index shadows the higher one. -/
def extendLabels (L : LCtx κ τ) (n : Nat)
    (labels : Fin n → Binder κ) (types : Fin n → τ) : LCtx κ τ :=
  (List.ofFn fun i => (labels i, types i)).foldr
    (fun p L => L.snoc p.1 p.2) L

end Isotope.LambdaSSA.Named
