import Isotope.LambdaSSA.Translation.ANF.Elaboration
import Isotope.LambdaSSA.Translation.ANF.ToSSA

/-! # Closed exact lambda-iter frontend for lambda-SSA -/

namespace Isotope.LambdaSSA.Translation.Frontend.Core

open Isotope.LambdaIter

/-- Compile a locally nameless term without free names to an SSA region which
returns to its sole external continuation. -/
def compile (t : LambdaIter.LocallyNameless.Tm Empty Φ n) : LambdaSSA.Region Φ :=
  ANF.ToSSA.program 0 (ANF.Elaboration.elaborate t)

variable {τ : Type u} [TypeFormers τ]
variable {Φ : Type q} [HasTy Φ τ]

/-- The compiler preserves exact typing and exposes one result continuation. -/
def compile_hasType {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {t : LambdaIter.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : LambdaIter.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β t A) :
    LambdaSSA.Region.HasType
      (LambdaSSA.LocallyNameless.ToDeBruijn.context β) (compile t) [A] :=
  ANF.ToSSA.program_hasType (ANF.Elaboration.elaborate_hasType h)
    (by simp [LambdaSSA.At])

end Isotope.LambdaSSA.Translation.Frontend.Core
