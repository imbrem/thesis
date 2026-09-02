import Isotope.LambdaCase.Typing
import Isotope.LambdaSSA.Translation.Frontend.Core

/-! # Lambda-case frontends for lambda-SSA -/

namespace Isotope.LambdaSSA.Translation.Frontend.LambdaCase

open Isotope.LambdaIter

namespace LocallyNameless

/-- Compile an exact locally nameless lambda-case term with no free names. -/
def compile (t : Isotope.LambdaCase.LocallyNameless.Tm Empty Φ n) :
    LambdaSSA.Region Φ :=
  Core.compile t.embed

variable {τ : Type u} [TypeFormers τ]
variable {Φ : Type q} [HasTy Φ τ]

/-- Exact typing is preserved by the lambda-case frontend. -/
def compile_hasType {β : Isotope.LambdaCase.LocallyNameless.BoundCtx τ n}
    {t : Isotope.LambdaCase.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : Isotope.LambdaCase.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β t A) :
    LambdaSSA.Region.HasType
      (LambdaSSA.LocallyNameless.ToDeBruijn.context β) (compile t) [A] :=
  Core.compile_hasType h.embed

end LocallyNameless

end Isotope.LambdaSSA.Translation.Frontend.LambdaCase
