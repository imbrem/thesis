import Isotope.LambdaSeq.Typing
import Isotope.LambdaSSA.Translation.Frontend.Core

/-! # Lambda-seq frontends for lambda-SSA -/

namespace Isotope.LambdaSSA.Translation.Frontend.LambdaSeq

open Isotope.LambdaIter

namespace LocallyNameless

/-- Compile an exact locally nameless lambda-seq term with no free names. -/
def compile (t : Isotope.LambdaSeq.LocallyNameless.Tm Empty Φ n) :
    LambdaSSA.Region Φ :=
  Core.compile t.embedIter

variable {τ : Type u} [TypeFormers τ]
variable {Φ : Type q} [HasTy Φ τ]

/-- Exact typing is preserved by the lambda-seq frontend. -/
def compile_hasType {β : Isotope.LambdaSeq.LocallyNameless.BoundCtx τ n}
    {t : Isotope.LambdaSeq.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : Isotope.LambdaSeq.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β t A) :
    LambdaSSA.Region.HasType
      (LambdaSSA.LocallyNameless.ToDeBruijn.context β) (compile t) [A] :=
  Core.compile_hasType h.embedIter

end LocallyNameless

end Isotope.LambdaSSA.Translation.Frontend.LambdaSeq
