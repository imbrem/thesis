import Isotope.LambdaSeq.Typing
import Isotope.LambdaSSA.Translation.Frontend.Core
import Isotope.LambdaSSA.Translation.Frontend.LambdaCase

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

namespace Named

open Isotope.LambdaIter

/-- Compile a closed named sequential term through its lambda-case embedding. -/
def compile (t : Isotope.LambdaSeq.Named.Tm Empty Φ) : LambdaSSA.Region Φ :=
  Isotope.LambdaSSA.Translation.Frontend.LambdaCase.Named.compile
    (Isotope.LambdaSeq.Named.embedCase t)

variable {τ : Type u} [TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]

/-- Compile any well-typed closed named lambda-seq term. -/
noncomputable def compileTyped {t : Isotope.LambdaSeq.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaSeq.Named.HasType (Ctx.nil : Ctx ν τ) t A) :
    LambdaSSA.Region Φ :=
  Isotope.LambdaSSA.Translation.Frontend.LambdaCase.Named.compileTyped h.embedCase

def compileTyped_hasType {t : Isotope.LambdaSeq.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaSeq.Named.HasType (Ctx.nil : Ctx ν τ) t A) :
    LambdaSSA.Region.HasType [] (compileTyped h) [A] :=
  Isotope.LambdaSSA.Translation.Frontend.LambdaCase.Named.compileTyped_hasType h.embedCase

end Named

end Isotope.LambdaSSA.Translation.Frontend.LambdaSeq
