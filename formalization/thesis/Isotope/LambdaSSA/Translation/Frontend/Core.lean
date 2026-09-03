import Isotope.LambdaSSA.Translation.Compile
import Isotope.LambdaSSA.Translation.Frontend.Closed
import Isotope.LambdaSSA.Translation.Frontend.NamedToLocallyNameless

/-! # Closed exact lambda-iter frontend for lambda-SSA -/

namespace Isotope.LambdaSSA.Translation.Frontend.Core

open Isotope.LambdaIter

/-- Compile a locally nameless term without free names to an SSA region which
returns to its sole external continuation. -/
def compile (t : LambdaIter.LocallyNameless.Tm Empty Φ n) : LambdaSSA.Region Φ :=
  Compile.compile 0 t

variable {τ : Type u} [TypeFormers τ]
variable {Φ : Type q} [HasTy Φ τ]

/-- The compiler preserves exact typing and exposes one result continuation. -/
def compile_hasType {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {t : LambdaIter.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : LambdaIter.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β t A) :
    LambdaSSA.Region.HasType
      (LambdaSSA.LocallyNameless.ToDeBruijn.context β) (compile t) [A] :=
  Compile.compile_hasType h (by simp [LambdaSSA.At])

namespace Named

variable {ν : Type w} [DecidableEq ν]

/-- Resolve binders and erase impossible free names from a well-typed closed
named lambda-iter term. -/
noncomputable def closedTerm {t : LambdaIter.Named.Tm ν Φ} {A : τ}
    (h : LambdaIter.Named.HasType Φ (LambdaIter.Ctx.nil : LambdaIter.Ctx ν τ) t A) :
    Σ t' : LambdaIter.LocallyNameless.Tm Empty Φ 0,
      LambdaIter.LocallyNameless.HasType Φ
        (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) .nil t' A :=
  Closed.erase (NamedToLocallyNameless.chooseHasTypeClosed h)

/-- Compile any exactly typed closed named lambda-iter term. -/
noncomputable def compileTyped {t : LambdaIter.Named.Tm ν Φ} {A : τ}
    (h : LambdaIter.Named.HasType Φ (LambdaIter.Ctx.nil : LambdaIter.Ctx ν τ) t A) :
    LambdaSSA.Region Φ := compile (closedTerm h).1

def compileTyped_hasType {t : LambdaIter.Named.Tm ν Φ} {A : τ}
    (h : LambdaIter.Named.HasType Φ (LambdaIter.Ctx.nil : LambdaIter.Ctx ν τ) t A) :
    LambdaSSA.Region.HasType [] (compileTyped h) [A] :=
  compile_hasType (closedTerm h).2

end Named

end Isotope.LambdaSSA.Translation.Frontend.Core
