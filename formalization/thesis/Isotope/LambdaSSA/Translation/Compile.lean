import Isotope.LambdaSSA.Translation.ANF.Elaboration
import Isotope.LambdaSSA.Translation.ANF.ToSSA

/-! # Composed exact lambda-iter to lambda-SSA compiler -/

namespace Isotope.LambdaSSA.Translation.Compile

open Isotope.LambdaIter

universe u q

/-- Compile a locally nameless exact lambda-iter term with no free names to an
SSA region which passes its result to `result`. -/
def compile (result : Nat) (t : LambdaIter.LocallyNameless.Tm Empty Φ n) :
    LambdaSSA.Region Φ :=
  ANF.ToSSA.program result (ANF.Elaboration.elaborate t)

variable {τ : Type u} [TypeFormers τ]
variable {Φ : Type q} [HasTy Φ τ]

/-- The composed compiler preserves exact typing for arbitrary bound-variable
contexts and arbitrary well-typed result continuations. -/
theorem compile_hasType
    {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {t : LambdaIter.LocallyNameless.Tm Empty Φ n} {A : τ}
    {L : LambdaSSA.LCtx τ} {result : Nat}
    (h : LambdaIter.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β t A)
    (hout : LambdaSSA.At L result A) :
    LambdaSSA.Region.HasType
      (LambdaSSA.LocallyNameless.ToDeBruijn.context β)
      (compile result t) L :=
  ANF.ToSSA.program_hasType (ANF.Elaboration.elaborate_hasType h) hout

/-- A closed compiled program targets its sole result label. -/
theorem compileClosed_hasType
    {t : LambdaIter.LocallyNameless.Tm Empty Φ 0} {A : τ}
    (h : LambdaIter.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) .nil t A) :
    LambdaSSA.Region.HasType [] (compile 0 t) [A] :=
  compile_hasType h (by simp [LambdaSSA.At])

end Isotope.LambdaSSA.Translation.Compile
