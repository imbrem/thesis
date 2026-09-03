import Isotope.LambdaSSA.Translation.Compile
import Isotope.LambdaSSA.Translation.ANF.Elaboration.Subtyping
import Isotope.LambdaSSA.Translation.ANF.ToSSA.Subtyping

/-! # Proof-relevant subtyping preservation for the composed compiler -/

namespace Isotope.LambdaSSA.Translation.Compile.Subtyping

open Isotope.LambdaIter

universe u q

variable {τ : Type u} [TypeFormers τ] [LambdaIter.Subtyping τ]
variable {Φ : Type q} [HasTy Φ τ]

/-- The unchanged raw lambda-iter-to-SSA compiler carries a source subtyping
derivation to a proof-relevant SSA typing derivation. -/
def compile_hasType
    {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {t : LambdaIter.LocallyNameless.Tm Empty Φ n} {A : τ}
    {L : LambdaSSA.LCtx τ} {result : Nat}
    (h : LambdaIter.Subtyping.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β t A)
    (hout : LambdaSSA.At L result A) :
    LambdaSSA.Subtyping.Region.HasType
      (LambdaSSA.LocallyNameless.ToDeBruijn.context β)
      (Compile.compile result t) L :=
  ANF.ToSSA.Subtyping.program_hasType
    (ANF.Subtyping.elaborate_hasType h) hout

/-- A closed compiled program passes its result to its sole result label. -/
def compileClosed_hasType
    {t : LambdaIter.LocallyNameless.Tm Empty Φ 0} {A : τ}
    (h : LambdaIter.Subtyping.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) .nil t A) :
    LambdaSSA.Subtyping.Region.HasType [] (Compile.compile 0 t) [A] :=
  compile_hasType h (by simp [LambdaSSA.At])

end Isotope.LambdaSSA.Translation.Compile.Subtyping
