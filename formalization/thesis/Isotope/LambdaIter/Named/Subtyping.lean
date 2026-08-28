import Isotope.LambdaIter.Named.Context

/-! # Instruction subtyping for named lambda-iter -/

namespace Isotope.LambdaIter.Named

/-- Thesis instruction typing: accepted inputs vary contravariantly from the
declared source and returned results vary covariantly from the declared target. -/
structure InstTy [TypeFormers τ] [Subtyping τ] [HasTy Φ τ]
    (f : Φ) (A B : τ) : Type _ where
  input : Subty A (instrSrc f)
  output : Subty (instrTrg f) B

end Isotope.LambdaIter.Named
