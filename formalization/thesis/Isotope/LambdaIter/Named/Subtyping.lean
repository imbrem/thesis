import Isotope.LambdaIter.Named.Context

/-! # Instruction subtyping for named lambda-iter -/

namespace Isotope.LambdaIter.Named

/-- Thesis instruction typing: accepted inputs vary contravariantly from the
declared source and returned results vary covariantly from the declared target. -/
structure InstTy [TypeFormers τ] [Subtyping τ] (S : Signature τ)
    (f : S.Op) (A B : τ) : Type _ where
  input : Subty A (S.src f)
  output : Subty (S.trg f) B

end Isotope.LambdaIter.Named
