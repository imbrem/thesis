import Isotope.LambdaIter.Named.Defs
import Isotope.LambdaIter.Weakening
import Isotope.LambdaIter.Context.Shadowing

/-!
# Contexts for named lambda-iter

The named presentation uses the shared `LambdaIter.Ctx`: contexts are snoc
lists, the newest binder is at the right, anonymous slots remain present but
cannot be referenced, and lookup selects the newest visible binding.
-/

namespace Isotope.LambdaIter.Named

abbrev Ctx := Isotope.LambdaIter.Ctx

end Isotope.LambdaIter.Named
