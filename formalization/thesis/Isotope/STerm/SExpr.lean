import Isotope.SExp.Defs
import Isotope.STerm.Defs

namespace Isotope

open STerm

namespace SExp

variable {A}

@[simp]
def toTerm : SExp A → STerm Unit A
  | .atom a => .atom a
  | .par es => .op () (fun i => toTerm (es i))

-- @[simp]
-- theorem toTerm_parL (es : List (SExp A))
--   : toTerm (parL es) = .opL () (toTerm <$> es) := by
--   simp only [parL, toTerm, opL]
--   have hes : (fun i => (es.get (i.cast (by simp [Functor.map]))).toTerm) = (toTerm <$> es).get
--     := by ext i; simp [Functor.map]
--   rw [<-hes]
--   clear hes
--   sorry

end SExp

open SExp

namespace STerm

variable {O A E}

-- TODO: map to S-expressions, turning ops ==> atoms

end STerm

end Isotope
