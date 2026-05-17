import Mathlib.Data.Set.Basic

import Isotope.Args.Defs

namespace Isotope

universe uargs

variable {Arity : Type uargs} [instArgs : Args Arity]

instance Args.instSet {S : Set Arity} : Args S where
  Ix n := Ix n.val

instance Args.Hom.setToVal {S : Set Arity} : Args.Hom S Arity where
  mapArgs n := n
  mapIx i := i

end Isotope
