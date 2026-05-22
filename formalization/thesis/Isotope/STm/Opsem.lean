import Isotope.STm.Defs

namespace Isotope

namespace STm

variable {Arity} [instArgs : Args Arity] {L : Lang Arity} {A}

class OpSem (L : Lang Arity) where
  step : STm L Empty -> STm L A

end STm

end Isotope
