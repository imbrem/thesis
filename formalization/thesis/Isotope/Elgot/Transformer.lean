import Isotope.Elgot.Transformer.Reader

/-!
# Elgot-preserving monad transformers

`ReaderT R m` inherits complete Elgot structure from `m`, by iterating pointwise in the
environment.
-/
