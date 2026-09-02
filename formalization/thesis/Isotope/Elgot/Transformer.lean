import Isotope.Elgot.Transformer.Reader
import Isotope.Elgot.Transformer.State

/-!
# Elgot-preserving monad transformers

* `Isotope.Elgot.Transformer.Reader` — `ReaderT R m`, iterated pointwise in the environment.
* `Isotope.Elgot.Transformer.State` — `StateT S m`, iterated by threading the state through the
  recursive argument, along the distributor `(B ⊕ A) × S → (B × S) ⊕ (A × S)`.

Both carry `Iterate` and `LawfulElgotMonad` instances derived from those of `m`.
-/
