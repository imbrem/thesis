import Isotope.Elgot.Transformer.Reader
import Isotope.Elgot.Transformer.State
import Isotope.Elgot.Transformer.Writer

/-!
# Elgot-preserving monad transformers

* `Isotope.Elgot.Transformer.Reader` — `ReaderT R m`, iterated pointwise in the environment.
* `Isotope.Elgot.Transformer.State` — `StateT S m`, iterated by threading the state through the
  recursive argument, along the distributor `(B ⊕ A) × S → (B × S) ⊕ (A × S)`.
* `Isotope.Elgot.Transformer.Writer` — `WriterT W m` for a monoid `W`, iterated by threading the
  accumulated output through the recursive argument, seeded at `1`.  Output produced by a
  nonterminating run is discarded along with the run.

Both carry `Iterate` and `LawfulElgotMonad` instances derived from those of `m`.
-/
