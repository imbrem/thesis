import Isotope.Elgot.ITree.Basic
import Isotope.Elgot.ITree.Monad
import Isotope.Elgot.ITree.Iteration
import Isotope.Elgot.ITree.Laws

/-!
# Weak interaction trees

The implementation provides a universe-polymorphic event signature, `Ret`,
`Vis`, silent `Tau`, silent divergence, a lawful monad, productive complete
iteration, and its defining fixpoint law.  Equality is extensional equality of
all coherent finite observations, exposed by `Tree.eq_iff_observe`.

The remaining Conway laws (naturality, codiagonal, and pure-map uniformity)
are deliberately not installed as a `LawfulElgotMonad` instance until their
finite-observation proofs are complete.  In particular, this module contains
no postulated laws and does not claim strong/Tau-counting bisimilarity.
-/
