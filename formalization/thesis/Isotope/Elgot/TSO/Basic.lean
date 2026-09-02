import Isotope.Elgot.TSO.Alphabet
import Isotope.Elgot.WS
import Isotope.Elgot.Kleisli

/-!
# The SPARC TSO monad

`TSO Loc Val = StateT Buf (Traces Σ)` with `Σ` the concatenation monoid of finite TSO
pomsets, i.e. `WS (Buf Loc Val) (Pom (Act Loc Val))`.  Its Kleisli category is the paper's
`Set_TSO` (`denotational-semantics-of-ssa.tex` L4823-4825, L4854).

Everything lands in `Type u → Type u` with `Loc Val : Type u` fully polymorphic, so the
Elgot infrastructure of `Isotope.Elgot.Basic` applies without any `ULift`.

## Honest boundary

Paper erratum: L4823-4825 writes `TSO = StateT Buf (Trace Σ)`, but `Trace Σ = TraceT Σ Id`
is deterministic and cannot carry the set-valued denotations of L4845/L4853 or the hom-sets
`Set_TSO(A,B)` of L4854.  It must read `Traces Σ`.  We use the partial-correctness
set-valued monad `WS`; see `Isotope.Elgot.WS` for what that costs.
-/

universe u

namespace Isotope.Elgot

open Isotope.Pomset TSO

/-- The SPARC TSO monad: a write buffer as state, finite TSO pomsets as effects, and
nondeterministic (partial-correctness) results. -/
abbrev TSO (Loc Val : Type u) : Type u → Type u := WS (Buf Loc Val) (Pom (Act Loc Val))

variable {Loc Val : Type u}

example : _root_.Monad (TSO Loc Val) := inferInstance
example : LawfulMonad (TSO Loc Val) := inferInstance
example : Iterate (TSO Loc Val) := inferInstance
example : LawfulElgotMonad (TSO Loc Val) := inferInstance

end Isotope.Elgot
