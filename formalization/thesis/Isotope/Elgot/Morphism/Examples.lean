import Isotope.Elgot.Morphism
import Isotope.Elgot.Transformer.Reader
import Isotope.Elgot.TraceSet.Compare

/-!
# Two more families of Elgot morphisms

* **Reading the environment at a fixed value.**  `ReaderT R m → m`, `x ↦ x r`.
  Every law is `rfl`, because `ReaderT`'s monad *and* iteration operators are
  defined pointwise in the environment.  Distinct environments give distinct
  morphisms as soon as the base monad has two distinct values
  (`Transformer.Reader.evalHom_injective`), so this is the standard supply of
  *parallel* morphisms that differ.
* **The deterministic trace model inside the nondeterministic one.**
  `FiniteTrace Sigma → TraceSet (FreeMonoid Sigma) Tau`, sending a terminating
  computation to the singleton of its trace and divergence to `∅`.  The three
  laws are already proved in `Isotope/Elgot/TraceSet/Compare.lean`; this file
  only packages them.  The packaging matters because it makes the embedding
  usable as a morphism of *models*.
-/

namespace Isotope.Elgot

universe u

namespace Transformer.Reader

variable {R : Type u} {m : Type u → Type u} [Monad m] [Iterate m]

/-- **Evaluation at a fixed environment is an Elgot morphism `ReaderT R m → m`.**
All three laws hold definitionally: `ReaderT` sequences and iterates pointwise
in the environment. -/
def evalHom (r : R) : ElgotHom (ReaderT R m) m where
  app x := x r
  app_pure _ := rfl
  app_bind _ _ := rfl
  app_iter _ _ := rfl

@[simp] theorem evalHom_app (r : R) {A : Type u} (x : ReaderT R m A) :
    (evalHom r).app x = x r := rfl

/-- **Distinct environments give distinct morphisms.**  So the hom-sets of
Elgot morphisms are not subsingletons: this is a genuinely parallel pair. -/
theorem evalHom_ne [DecidableEq R] {r₁ r₂ : R} (hr : r₁ ≠ r₂) {A : Type u}
    {y z : m A} (hyz : y ≠ z) :
    (evalHom (m := m) r₁) ≠ evalHom r₂ := by
  intro h
  have := congrArg (fun φ => φ.app (A := A) (fun r => if r = r₁ then y else z)) h
  simp only [evalHom_app, if_neg (Ne.symm hr)] at this
  exact hyz this

end Transformer.Reader

variable {Sigma Tau : Type u} [MulAction (FreeMonoid Sigma) Tau]

/-- **The deterministic finite-trace model embeds in trace sets**, as an Elgot
morphism.  Iteration is preserved on the nose because both models discard the
traces of productive infinite loops. -/
noncomputable def FiniteTrace.toTraceSetHom :
    ElgotHom (FiniteTrace Sigma) (TraceSet (FreeMonoid Sigma) Tau) where
  app x := x.toTraceSet
  app_pure a := FiniteTrace.toTraceSet_pure a
  app_bind x f := FiniteTrace.toTraceSet_bind x f
  app_iter f a := FiniteTrace.toTraceSet_iter f a

@[simp] theorem FiniteTrace.toTraceSetHom_app {A : Type u} (x : FiniteTrace Sigma A) :
    (toTraceSetHom (Tau := Tau)).app x = x.toTraceSet := rfl

/-- The embedding is injective, hence a non-degenerate comparison. -/
theorem FiniteTrace.toTraceSetHom_injective {A : Type u} :
    Function.Injective ((toTraceSetHom (Sigma := Sigma) (Tau := Tau)).app (A := A)) :=
  toTraceSet_injective

end Isotope.Elgot
