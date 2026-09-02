import Isotope.LambdaSSA.Typing
import Isotope.LambdaIter.Subtyping.Semantics.Model

namespace Isotope.LambdaSSA.Semantics.Monadic

open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics

universe u v

/-- Values for a newest-first SSA context, represented in oldest-to-newest
nested-pair order to match the categorical context object. -/
def Env {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ] :
    VCtx τ → Type (max u v)
  | [] => PUnit
  | A :: Γ => Env Γ × TyDen A

/-- Interpret a typed SSA variable lookup. -/
def Env.get {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ] :
    {Γ : VCtx τ} → Env Γ → (i : Nat) → {A : τ} → At Γ i A → TyDen A
  | [], _, _, _, h => by simp [At] at h
  | B :: Γ, ρ, 0, A, h => by
      have e : B = A := by simpa [At] using h
      exact e ▸ ρ.2
  | _ :: _, ρ, i + 1, _, h => Env.get ρ.1 i h

end Isotope.LambdaSSA.Semantics.Monadic
