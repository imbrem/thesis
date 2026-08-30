import Isotope.LambdaIter.Semantics.Purity
import Isotope.LambdaIter.LocallyNameless.TypingSubst

/-! # Semantics of typed renaming and substitution -/

namespace Isotope.LambdaIter.Semantics

open Isotope.LambdaIter.LocallyNameless

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m] [Elgot.Iterate m]
variable [InstructionModel Φ τ ε m]

namespace BoundDen

/-- Reconstruct an environment from its newest-first dependent `Fin` view. -/
def ofFun : {n : Nat} → (β : BoundCtx τ n) →
    ((i : Fin n) → TyDen (β.get i)) → BoundDen β
  | 0, .nil, _ => PUnit.unit
  | _ + 1, .snoc β A, f =>
      (ofFun β (fun i => f i.succ), f 0)

@[simp] theorem get_ofFun {n : Nat} (β : BoundCtx τ n)
    (f : (i : Fin n) → TyDen (β.get i)) (i : Fin n) :
    get (ofFun β f) i = f i := by
  induction β with
  | nil => exact Fin.elim0 i
  | snoc β A ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact ih (fun k => f k.succ) j

/-- Pull a target environment back along a type-preserving index renaming. -/
def pull {n k : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ k}
    (r : TypedRenaming β β') (ρ : BoundDen β') : BoundDen β :=
  ofFun β fun i => r.typed i ▸ get ρ (r.toFun i)

@[simp] theorem get_pull {n k : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ k}
    (r : TypedRenaming β β') (ρ : BoundDen β') (i : Fin n) :
    get (pull r ρ) i = r.typed i ▸ get ρ (r.toFun i) :=
  get_ofFun β _ i

@[simp] theorem pull_up {n k : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ k}
    (r : TypedRenaming β β') (ρ : BoundDen β') (A : τ) (a : TyDen A) :
    pull (r.up A) (ρ, a) = (pull r ρ, a) := by
  apply Prod.ext
  · apply congrArg (ofFun β)
    funext i
    rfl
  · rfl

end BoundDen

end Isotope.LambdaIter.Semantics
