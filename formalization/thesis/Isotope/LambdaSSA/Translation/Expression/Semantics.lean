import Isotope.LambdaSSA.Translation.FromSSA
import Isotope.LambdaSSA.Semantics.Monadic.Term
import Isotope.LambdaIter.Subtyping.Semantics.Denotation

/-! # Direct semantics of the SSA/exact-expression bridge -/

namespace Isotope.LambdaSSA.Translation.Expression.Semantics

set_option autoImplicit true
set_option relaxedAutoImplicit true

open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics

universe u v q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Isotope.Elgot.Iterate m] [InstructionModel Φ τ ε m]

@[simp] def envToBound : {Γ : LambdaSSA.VCtx τ} →
    LambdaSSA.Semantics.Monadic.Env Γ → BoundDen (FromSSA.boundContext Γ)
  | [], _ => PUnit.unit
  | _ :: _, ρ => (envToBound ρ.1, ρ.2)

/-- Evidence that a generic derivation is exactly the constructor-preserving
embedding of an exact derivation.  In particular this relation has no `sub`
constructor. -/
inductive ExactGeneric {ν : Type*} [DecidableEq ν] : {n : Nat} →
    {Γ : Ctx ν τ} → {β : LambdaIter.LocallyNameless.BoundCtx τ n} →
    {t : LambdaIter.LocallyNameless.Tm ν Φ n} → {A : τ} →
    LambdaIter.LocallyNameless.HasType Φ Γ β t A →
    LambdaIter.Subtyping.LocallyNameless.HasType Φ Γ β t A → Prop where
  | fv : ExactGeneric (.fv h) (.fv h)
  | bv : ExactGeneric .bv .bv
  | op : ExactGeneric ha ga → ExactGeneric (.op ha) (.op ga)
  | let₁ : ExactGeneric ha ga → ExactGeneric hb gb →
      ExactGeneric (.let₁ ha hb) (.let₁ ga gb)
  | unit : ExactGeneric .unit .unit
  | pair : ExactGeneric ha ga → ExactGeneric hb gb →
      ExactGeneric (.pair ha hb) (.pair ga gb)
  | let₂ : ExactGeneric ha ga → ExactGeneric hb gb →
      ExactGeneric (.let₂ ha hb) (.let₂ ga gb)
  | inl : ExactGeneric ha ga → ExactGeneric (.inl ha) (.inl ga)
  | inr : ExactGeneric hb gb → ExactGeneric (.inr hb) (.inr gb)
  | case : ExactGeneric he ge → ExactGeneric hl gl → ExactGeneric hr gr →
      ExactGeneric (.case he hl hr) (.case ge gl gr)
  | abort : ExactGeneric ha ga → ExactGeneric (.abort ha) (.abort ga)
  | iter : ExactGeneric ha ga → ExactGeneric hb gb →
      ExactGeneric (.iter ha hb) (.iter ga gb)

end Isotope.LambdaSSA.Translation.Expression.Semantics
