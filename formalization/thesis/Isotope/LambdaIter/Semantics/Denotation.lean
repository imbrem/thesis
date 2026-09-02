import Isotope.LambdaIter.Metatheory
import Isotope.LambdaIter.Subtyping.Semantics.Denotation

/-! # Monadic denotation for coercion-free lambda-iter -/

namespace Isotope.LambdaIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]

/-- Embed an exact derivation into the proof-relevant generic judgment without
introducing any coercion node. -/
@[simp] def HasType.toGeneric : {Γ : Ctx ν τ} → {n : Nat} →
    {β : BoundCtx τ n} → {t : Tm ν Φ n} → {A : τ} → HasType Φ Γ β t A →
      Subtyping.LocallyNameless.HasType Φ Γ β t A
  | _, _, _, _, _, .fv h => .fv h
  | _, _, _, _, _, .bv => .bv
  | _, _, _, _, _, .op h => .op h.toGeneric
  | _, _, _, _, _, .let₁ ha hb => .let₁ ha.toGeneric hb.toGeneric
  | _, _, _, _, _, .unit => .unit
  | _, _, _, _, _, .pair ha hb => .pair ha.toGeneric hb.toGeneric
  | _, _, _, _, _, .let₂ ha hc => .let₂ ha.toGeneric hc.toGeneric
  | _, _, _, _, _, .inl h => .inl h.toGeneric
  | _, _, _, _, _, .inr h => .inr h.toGeneric
  | _, _, _, _, _, .case he hl hr => .case he.toGeneric hl.toGeneric hr.toGeneric
  | _, _, _, _, _, .abort h => .abort h.toGeneric
  | _, _, _, _, _, .iter ha hb => .iter ha.toGeneric hb.toGeneric

end Isotope.LambdaIter.LocallyNameless

namespace Isotope.LambdaIter.Semantics

open Isotope.LambdaIter.LocallyNameless
open Isotope.LambdaIter.Subtyping.Semantics

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m] [Isotope.Elgot.Iterate m]
variable [InstructionModel Φ τ ε m]

/-- Monadic denotation of an exact derivation, with no semantic coercions. -/
def denote {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β t A) : CtxDen Γ → BoundDen β → m (TyDen A) :=
  Subtyping.Semantics.denote (ε := ε) (m := m) h.toGeneric

/-- Optional coherence of monadic denotation with respect to exact typing
witnesses.  As in the categorical model this need not follow from arbitrary,
possibly non-injective object-language type formers. -/
class TypingCoherent : Prop where
  denote_eq {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
      {t : Tm ν Φ n} {A : τ} (h k : HasType Φ Γ β t A) :
    denote (ε := ε) (m := m) h = denote (ε := ε) (m := m) k

end Isotope.LambdaIter.Semantics
