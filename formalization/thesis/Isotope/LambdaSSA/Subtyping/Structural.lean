import Isotope.LambdaSSA.Subtyping.Typing
import Isotope.LambdaSSA.Structural

namespace Isotope.LambdaSSA.Subtyping

open Isotope.LambdaIter

variable [TypeFormers τ] [LambdaIter.Subtyping τ] [HasTy Φ τ]

def Tm.HasType.rename {Γ Δ : LambdaSSA.VCtx τ} {a : LambdaSSA.Tm Φ} {A : τ}
    {ρ : Nat → Nat} (hρ : LambdaSSA.Ren Γ Δ ρ) :
    Tm.HasType Γ a A → Tm.HasType Δ (a.rename ρ) A
  | .var h => .var (hρ h)
  | .op h => .op (h.rename hρ)
  | .let₁ ha hb => .let₁ (ha.rename hρ) (hb.rename (hρ.lift _))
  | .pair ha hb => .pair (ha.rename hρ) (hb.rename hρ)
  | .unit => .unit
  | .let₂ ha hb => .let₂ (ha.rename hρ) (hb.rename ((hρ.lift _).lift _))
  | .inl h => .inl (h.rename hρ)
  | .inr h => .inr (h.rename hρ)
  | .case he hl hr => .case (he.rename hρ)
      (hl.rename (hρ.lift _)) (hr.rename (hρ.lift _))
  | .abort h => .abort (h.rename hρ)
  | .sub h hAB => .sub (h.rename hρ) hAB

def Region.HasType.renameVars {Γ Δ : LambdaSSA.VCtx τ}
    {r : LambdaSSA.Region Φ} {L : LambdaSSA.LCtx τ} {ρ : Nat → Nat}
    (hρ : LambdaSSA.Ren Γ Δ ρ) :
    Region.HasType Γ r L → Region.HasType Δ (r.renameVars ρ) L
  | .br h ha => .br h (ha.rename hρ)
  | .case he hl hr => .case (he.rename hρ)
      (hl.renameVars (hρ.lift _)) (hr.renameVars (hρ.lift _))
  | .let₁ ha hr => .let₁ (ha.rename hρ) (hr.renameVars (hρ.lift _))
  | .let₂ ha hr => .let₂ (ha.rename hρ) (hr.renameVars ((hρ.lift _).lift _))
  | .cfg R he hb => .cfg R (he.renameVars hρ)
      (fun i => (hb i).renameVars (hρ.lift _))

end Isotope.LambdaSSA.Subtyping
