import Isotope.LambdaIter.NoSubtyping.Metatheory.Syntax

/-! Renaming and substitution of the complete no-subtyping equality theory. -/

namespace Isotope.LambdaIter.NoSubtyping.LocallyNameless

open Isotope.LambdaIter.LocallyNameless
open Isotope.LambdaIter.LocallyNameless.Tm
open Syntax

variable {τ : Type u} [TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] {pureEff : ε}
variable {Γ : LambdaIter.Ctx ν τ}

namespace Pure

/-- Syntactic purity is stable under arbitrary bound renaming. -/
def rename (ρ : Fin n → Fin m) : {a : Tm ν Φ n} →
    Pure pureEff a → Pure pureEff (Tm.rename ρ a)
  | _, .fv => .fv
  | _, .bv => .bv
  | _, .op hf h => .op hf (rename ρ h)
  | _, .let₁ ha hb => .let₁ (rename ρ ha) (rename (upRen ρ) hb)
  | _, .unit => .unit
  | _, .pair ha hb => .pair (rename ρ ha) (rename ρ hb)
  | _, .let₂ ha hb => .let₂ (rename ρ ha) (rename (upRen (upRen ρ)) hb)
  | _, .inl h => .inl (rename ρ h)
  | _, .inr h => .inr (rename ρ h)
  | _, .case he hl hr =>
      .case (rename ρ he) (rename (upRen ρ) hl) (rename (upRen ρ) hr)
  | _, .abort h => .abort (rename ρ h)

end Pure

namespace StructuralAxiom

def rename (ρ : Fin n → Fin m) : {a b : Tm ν Φ n} →
    StructuralAxiom pureEff a b →
      StructuralAxiom pureEff (Tm.rename ρ a) (Tm.rename ρ b)
  | _, _, .letBeta hp => by
      simpa using StructuralAxiom.letBeta (hp.rename ρ)
  | _, _, .letEta _ => .letEta _
  | _, _, .unitEta _ => .unitEta _
  | _, _, .pairBeta _ _ _ => by
      simpa using StructuralAxiom.pairBeta
        (Tm.rename ρ _) (Tm.rename ρ _) (Tm.rename (upRen (upRen ρ)) _)
  | _, _, .pairEta _ => .pairEta _
  | _, _, .caseBetaL _ _ _ => .caseBetaL _ _ _
  | _, _, .caseBetaR _ _ _ => .caseBetaR _ _ _
  | _, _, .caseEta _ => .caseEta _
  | _, _, .emptyInitial _ _ _ => .emptyInitial _ _ _

end StructuralAxiom

namespace SequencingAxiom

def rename (ρ : Fin n → Fin m) : {a b : Tm ν Φ n} →
    SequencingAxiom pureEff a b →
      SequencingAxiom pureEff (Tm.rename ρ a) (Tm.rename ρ b)
  | _, _, .bindOp _ _ => by
      simpa using SequencingAxiom.bindOp (pureEff := pureEff)
        (Tm.rename ρ _) (Tm.rename (upRen ρ) _)
  | _, _, .bindLet _ _ _ => by
      simpa using SequencingAxiom.bindLet (pureEff := pureEff)
        (Tm.rename ρ _) (Tm.rename (upRen ρ) _) (Tm.rename (upRen ρ) _)
  | _, _, .bindLetPair _ _ _ => by
      simpa using SequencingAxiom.bindLetPair (pureEff := pureEff)
        (Tm.rename ρ _) (Tm.rename (upRen (upRen ρ)) _) (Tm.rename (upRen ρ) _)
  | _, _, .bindLetCase _ _ _ _ => by
      simpa using SequencingAxiom.bindLetCase (pureEff := pureEff)
        (Tm.rename ρ _) (Tm.rename (upRen ρ) _) (Tm.rename (upRen ρ) _)
        (Tm.rename (upRen ρ) _)
  | _, _, .bindPair _ _ => by
      simpa using SequencingAxiom.bindPair (pureEff := pureEff)
        (Tm.rename ρ _) (Tm.rename (upRen (upRen ρ)) _)
  | _, _, .bindCase _ _ _ => by
      simpa using SequencingAxiom.bindCase (pureEff := pureEff)
        (Tm.rename ρ _) (Tm.rename (upRen ρ) _) (Tm.rename (upRen ρ) _)

end SequencingAxiom

namespace IterationAxiom

def rename (ρ : Fin n → Fin m) : {a b : Tm ν Φ n} →
    IterationAxiom pureEff a b →
      IterationAxiom pureEff (Tm.rename ρ a) (Tm.rename ρ b)
  | _, _, .fixpoint _ _ => by
      simpa using IterationAxiom.fixpoint (pureEff := pureEff)
        (Tm.rename ρ _) (Tm.rename (upRen ρ) _)
  | _, _, .naturality _ _ _ => by
      simpa using IterationAxiom.naturality (pureEff := pureEff)
        (Tm.rename ρ _) (Tm.rename (upRen ρ) _) (Tm.rename (upRen ρ) _)
  | _, _, .codiagonal _ _ => by
      simpa using IterationAxiom.codiagonal (pureEff := pureEff)
        (Tm.rename ρ _) (Tm.rename (upRen ρ) _)
  | _, _, .iterBind _ _ => by
      simpa using IterationAxiom.iterBind (pureEff := pureEff)
        (Tm.rename ρ _) (Tm.rename (upRen ρ) _)

end IterationAxiom

namespace CoreAxiom

def rename (ρ : Fin n → Fin m) : {a b : Tm ν Φ n} → CoreAxiom pureEff a b →
    CoreAxiom pureEff (Tm.rename ρ a) (Tm.rename ρ b)
  | _, _, .structural h => .structural (h.rename ρ)
  | _, _, .sequencing h => .sequencing (h.rename ρ)
  | _, _, .iteration h => .iteration (h.rename ρ)

end CoreAxiom

namespace Eqv

/-- The complete typed equational theory is stable under every exactly typed
bound-variable renaming. -/
def rename {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    (ρ : TypedRenaming β β') :
    {a b : Tm ν Φ n} → {A : τ} → Eqv pureEff Γ β a b A →
      Eqv pureEff Γ β' (Tm.rename ρ.toFun a) (Tm.rename ρ.toFun b) A
  | _, _, _, .refl h => .refl (HasType.rename ρ h)
  | _, _, _, .symm h => .symm (rename ρ h)
  | _, _, _, .trans h k => .trans (rename ρ h) (rename ρ k)
  | _, _, _, .op h => .op (rename ρ h)
  | _, _, _, .let₁ ha hb => .let₁ (rename ρ ha) (rename (ρ.up _) hb)
  | _, _, _, .unit => .unit
  | _, _, _, .pair ha hb => .pair (rename ρ ha) (rename ρ hb)
  | _, _, _, .let₂ he hc => .let₂ (rename ρ he) (rename ((ρ.up _).up _) hc)
  | _, _, _, .inl h => .inl (rename ρ h)
  | _, _, _, .inr h => .inr (rename ρ h)
  | _, _, _, .case he hl hr =>
      .case (rename ρ he) (rename (ρ.up _) hl) (rename (ρ.up _) hr)
  | _, _, _, .abort h => .abort (rename ρ h)
  | _, _, _, .iter ha hb => .iter (rename ρ ha) (rename (ρ.up _) hb)
  | _, _, _, .ax hax ha hb =>
      .ax (hax.rename ρ.toFun) (HasType.rename ρ ha) (HasType.rename ρ hb)
  | _, _, _, .uniformity ha hh hp hb hb' square => by
      refine Eqv.uniformity
        (HasType.rename ρ ha)
        (HasType.rename (ρ.up _) hh)
        (hp.rename (upRen ρ.toFun))
        (HasType.rename (ρ.up _) hb)
        (HasType.rename (ρ.up _) hb')
        ?_
      convert rename (ρ.up _) square using 1 <;>
        simp only [TypedRenaming.up, Syntax.rename_case, Syntax.rename_inl,
          Syntax.rename_inr, Syntax.rename_bv, Syntax.rename_underBinder,
          Syntax.rename_instantiate, Syntax.upRen_zero] <;>
        congr 1 <;>
        first
        | (apply Syntax.rename_congr; intro i; rfl)
        | (change (Tm.rename (upRen ρ.toFun) _).underBinder.inr =
              (Tm.rename (upRen (upRen ρ.toFun)) _).inr
           exact congrArg Tm.inr (Syntax.rename_underBinder ρ.toFun _).symm)
        | (change (Tm.rename (upRen ρ.toFun) _).underBinder =
              Tm.rename (upRen (upRen ρ.toFun)) _
           exact (Syntax.rename_underBinder ρ.toFun _).symm)

end Eqv

end Isotope.LambdaIter.NoSubtyping.LocallyNameless
