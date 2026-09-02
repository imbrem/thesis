import Isotope.LambdaCase.Metatheory.Syntax
import Isotope.LambdaCase.TypingSubst

/-!
# The lambda-case equational theory is stable under typed renaming

`Equiv.rename` below transports a lambda-case equation along an exactly typed
bound-variable renaming.  It is what makes composition in the syntactic
category of `Isotope/LambdaCase/Models/SynCategory.lean` well defined on
equivalence classes, and it is *not* needed for initiality.

Lambda-iter gets the corresponding result cheaply, because it factors its
equations through a raw `CoreAxiom` relation with its own `rename`
(`Isotope/LambdaIter/Metatheory/EquivSubst.lean`), and re-attaches endpoint
typing at a single `Eqv.ax` constructor.  Lambda-case has no such factoring:
all fifteen of its axioms are `Equiv` constructors carrying per-subterm typing
witnesses, so a single recursion must both move the renaming past
`instantiate`, `lift`, `underBinder` and `underTwoBinders` in each axiom's raw
shape (the lemmas of `Metatheory/Syntax.lean`) and rebuild every typing witness
under the renaming (`HasType.rename` of `TypingSubst.lean`).

Only renaming is proved here.  Stability under arbitrary pure substitution is
not, and is not needed by anything in this development.
-/

namespace Isotope.LambdaCase.LocallyNameless

variable {τ : Type u} [LambdaIter.TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [LambdaIter.HasTy Φ τ]
variable {ε : Type r} [LambdaIter.HasEff Φ ε]
variable {Γ : Ctx ν τ}

/-- **The lambda-case equational theory is stable under every exactly typed
bound renaming.**

Reflexivity leaves and congruence rules transport structurally; each axiom
transports by rebuilding its typing witnesses under the renaming and using the
commutation lemmas of `Metatheory/Syntax.lean` to put the renamed raw shape
back into the form of the same axiom. -/
theorem Equiv.rename {pureEff : ε} {n m : Nat} {β : BoundCtx τ n}
    {β' : BoundCtx τ m} (ρ : TypedRenaming β β') :
    {a b : Tm ν Φ n} → {A : τ} → Equiv pureEff Γ β a b A →
      Equiv pureEff Γ β' (Tm.rename ρ.toFun a) (Tm.rename ρ.toFun b) A
  | _, _, _, .var h => .var h
  | _, _, _, .bvar (i := i) => ρ.typed i ▸ Equiv.bvar
  | _, _, _, .symm h => .symm (Equiv.rename ρ h)
  | _, _, _, .trans h k => .trans (Equiv.rename ρ h) (Equiv.rename ρ k)
  | _, _, _, .op h => .op (Equiv.rename ρ h)
  | _, _, _, .let₁ ha hb => .let₁ (Equiv.rename ρ ha) (Equiv.rename (ρ.up _) hb)
  | _, _, _, .unit => .unit
  | _, _, _, .pair ha hb => .pair (Equiv.rename ρ ha) (Equiv.rename ρ hb)
  | _, _, _, .let₂ ha hc =>
      .let₂ (Equiv.rename ρ ha) (Equiv.rename ((ρ.up _).up _) hc)
  | _, _, _, .inl ha => .inl (Equiv.rename ρ ha)
  | _, _, _, .inr hb => .inr (Equiv.rename ρ hb)
  | _, _, _, .case he hl hr =>
      .case (Equiv.rename ρ he) (Equiv.rename (ρ.up _) hl)
        (Equiv.rename (ρ.up _) hr)
  | _, _, _, .abort ha => .abort (Equiv.rename ρ ha)
  | _, _, _, .letBeta hp ha hb => by
      simpa using Equiv.letBeta (hp.rename ρ.toFun) (ha.rename ρ)
        (hb.rename (ρ.up _))
  | _, _, _, .letEta ha => by
      simpa using Equiv.letEta (pureEff := pureEff) (ha.rename ρ)
  | _, _, _, .unitEta ha => by
      simpa using Equiv.unitEta (pureEff := pureEff) (ha.rename ρ)
  | _, _, _, .pairBeta ha hb hc => by
      simpa using Equiv.pairBeta (ha.rename ρ) (hb.rename ρ)
        (hc.rename ((ρ.up _).up _))
  | _, _, _, .pairEta ha => by
      simpa using Equiv.pairEta (pureEff := pureEff) (ha.rename ρ)
  | _, _, _, .caseBetaL he hl hr => by
      simpa using Equiv.caseBetaL (he.rename ρ) (hl.rename (ρ.up _))
        (hr.rename (ρ.up _))
  | _, _, _, .caseBetaR he hl hr => by
      simpa using Equiv.caseBetaR (he.rename ρ) (hl.rename (ρ.up _))
        (hr.rename (ρ.up _))
  | _, _, _, .caseEta he => by
      simpa using Equiv.caseEta (pureEff := pureEff) (he.rename ρ)
  | _, _, _, .emptyInitial ha hb hc => by
      simpa using Equiv.emptyInitial (pureEff := pureEff) (ha.rename ρ)
        (hb.rename (ρ.up _)) (hc.rename (ρ.up _))
  | _, _, _, .bindOp ha hc => by
      simpa using Equiv.bindOp (pureEff := pureEff) (ha.rename ρ)
        (hc.rename (ρ.up _))
  | _, _, _, .bindLet ha hb hc => by
      simpa using Equiv.bindLet (pureEff := pureEff) (ha.rename ρ)
        (hb.rename (ρ.up _)) (hc.rename (ρ.up _))
  | _, _, _, .bindLetPair he hc hd => by
      simpa using Equiv.bindLetPair (pureEff := pureEff) (he.rename ρ)
        (hc.rename ((ρ.up _).up _)) (hd.rename (ρ.up _))
  | _, _, _, .bindLetCase he hl hr hd => by
      simpa using Equiv.bindLetCase (pureEff := pureEff) (he.rename ρ)
        (hl.rename (ρ.up _)) (hr.rename (ρ.up _)) (hd.rename (ρ.up _))
  | _, _, _, .bindPair ha hc => by
      simpa using Equiv.bindPair (pureEff := pureEff) (ha.rename ρ)
        (hc.rename ((ρ.up _).up _))
  | _, _, _, .bindCase he hl hr => by
      simpa using Equiv.bindCase (pureEff := pureEff) (he.rename ρ)
        (hl.rename (ρ.up _)) (hr.rename (ρ.up _))

end Isotope.LambdaCase.LocallyNameless
