import Isotope.LambdaCase.Metatheory
import Isotope.LambdaIter.Metatheory

/-!
# The lambda-case equational theory embeds into the lambda-iter one

`Isotope.LambdaCase.LocallyNameless.Tm.embed` is the constructor-preserving
inclusion of lambda-case terms into lambda-iter terms, and
`LambdaCase.LocallyNameless.HasType.embed` transports typing along it.  This
file supplies the two remaining pieces:

* `Pure.embed`, purity along the inclusion for the exact judgment (the
  subtyping variant already had it);
* `Equiv.embedIter`, **stability of the lambda-case equational theory under the
  inclusion**: every lambda-case equation is a lambda-iter equation between the
  embedded terms.

The comment at the end of `Isotope/LambdaCase/Equiv.lean` records this as
deferred "until endpoint-typing transport is available for every commuting
conversion".  It is available: lambda-case's fifteen axioms are exactly
lambda-iter's `StructuralAxiom` and `SequencingAxiom` schemes, so each case is
a single `Eqv.ax` whose two endpoint derivations are rebuilt from the typing
witnesses the lambda-case constructor already carries, together with
`HasType.newest`, `HasType.previous`, `HasType.lift`, `HasType.underBinder`,
`HasType.underTwoBinders` and `HasType.instantiate` on the lambda-iter side.
The raw shapes match on the nose because `Tm.embed` commutes with `lift`,
`underBinder`, `underTwoBinders` and `instantiate` (`@[simp]` lemmas in
`Isotope/LambdaCase/Syntax.lean`).

Note what this is *not*: it is a map of derivations in one direction only.  No
converse (conservativity of lambda-iter over lambda-case) is proved here.
-/

namespace Isotope.LambdaCase.LocallyNameless

open Isotope.LambdaIter.LocallyNameless (Eqv)

variable {τ : Type u} [LambdaIter.TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [LambdaIter.HasTy Φ τ]
variable {ε : Type r} [LambdaIter.HasEff Φ ε]
variable {Γ : Ctx ν τ}

omit [DecidableEq ν] in
/-- Purity is preserved by the inclusion into lambda-iter. -/
theorem Pure.embed {pureEff : ε} : {n : Nat} → {t : Tm ν Φ n} →
    Pure pureEff t → LambdaIter.LocallyNameless.Pure pureEff (Tm.embed t)
  | _, _, .fv => .fv
  | _, _, .bv => .bv
  | _, _, .op hf ha => .op hf ha.embed
  | _, _, .let₁ ha hb => .let₁ ha.embed hb.embed
  | _, _, .unit => .unit
  | _, _, .pair ha hb => .pair ha.embed hb.embed
  | _, _, .let₂ ha hb => .let₂ ha.embed hb.embed
  | _, _, .inl ha => .inl ha.embed
  | _, _, .inr ha => .inr ha.embed
  | _, _, .case he hl hr => .case he.embed hl.embed hr.embed
  | _, _, .abort ha => .abort ha.embed

/-- **Every exact lambda-case equation is an exact lambda-iter equation between
the embedded terms.**

The three reflexivity leaves become `Eqv.refl`, the eleven congruence rules
become the corresponding lambda-iter congruence rules, and each of the fifteen
axioms becomes `Eqv.ax` at the matching `StructuralAxiom` or `SequencingAxiom`
scheme, with both endpoint typing derivations reconstructed from the witnesses
the lambda-case constructor carries. -/
theorem Equiv.embedIter {pureEff : ε} {n : Nat} {β : BoundCtx τ n}
    {a b : Tm ν Φ n} {A : τ} : Equiv pureEff Γ β a b A →
      Eqv pureEff Γ β (Tm.embed a) (Tm.embed b) A
  | .var h => .refl (.fv h)
  | .bvar => .refl .bv
  | .symm h => .symm h.embedIter
  | .trans h k => .trans h.embedIter k.embedIter
  | .op h => .op h.embedIter
  | .let₁ ha hb => .let₁ ha.embedIter hb.embedIter
  | .unit => .unit
  | .pair ha hb => .pair ha.embedIter hb.embedIter
  | .let₂ ha hc => .let₂ ha.embedIter hc.embedIter
  | .inl ha => .inl ha.embedIter
  | .inr hb => .inr hb.embedIter
  | .case he hl hr => .case he.embedIter hl.embedIter hr.embedIter
  | .abort ha => .abort ha.embedIter
  | .letBeta hp ha hb => by
      simpa only [Tm.embed, Tm.embed_instantiate] using
        Eqv.ax (pureEff := pureEff) (.structural (.letBeta hp.embed))
          (.let₁ ha.embed hb.embed) (hb.embed.instantiate ha.embed)
  | .letEta ha => by
      simpa only [Tm.embed] using
        Eqv.ax (pureEff := pureEff) (.structural (.letEta _))
          (.let₁ ha.embed .newest) ha.embed
  | .unitEta ha => by
      simpa only [Tm.embed] using
        Eqv.ax (pureEff := pureEff) (.structural (.unitEta _))
          (.let₁ ha.embed .unit) ha.embed
  | .pairBeta ha hb hc => by
      simpa only [Tm.embed, Tm.embed_lift] using
        Eqv.ax (pureEff := pureEff) (.structural (.pairBeta _ _ _))
          (.let₂ (.pair ha.embed hb.embed) hc.embed)
          (.let₁ ha.embed (.let₁ hb.embed.lift hc.embed))
  | .pairEta ha => by
      simpa only [Tm.embed] using
        Eqv.ax (pureEff := pureEff) (.structural (.pairEta _))
          (.let₂ ha.embed (.pair .previous .newest)) ha.embed
  | .caseBetaL he hl hr => by
      simpa only [Tm.embed] using
        Eqv.ax (pureEff := pureEff) (.structural (.caseBetaL _ _ _))
          (.case (.inl he.embed) hl.embed hr.embed) (.let₁ he.embed hl.embed)
  | .caseBetaR he hl hr => by
      simpa only [Tm.embed] using
        Eqv.ax (pureEff := pureEff) (.structural (.caseBetaR _ _ _))
          (.case (.inr he.embed) hl.embed hr.embed) (.let₁ he.embed hr.embed)
  | .caseEta he => by
      simpa only [Tm.embed] using
        Eqv.ax (pureEff := pureEff) (.structural (.caseEta _))
          (.case he.embed (.inl .newest) (.inr .newest)) he.embed
  | .emptyInitial ha hb hc => by
      simpa only [Tm.embed] using
        Eqv.ax (pureEff := pureEff) (.structural (.emptyInitial _ _ _))
          (.let₁ (.abort ha.embed) hb.embed) (.let₁ (.abort ha.embed) hc.embed)
  | .bindOp ha hc => by
      simpa only [Tm.embed, Tm.embed_underBinder] using
        Eqv.ax (pureEff := pureEff) (.sequencing (.bindOp _ _))
          (.let₁ (.op ha.embed) hc.embed)
          (.let₁ ha.embed (.let₁ (.op .newest) hc.embed.underBinder))
  | .bindLet ha hb hc => by
      simpa only [Tm.embed, Tm.embed_underBinder] using
        Eqv.ax (pureEff := pureEff) (.sequencing (.bindLet _ _ _))
          (.let₁ (.let₁ ha.embed hb.embed) hc.embed)
          (.let₁ ha.embed (.let₁ hb.embed hc.embed.underBinder))
  | .bindLetPair he hc hd => by
      simpa only [Tm.embed, Tm.embed_underBinder] using
        Eqv.ax (pureEff := pureEff) (.sequencing (.bindLetPair _ _ _))
          (.let₁ (.let₂ he.embed hc.embed) hd.embed)
          (.let₂ he.embed (.let₁ hc.embed hd.embed.underBinder.underBinder))
  | .bindLetCase he hl hr hd => by
      simpa only [Tm.embed, Tm.embed_underBinder] using
        Eqv.ax (pureEff := pureEff) (.sequencing (.bindLetCase _ _ _ _))
          (.let₁ (.case he.embed hl.embed hr.embed) hd.embed)
          (.case he.embed (.let₁ hl.embed hd.embed.underBinder)
            (.let₁ hr.embed hd.embed.underBinder))
  | .bindPair ha hc => by
      simpa only [Tm.embed, Tm.embed_underTwoBinders] using
        Eqv.ax (pureEff := pureEff) (.sequencing (.bindPair _ _))
          (.let₂ ha.embed hc.embed)
          (.let₁ ha.embed (.let₂ .newest hc.embed.underTwoBinders))
  | .bindCase he hl hr => by
      simpa only [Tm.embed, Tm.embed_underBinder] using
        Eqv.ax (pureEff := pureEff) (.sequencing (.bindCase _ _ _))
          (.case he.embed hl.embed hr.embed)
          (.let₁ he.embed
            (.case .newest hl.embed.underBinder hr.embed.underBinder))

end Isotope.LambdaCase.LocallyNameless
