import Isotope.LambdaIter.LocallyNameless.Equiv
import Isotope.LambdaIter.LocallyNameless.TypingSubst

/-!
# Proof-relevant typed equality derivations

Unlike `Equiv`, this judgment is indexed by the exact typing derivations at
its endpoints.  In particular, transitivity shares one literal middle typing
derivation.  This is necessary because subtype derivations have
proof-relevant denotations.
-/

namespace Isotope.LambdaIter.LocallyNameless.TypedEquiv

variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε]
variable {pureEff : ε} {Γ : LambdaIter.Ctx ν τ}

open LocallyNameless

set_option relaxedAutoImplicit true

/-- A typed equational derivation whose endpoint typing evidence is retained.
The non-structural equation schemes are added below as constructors rather
than injected from `Equiv`, so semantic soundness can inspect every rule. -/
inductive Deriv (pureEff : ε) (Γ : LambdaIter.Ctx ν τ) :
    {n : Nat} → {β : BoundCtx τ n} → {a b : Tm ν Φ n} → {A : τ} →
      HasType Φ Γ β a A → HasType Φ Γ β b A → Type (max u q w r) where
  | refl (h : HasType Φ Γ β a A) : Deriv pureEff Γ h h
  | symm (h : Deriv pureEff Γ ha hb) : Deriv pureEff Γ hb ha
  | trans (h : Deriv pureEff Γ ha hm) (k : Deriv pureEff Γ hm hc) :
      Deriv pureEff Γ ha hc
  | sub {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A B : τ}
      {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
      (h : Deriv pureEff Γ ha hb) (d : Subty A B) :
      Deriv pureEff Γ (.sub ha d) (.sub hb d)
  | op (h : Deriv pureEff Γ ha hb) :
      Deriv pureEff Γ (.op ha) (.op hb)
  | let₁ (da : Deriv pureEff Γ ha ha')
      (db : Deriv pureEff Γ hb hb') :
      Deriv pureEff Γ (.let₁ ha hb) (.let₁ ha' hb')
  | pair (da : Deriv pureEff Γ ha ha')
      (db : Deriv pureEff Γ hb hb') :
      Deriv pureEff Γ (.pair ha hb) (.pair ha' hb')
  | let₂ (da : Deriv pureEff Γ ha ha')
      (dc : Deriv pureEff Γ hc hc') :
      Deriv pureEff Γ (.let₂ ha hc) (.let₂ ha' hc')
  | inl (h : Deriv pureEff Γ ha hb) :
      Deriv pureEff Γ (HasType.inl (B := B) ha) (HasType.inl (B := B) hb)
  | inr (h : Deriv pureEff Γ ha hb) :
      Deriv pureEff Γ (HasType.inr (A := A) ha) (HasType.inr (A := A) hb)
  | case (de : Deriv pureEff Γ he he')
      (dl : Deriv pureEff Γ hl hl') (dr : Deriv pureEff Γ hr hr') :
      Deriv pureEff Γ (.case he hl hr) (.case he' hl' hr')
  | abort (h : Deriv pureEff Γ ha hb) :
      Deriv pureEff Γ (HasType.abort (C := C) ha) (HasType.abort (C := C) hb)
  | iter (da : Deriv pureEff Γ ha ha')
      (db : Deriv pureEff Γ hb hb') :
      Deriv pureEff Γ (.iter ha hb) (.iter ha' hb')
  | letBeta (hp : Pure pureEff a) (ha : HasType Φ Γ β a A)
      (hb : HasType Φ Γ (.snoc β A) b B) :
      Deriv pureEff Γ (.let₁ ha hb) (hb.instantiate ha)
  | letEta (ha : HasType Φ Γ β a A) :
      Deriv pureEff Γ
        (.let₁ ha HasType.newest) ha
  | unitEta (ha : HasType Φ Γ β a TypeFormers.unit) :
      Deriv pureEff Γ (.let₁ ha .unit) ha
  | pairBeta (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B)
      (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C) :
      Deriv pureEff Γ (.let₂ (.pair ha hb) hc)
        (.let₁ ha (.let₁ (hb.lift (B := A)) hc))
  | pairEta (ha : HasType Φ Γ β a (TypeFormers.tensor A B)) :
      Deriv pureEff Γ
        (.let₂ ha
          (.pair HasType.previous HasType.newest)) ha
  | caseBetaL (he : HasType Φ Γ β e A)
      (hl : HasType Φ Γ (.snoc β A) l C)
      (hr : HasType Φ Γ (.snoc β B) r C) :
      Deriv pureEff Γ (.case (.inl he) hl hr) (.let₁ he hl)
  | caseBetaR (he : HasType Φ Γ β e B)
      (hl : HasType Φ Γ (.snoc β A) l C)
      (hr : HasType Φ Γ (.snoc β B) r C) :
      Deriv pureEff Γ (.case (.inr he) hl hr) (.let₁ he hr)
  | caseEta (he : HasType Φ Γ β e (TypeFormers.coprod A B)) :
      Deriv pureEff Γ
        (.case he
          (.inl HasType.newest) (.inr HasType.newest)) he
  | bindOp (ha : HasType Φ Γ β a (instrSrc f))
      (hc : HasType Φ Γ (.snoc β (instrTrg f)) c C) :
      Deriv pureEff Γ (.let₁ (.op ha) hc)
        (.let₁ ha (.let₁ (.op HasType.newest) hc.underBinder))
  | bindLet (ha : HasType Φ Γ β a A)
      (hb : HasType Φ Γ (.snoc β A) b B)
      (hc : HasType Φ Γ (.snoc β B) c C) :
      Deriv pureEff Γ (.let₁ (.let₁ ha hb) hc)
        (.let₁ ha (.let₁ hb hc.underBinder))
  | bindLetPair (he : HasType Φ Γ β e (TypeFormers.tensor A B))
      (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C)
      (hd : HasType Φ Γ (.snoc β C) d D) :
      Deriv pureEff Γ (.let₁ (.let₂ he hc) hd)
        (.let₂ he (.let₁ hc (hd.underBinder.underBinder)))
  | bindLetCase (he : HasType Φ Γ β e (TypeFormers.coprod A B))
      (hl : HasType Φ Γ (.snoc β A) l C)
      (hr : HasType Φ Γ (.snoc β B) r C)
      (hd : HasType Φ Γ (.snoc β C) d D) :
      Deriv pureEff Γ (.let₁ (.case he hl hr) hd)
        (.case he (.let₁ hl hd.underBinder) (.let₁ hr hd.underBinder))
  | bindPair (ha : HasType Φ Γ β a (TypeFormers.tensor A B))
      (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C) :
      Deriv pureEff Γ (.let₂ ha hc)
        (.let₁ ha (.let₂ HasType.newest hc.underTwoBinders))
  | bindCase (he : HasType Φ Γ β e (TypeFormers.coprod A B))
      (hl : HasType Φ Γ (.snoc β A) l C)
      (hr : HasType Φ Γ (.snoc β B) r C) :
      Deriv pureEff Γ (.case he hl hr)
        (.let₁ he
          (.case HasType.newest hl.underBinder hr.underBinder))

set_option relaxedAutoImplicit false

/-- The legacy raw relation has syntax-directed reflexivity constructors;
package their recursion over an exact typing derivation. -/
def equivRefl : {n : Nat} → {β : BoundCtx τ n} → {a : Tm ν Φ n} → {A : τ} →
    HasType Φ Γ β a A → Equiv pureEff Γ β a a A
  | _, _, _, _, .fv h => .var h
  | _, _, _, _, .bv => .bvar
  | _, _, _, _, .op h => .op (equivRefl h)
  | _, _, _, _, .let₁ ha hb => .let₁ (equivRefl ha) (equivRefl hb)
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .pair ha hb => .pair (equivRefl ha) (equivRefl hb)
  | _, _, _, _, .let₂ ha hb => .let₂ (equivRefl ha) (equivRefl hb)
  | _, _, _, _, .inl h => .inl (equivRefl h)
  | _, _, _, _, .inr h => .inr (equivRefl h)
  | _, _, _, _, .case he hl hr => .case (equivRefl he) (equivRefl hl) (equivRefl hr)
  | _, _, _, _, .abort h => .abort (equivRefl h)
  | _, _, _, _, .iter ha hb => .iter (equivRefl ha) (equivRefl hb)
  | _, _, _, _, .sub h d => .sub (equivRefl h) d

/-- Forget exact endpoint typing derivations. -/
def Deriv.erase {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A} :
    Deriv pureEff Γ ha hb →
    Equiv pureEff Γ β a b A
  | .refl h => equivRefl h
  | .symm h => .symm h.erase
  | .trans h k => .trans h.erase k.erase
  | .sub h d => .sub h.erase d
  | .op h => .op h.erase
  | .let₁ ha hb => .let₁ ha.erase hb.erase
  | .pair ha hb => .pair ha.erase hb.erase
  | .let₂ ha hb => .let₂ ha.erase hb.erase
  | .inl h => .inl h.erase
  | .inr h => .inr h.erase
  | .case he hl hr => .case he.erase hl.erase hr.erase
  | .abort h => .abort h.erase
  | .iter ha hb => .iter ha.erase hb.erase
  | .letBeta hp ha hb => .letBeta hp ha hb
  | .letEta ha => .letEta ha
  | .unitEta ha => .unitEta ha
  | .pairBeta ha hb hc => .pairBeta ha hb hc
  | .pairEta ha => .pairEta ha
  | .caseBetaL he hl hr => .caseBetaL he hl hr
  | .caseBetaR he hl hr => .caseBetaR he hl hr
  | .caseEta he => .caseEta he
  | .bindOp ha hc => .bindOp ha hc
  | .bindLet ha hb hc => .bindLet ha hb hc
  | .bindLetPair he hc hd => .bindLetPair he hc hd
  | .bindLetCase he hl hr hd => .bindLetCase he hl hr hd
  | .bindPair ha hc => .bindPair ha hc
  | .bindCase he hl hr => .bindCase he hl hr

/-- Proposition truncation at fixed proof-relevant endpoints. -/
abbrev Related (pureEff : ε) (Γ : LambdaIter.Ctx ν τ)
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b A) : Prop :=
  Nonempty (Deriv pureEff Γ ha hb)

/-- Proposition-level equality of raw terms: endpoint derivations merely have
to exist, while the derivation connecting the chosen endpoints is truncated. -/
def EqvProp (pureEff : ε) (Γ : LambdaIter.Ctx ν τ) (β : BoundCtx τ n)
    (a b : Tm ν Φ n) (A : τ) : Prop :=
  Nonempty (Σ ha : HasType Φ Γ β a A,
    Σ hb : HasType Φ Γ β b A, Deriv pureEff Γ ha hb)

theorem EqvProp.toEquiv : EqvProp (Φ := Φ) pureEff Γ β a b A →
    Equiv (Φ := Φ) pureEff Γ β a b A :=
  fun h => h.elim fun ⟨_, _, d⟩ => d.erase

end Isotope.LambdaIter.LocallyNameless.TypedEquiv
