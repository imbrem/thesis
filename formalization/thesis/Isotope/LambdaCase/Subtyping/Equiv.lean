import Isotope.LambdaCase.Subtyping.Typing
import Isotope.LambdaIter.Subtyping.LocallyNameless.Equiv
import Isotope.LambdaIter.Subtyping.Named.Equiv

/-! # Equational theory of lambda-case -/

namespace Isotope.LambdaCase.Subtyping

namespace Named

open Isotope.LambdaCase.Named

/-- The named presentation is the iteration-free fragment of the named
lambda-iter theory.  Endpoints are necessarily images of lambda-case terms. -/
def Eqv [DecidableEq ν] [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
    [LambdaIter.HasTy Φ τ] [LambdaIter.HasEff Φ ε] (pureEff : ε)
    (Γ : Ctx ν τ) (a b : Tm ν Φ) (A : τ) : Prop :=
  LambdaIter.Subtyping.Named.Eqv pureEff Γ (embed a) (embed b) A

theorem Eqv.embed [DecidableEq ν] [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
    [LambdaIter.HasTy Φ τ] [LambdaIter.HasEff Φ ε]
    {pureEff : ε} {Γ : Ctx ν τ} {a b : Tm ν Φ} {A : τ} :
    Eqv pureEff Γ a b A → LambdaIter.Subtyping.Named.Eqv pureEff Γ (embed a) (embed b) A := id

end Named

namespace LocallyNameless

open Isotope.LambdaCase.LocallyNameless

variable {τ : Type u} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [LambdaIter.HasTy Φ τ]
variable {ε : Type r} [LambdaIter.HasEff Φ ε]

/-- The beta-eta and commuting-conversion theory, with no iteration axioms. -/
inductive Equiv (pureEff : ε) (Γ : Ctx ν τ) :
    {n : Nat} → BoundCtx τ n → Tm ν Φ n → Tm ν Φ n → τ → Prop where
  | var (h : Γ.lookup x = some A) : Equiv pureEff Γ β (.fv x) (.fv x) A
  | bvar : Equiv pureEff Γ β (.bv i) (.bv i) (β.get i)
  | symm : Equiv pureEff Γ β a b A → Equiv pureEff Γ β b a A
  | trans : Equiv pureEff Γ β a b A → Equiv pureEff Γ β b c A → Equiv pureEff Γ β a c A
  | sub : Equiv pureEff Γ β a b A → LambdaIter.Subty A B → Equiv pureEff Γ β a b B
  | op (h : Equiv pureEff Γ β a a' (LambdaIter.instrSrc f)) :
      Equiv pureEff Γ β (.op f a) (.op f a') (LambdaIter.instrTrg f)
  | let₁ (ha : Equiv pureEff Γ β a a' A)
      (hb : Equiv pureEff Γ (.snoc β A) b b' B) :
      Equiv pureEff Γ β (.let₁ a b) (.let₁ a' b') B
  | unit : Equiv pureEff Γ β .unit .unit LambdaIter.TypeFormers.unit
  | pair (ha : Equiv pureEff Γ β a a' A) (hb : Equiv pureEff Γ β b b' B) :
      Equiv pureEff Γ β (.pair a b) (.pair a' b') (LambdaIter.TypeFormers.tensor A B)
  | let₂ (ha : Equiv pureEff Γ β a a' (LambdaIter.TypeFormers.tensor A B))
      (hc : Equiv pureEff Γ (.snoc (.snoc β A) B) c c' C) :
      Equiv pureEff Γ β (.let₂ a c) (.let₂ a' c') C
  | inl (ha : Equiv pureEff Γ β a a' A) :
      Equiv pureEff Γ β (.inl a) (.inl a') (LambdaIter.TypeFormers.coprod A B)
  | inr (hb : Equiv pureEff Γ β b b' B) :
      Equiv pureEff Γ β (.inr b) (.inr b') (LambdaIter.TypeFormers.coprod A B)
  | case (he : Equiv pureEff Γ β e e' (LambdaIter.TypeFormers.coprod A B))
      (hl : Equiv pureEff Γ (.snoc β A) l l' C)
      (hr : Equiv pureEff Γ (.snoc β B) r r' C) :
      Equiv pureEff Γ β (.case e l r) (.case e' l' r') C
  | abort (ha : Equiv pureEff Γ β a a' LambdaIter.TypeFormers.empty) :
      Equiv pureEff Γ β (.abort a) (.abort a') C
  | letBeta (hp : Pure pureEff a) (ha : HasType Φ Γ β a A)
      (hb : HasType Φ Γ (.snoc β A) b B) :
      Equiv pureEff Γ β (.let₁ a b) (Tm.instantiate b a) B
  | letEta {n} {β : BoundCtx τ n} {a : Tm ν Φ n} (ha : HasType Φ Γ β a A) :
      Equiv pureEff Γ β (.let₁ a (.bv 0)) a A
  | unitEta (ha : HasType Φ Γ β a LambdaIter.TypeFormers.unit) :
      Equiv pureEff Γ β (.let₁ a .unit) a LambdaIter.TypeFormers.unit
  | pairBeta (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B)
      (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C) :
      Equiv pureEff Γ β (.let₂ (.pair a b) c) (.let₁ a (.let₁ (Tm.lift b) c)) C
  | pairEta {n} {β : BoundCtx τ n} {a : Tm ν Φ n}
      (ha : HasType Φ Γ β a (LambdaIter.TypeFormers.tensor A B)) :
      Equiv pureEff Γ β (.let₂ a (.pair (.bv 1) (.bv 0))) a
        (LambdaIter.TypeFormers.tensor A B)
  | caseBetaL (he : HasType Φ Γ β e A) (hl : HasType Φ Γ (.snoc β A) l C)
      (hr : HasType Φ Γ (.snoc β B) r C) :
      Equiv pureEff Γ β (.case (.inl e) l r) (.let₁ e l) C
  | caseBetaR (he : HasType Φ Γ β e B) (hl : HasType Φ Γ (.snoc β A) l C)
      (hr : HasType Φ Γ (.snoc β B) r C) :
      Equiv pureEff Γ β (.case (.inr e) l r) (.let₁ e r) C
  | caseEta {n} {β : BoundCtx τ n} {e : Tm ν Φ n}
      (he : HasType Φ Γ β e (LambdaIter.TypeFormers.coprod A B)) :
      Equiv pureEff Γ β (.case e (.inl (.bv 0)) (.inr (.bv 0))) e
        (LambdaIter.TypeFormers.coprod A B)
  | bindOp {n} {β : BoundCtx τ n} {a : Tm ν Φ n} {c : Tm ν Φ (n + 1)}
      (ha : HasType Φ Γ β a (LambdaIter.instrSrc f))
      (hc : HasType Φ Γ (.snoc β (LambdaIter.instrTrg f)) c C) :
      Equiv pureEff Γ β (.let₁ (.op f a) c)
        (.let₁ a (.let₁ (.op f (.bv 0)) (Tm.underBinder c))) C
  | bindLet (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ (.snoc β A) b B)
      (hc : HasType Φ Γ (.snoc β B) c C) :
      Equiv pureEff Γ β (.let₁ (.let₁ a b) c)
        (.let₁ a (.let₁ b (Tm.underBinder c))) C
  | bindLetPair (he : HasType Φ Γ β e (LambdaIter.TypeFormers.tensor A B))
      (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C)
      (hd : HasType Φ Γ (.snoc β C) d D) :
      Equiv pureEff Γ β (.let₁ (.let₂ e c) d)
        (.let₂ e (.let₁ c (Tm.underBinder (Tm.underBinder d)))) D
  | bindLetCase (he : HasType Φ Γ β e (LambdaIter.TypeFormers.coprod A B))
      (hl : HasType Φ Γ (.snoc β A) l C) (hr : HasType Φ Γ (.snoc β B) r C)
      (hd : HasType Φ Γ (.snoc β C) d D) :
      Equiv pureEff Γ β (.let₁ (.case e l r) d)
        (.case e (.let₁ l (Tm.underBinder d)) (.let₁ r (Tm.underBinder d))) D
  | bindPair {n} {β : BoundCtx τ n} {a : Tm ν Φ n} {c : Tm ν Φ (n + 2)}
      (ha : HasType Φ Γ β a (LambdaIter.TypeFormers.tensor A B))
      (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C) :
      Equiv pureEff Γ β (.let₂ a c)
        (.let₁ a (.let₂ (.bv 0) (Tm.underTwoBinders c))) C
  | bindCase {n} {β : BoundCtx τ n} {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)}
      (he : HasType Φ Γ β e (LambdaIter.TypeFormers.coprod A B))
      (hl : HasType Φ Γ (.snoc β A) l C) (hr : HasType Φ Γ (.snoc β B) r C) :
      Equiv pureEff Γ β (.case e l r)
        (.let₁ e (.case (.bv 0) (Tm.underBinder l) (Tm.underBinder r))) C
  | emptyInitial (ha : HasType Φ Γ β a LambdaIter.TypeFormers.empty)
      (hb : HasType Φ Γ (.snoc β A) b B) (hc : HasType Φ Γ (.snoc β A) c B) :
      Equiv pureEff Γ β (.let₁ (.abort a) b) (.let₁ (.abort a) c) B

/-- Every lambda-case equation is a lambda-iter equation. -/
def Equiv.embed {pureEff : ε} {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a b : Tm ν Φ n} {A : τ} : Equiv pureEff Γ β a b A →
    LambdaIter.Subtyping.LocallyNameless.Equiv pureEff Γ β a.embed b.embed A
  | .var h => .var h
  | .bvar => .bvar
  | .symm h => .symm h.embed
  | .trans h k => .trans h.embed k.embed
  | .sub h d => .sub h.embed d
  | .op h => .op h.embed
  | .let₁ ha hb => .let₁ ha.embed hb.embed
  | .unit => .unit
  | .pair ha hb => .pair ha.embed hb.embed
  | .let₂ ha hc => .let₂ ha.embed hc.embed
  | .inl h => .inl h.embed
  | .inr h => .inr h.embed
  | .case he hl hr => .case he.embed hl.embed hr.embed
  | .abort h => .abort h.embed
  | .letBeta hp ha hb => by simpa using LambdaIter.Subtyping.LocallyNameless.Equiv.letBeta hp.embed ha.embed hb.embed
  | .letEta ha => by simpa using LambdaIter.Subtyping.LocallyNameless.Equiv.letEta (pureEff := pureEff) ha.embed
  | .unitEta ha => LambdaIter.Subtyping.LocallyNameless.Equiv.unitEta (pureEff := pureEff) ha.embed
  | .pairBeta ha hb hc => by simpa only [Tm.embed, Tm.embed_lift] using LambdaIter.Subtyping.LocallyNameless.Equiv.pairBeta (pureEff := pureEff) ha.embed hb.embed hc.embed
  | .pairEta ha => LambdaIter.Subtyping.LocallyNameless.Equiv.pairEta (pureEff := pureEff) ha.embed
  | .caseBetaL he hl hr => LambdaIter.Subtyping.LocallyNameless.Equiv.caseBetaL (pureEff := pureEff) he.embed hl.embed hr.embed
  | .caseBetaR he hl hr => LambdaIter.Subtyping.LocallyNameless.Equiv.caseBetaR (pureEff := pureEff) he.embed hl.embed hr.embed
  | .caseEta he => LambdaIter.Subtyping.LocallyNameless.Equiv.caseEta (pureEff := pureEff) he.embed
  | .bindOp ha hc => by simpa only [Tm.embed, Tm.embed_underBinder] using LambdaIter.Subtyping.LocallyNameless.Equiv.bindOp (pureEff := pureEff) ha.embed hc.embed
  | .bindLet ha hb hc => by simpa only [Tm.embed, Tm.embed_underBinder] using LambdaIter.Subtyping.LocallyNameless.Equiv.bindLet (pureEff := pureEff) ha.embed hb.embed hc.embed
  | .bindLetPair he hc hd => by simpa only [Tm.embed, Tm.embed_underBinder] using LambdaIter.Subtyping.LocallyNameless.Equiv.bindLetPair (pureEff := pureEff) he.embed hc.embed hd.embed
  | .bindLetCase he hl hr hd => by simpa only [Tm.embed, Tm.embed_underBinder] using LambdaIter.Subtyping.LocallyNameless.Equiv.bindLetCase (pureEff := pureEff) he.embed hl.embed hr.embed hd.embed
  | .bindPair ha hc => by simpa only [Tm.embed, Tm.embed_underTwoBinders] using LambdaIter.Subtyping.LocallyNameless.Equiv.bindPair (pureEff := pureEff) ha.embed hc.embed
  | .bindCase he hl hr => by simpa only [Tm.embed, Tm.embed_underBinder] using LambdaIter.Subtyping.LocallyNameless.Equiv.bindCase (pureEff := pureEff) he.embed hl.embed hr.embed
  | .emptyInitial ha hb hc => LambdaIter.Subtyping.LocallyNameless.Equiv.emptyInitial (pureEff := pureEff) ha.embed hb.embed hc.embed

end LocallyNameless
end Isotope.LambdaCase.Subtyping
