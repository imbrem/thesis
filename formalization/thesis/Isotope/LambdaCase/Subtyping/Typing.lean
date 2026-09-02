import Isotope.LambdaCase.Syntax
import Isotope.LambdaIter.Subtyping.LocallyNameless.Typing
import Isotope.LambdaIter.Subtyping.Named.Typing

/-! # Extrinsic typing for lambda-case -/

namespace Isotope.LambdaCase.Subtyping

abbrev Ctx := LambdaIter.Ctx

namespace Named

open Isotope.LambdaCase.Named

variable [DecidableEq ν] [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
  [LambdaIter.HasTy Φ τ]

/-- Proof-relevant extrinsic typing for named lambda-case. -/
inductive HasType : Ctx ν τ → Tm ν Φ → τ → Type _ where
  | var (h : LambdaIter.Ctx.lookup Γ x = some A) : HasType Γ (.var x) A
  | op (hf : LambdaIter.Named.InstTy f A B) (ha : HasType Γ a A) : HasType Γ (.op f a) B
  | let₁ (ha : HasType Γ a A) (hb : HasType (.snoc Γ x A) b B) :
      HasType Γ (.let₁ x a b) B
  | unit : HasType Γ .unit LambdaIter.TypeFormers.unit
  | pair (ha : HasType Γ a A) (hb : HasType Γ b B) :
      HasType Γ (.pair a b) (LambdaIter.TypeFormers.tensor A B)
  | let₂ (ha : HasType Γ a (LambdaIter.TypeFormers.tensor A B))
      (hc : HasType (.snoc (.snoc Γ x A) y B) c C) : HasType Γ (.let₂ x y a c) C
  | inl (ha : HasType Γ a A) :
      HasType Γ (.inl a) (LambdaIter.TypeFormers.coprod A B)
  | inr (hb : HasType Γ b B) :
      HasType Γ (.inr b) (LambdaIter.TypeFormers.coprod A B)
  | case (he : HasType Γ e (LambdaIter.TypeFormers.coprod A B))
      (hl : HasType (.snoc Γ x A) l C) (hr : HasType (.snoc Γ y B) r C) :
      HasType Γ (.case e x l y r) C
  | abort (ha : HasType Γ a LambdaIter.TypeFormers.empty) : HasType Γ (.abort a) C
  | sub (ha : HasType Γ a A) (d : LambdaIter.Subty A B) : HasType Γ a B

/-- Named typing is preserved by the inclusion. -/
def HasType.embed {Γ : Ctx ν τ} {t : Tm ν Φ} {A : τ} :
    HasType Γ t A → LambdaIter.Subtyping.Named.HasType Γ (embed t) A
  | .var h => .var h
  | .op hf ha => .op hf ha.embed
  | .let₁ ha hb => .let₁ ha.embed hb.embed
  | .unit => .unit
  | .pair ha hb => .pair ha.embed hb.embed
  | .let₂ ha hc => .let₂ ha.embed hc.embed
  | .inl ha => .inl ha.embed
  | .inr hb => .inr hb.embed
  | .case he hl hr => .case he.embed hl.embed hr.embed
  | .abort ha => .abort ha.embed
  | .sub ha d => .sub ha.embed d

end Named

namespace LocallyNameless

open Isotope.LambdaCase.LocallyNameless

abbrev BoundCtx := LambdaIter.LocallyNameless.BoundCtx

variable {τ : Type u} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [LambdaIter.HasTy Φ τ]

/-- Extrinsic, proof-relevant typing for locally nameless lambda-case. -/
inductive HasType (Φ : Type q) [LambdaIter.HasTy Φ τ] (Γ : Ctx ν τ) :
    {n : Nat} → BoundCtx τ n → Tm ν Φ n → τ → Type (max u q w) where
  | fv (h : Γ.lookup x = some A) : HasType Φ Γ β (.fv x) A
  | bv : HasType Φ Γ β (.bv i) (β.get i)
  | op (ha : HasType Φ Γ β a (LambdaIter.instrSrc f)) :
      HasType Φ Γ β (.op f a) (LambdaIter.instrTrg f)
  | let₁ (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ (.snoc β A) b B) :
      HasType Φ Γ β (.let₁ a b) B
  | unit : HasType Φ Γ β .unit LambdaIter.TypeFormers.unit
  | pair (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B) :
      HasType Φ Γ β (.pair a b) (LambdaIter.TypeFormers.tensor A B)
  | let₂ (ha : HasType Φ Γ β a (LambdaIter.TypeFormers.tensor A B))
      (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C) : HasType Φ Γ β (.let₂ a c) C
  | inl (ha : HasType Φ Γ β a A) :
      HasType Φ Γ β (.inl a) (LambdaIter.TypeFormers.coprod A B)
  | inr (hb : HasType Φ Γ β b B) :
      HasType Φ Γ β (.inr b) (LambdaIter.TypeFormers.coprod A B)
  | case (he : HasType Φ Γ β e (LambdaIter.TypeFormers.coprod A B))
      (hl : HasType Φ Γ (.snoc β A) l C) (hr : HasType Φ Γ (.snoc β B) r C) :
      HasType Φ Γ β (.case e l r) C
  | abort (ha : HasType Φ Γ β a LambdaIter.TypeFormers.empty) : HasType Φ Γ β (.abort a) C
  | sub (ha : HasType Φ Γ β a A) (d : LambdaIter.Subty A B) : HasType Φ Γ β a B

/-- Locally nameless typing is preserved by the inclusion. -/
def HasType.embed {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} : HasType Φ Γ β t A →
    LambdaIter.Subtyping.LocallyNameless.HasType Φ Γ β (Tm.embed t) A
  | .fv h => .fv h
  | .bv => .bv
  | .op ha => .op ha.embed
  | .let₁ ha hb => .let₁ ha.embed hb.embed
  | .unit => .unit
  | .pair ha hb => .pair ha.embed hb.embed
  | .let₂ ha hc => .let₂ ha.embed hc.embed
  | .inl ha => .inl ha.embed
  | .inr hb => .inr hb.embed
  | .case he hl hr => .case he.embed hl.embed hr.embed
  | .abort ha => .abort ha.embed
  | .sub ha d => .sub ha.embed d

inductive Pure [LambdaIter.HasEff Φ ε] (pureEff : ε) : {n : Nat} → Tm ν Φ n → Prop where
  | fv : Pure pureEff (.fv x)
  | bv : Pure pureEff (.bv i)
  | op (hf : LambdaIter.IsPure pureEff f) : Pure pureEff a → Pure pureEff (.op f a)
  | let₁ : Pure pureEff a → Pure pureEff b → Pure pureEff (.let₁ a b)
  | unit : Pure pureEff .unit
  | pair : Pure pureEff a → Pure pureEff b → Pure pureEff (.pair a b)
  | let₂ : Pure pureEff a → Pure pureEff b → Pure pureEff (.let₂ a b)
  | inl : Pure pureEff a → Pure pureEff (.inl a)
  | inr : Pure pureEff a → Pure pureEff (.inr a)
  | case : Pure pureEff e → Pure pureEff l → Pure pureEff r → Pure pureEff (.case e l r)
  | abort : Pure pureEff a → Pure pureEff (.abort a)

def Pure.embed {ε : Type r} [LambdaIter.HasEff Φ ε] {pureEff : ε} :
    {n : Nat} → {t : Tm ν Φ n} →
      Pure pureEff t → LambdaIter.Subtyping.LocallyNameless.Pure pureEff (Tm.embed t)
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

end LocallyNameless
end Isotope.LambdaCase.Subtyping
