import Isotope.LambdaSeq.Syntax
import Isotope.LambdaCase.Typing

/-! # Extrinsic typing for lambda-seq -/

namespace Isotope.LambdaSeq

abbrev Ctx := LambdaIter.Ctx

namespace Named

variable [DecidableEq ν] [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
  [LambdaIter.HasTy Φ τ]

inductive HasType : Ctx ν τ → Tm ν Φ → τ → Prop where
  | var (h : LambdaIter.Ctx.lookup Γ x = some A) : HasType Γ (.var x) A
  | op (hf : LambdaIter.Named.InstTy f A B) (ha : HasType Γ a A) : HasType Γ (.op f a) B
  | let₁ (ha : HasType Γ a A) (hb : HasType (.snoc Γ x A) b B) :
      HasType Γ (.let₁ x a b) B
  | sub (ha : HasType Γ a A) (d : LambdaIter.Subty A B) : HasType Γ a B

def HasType.embedCase {Γ : Ctx ν τ} {t : Tm ν Φ} {A : τ} :
    HasType Γ t A → LambdaCase.Named.HasType Γ (Tm.embedCase t) A
  | .var h => .var h
  | .op hf ha => .op hf ha.embedCase
  | .let₁ ha hb => .let₁ ha.embedCase hb.embedCase
  | .sub ha d => .sub ha.embedCase d

def HasType.embedIter {Γ : Ctx ν τ} {t : Tm ν Φ} {A : τ} :
    HasType Γ t A → LambdaIter.Named.HasType Γ (Tm.embedIter t) A :=
  fun h => h.embedCase.embed

end Named

namespace LocallyNameless

abbrev BoundCtx := LambdaIter.LocallyNameless.BoundCtx

variable {τ : Type u} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [LambdaIter.HasTy Φ τ]

inductive HasType (Φ : Type q) [LambdaIter.HasTy Φ τ] (Γ : Ctx ν τ) :
    {n : Nat} → BoundCtx τ n → Tm ν Φ n → τ → Type (max u q w) where
  | fv (h : Γ.lookup x = some A) : HasType Φ Γ β (.fv x) A
  | bv : HasType Φ Γ β (.bv i) (β.get i)
  | op (ha : HasType Φ Γ β a (LambdaIter.instrSrc f)) :
      HasType Φ Γ β (.op f a) (LambdaIter.instrTrg f)
  | let₁ (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ (.snoc β A) b B) :
      HasType Φ Γ β (.let₁ a b) B
  | sub (ha : HasType Φ Γ β a A) (d : LambdaIter.Subty A B) : HasType Φ Γ β a B

def HasType.embedCase {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} : HasType Φ Γ β t A →
    LambdaCase.LocallyNameless.HasType Φ Γ β (Tm.embedCase t) A
  | .fv h => .fv h
  | .bv => .bv
  | .op ha => .op ha.embedCase
  | .let₁ ha hb => .let₁ ha.embedCase hb.embedCase
  | .sub ha d => .sub ha.embedCase d

def HasType.embedIter {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} : HasType Φ Γ β t A →
    LambdaIter.LocallyNameless.HasType Φ Γ β (Tm.embedIter t) A :=
  fun h => h.embedCase.embed

inductive Pure [LambdaIter.HasEff Φ ε] (pureEff : ε) : {n : Nat} → Tm ν Φ n → Prop where
  | fv : Pure pureEff (.fv x)
  | bv : Pure pureEff (.bv i)
  | op (hf : LambdaIter.IsPure pureEff f) : Pure pureEff a → Pure pureEff (.op f a)
  | let₁ : Pure pureEff a → Pure pureEff b → Pure pureEff (.let₁ a b)

def Pure.embedCase {ε : Type r} [LambdaIter.HasEff Φ ε] {pureEff : ε} :
    {n : Nat} → {t : Tm ν Φ n} → Pure pureEff t →
      LambdaCase.LocallyNameless.Pure pureEff (Tm.embedCase t)
  | _, _, .fv => .fv
  | _, _, .bv => .bv
  | _, _, .op hf ha => .op hf ha.embedCase
  | _, _, .let₁ ha hb => .let₁ ha.embedCase hb.embedCase

end LocallyNameless
end Isotope.LambdaSeq
