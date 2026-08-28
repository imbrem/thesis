/-
Copyright (c) 2026 Remu G. -/
import Isotope.LambdaIter.Named.Context

/-! # Typing for named lambda-iter -/

namespace Isotope.LambdaIter.Named

open TypeFormers

variable [DecidableEq ι] [TypeFormers τ] (S : Signature τ)

inductive HasType : Ctx ι τ → Tm ι S → τ → Prop where
  | var (h : Ctx.lookup Γ x = some A) : HasType Γ (.var x) A
  | op (ha : HasType Γ a (S.src f)) : HasType Γ (.op f a) (S.trg f)
  | let₁ (ha : HasType Γ a A) (hb : HasType ((x, A) :: Γ) b B) :
      HasType Γ (.let₁ x a b) B
  | unit : HasType Γ .unit TypeFormers.unit
  | pair (ha : HasType Γ a A) (hb : HasType Γ b B) :
      HasType Γ (.pair a b) (tensor A B)
  | let₂ (ha : HasType Γ a (tensor A B))
      (hc : HasType ((y, B) :: (x, A) :: Γ) c C) :
      HasType Γ (.let₂ x y a c) C
  | inl (ha : HasType Γ a A) : HasType Γ (.inl a) (coprod A B)
  | inr (hb : HasType Γ b B) : HasType Γ (.inr b) (coprod A B)
  | case (he : HasType Γ e (coprod A B))
      (ha : HasType ((x, A) :: Γ) a C)
      (hb : HasType ((y, B) :: Γ) b C) :
      HasType Γ (.case e x a y b) C
  | abort (ha : HasType Γ a TypeFormers.empty) : HasType Γ (.abort a) C
  | iter (ha : HasType Γ a A)
      (hb : HasType ((x, A) :: Γ) b (coprod B A)) :
      HasType Γ (.iter a x b) B

end Isotope.LambdaIter.Named
