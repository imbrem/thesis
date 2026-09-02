import Isotope.LambdaIter.Named.Subtyping

/-! # Typing for named lambda-iter -/

namespace Isotope.LambdaIter.Subtyping.Named

open Isotope.LambdaIter.Named

open TypeFormers

variable [DecidableEq ν] [TypeFormers τ] [Subtyping τ] [HasTy Φ τ]

/-- Proof-relevant named typing derivations.  Keeping these derivations in
`Type` is essential for denotational semantics: the `sub` and `op` rules
carry coercions whose interpretations are computational data. -/
inductive HasType : Ctx ν τ → Tm ν Φ → τ → Type _ where
  | var (h : Ctx.lookup Γ x = some A) : HasType Γ (.var x) A
  | op (hf : InstTy f A B) (ha : HasType Γ a A) : HasType Γ (.op f a) B
  | let₁ (ha : HasType Γ a A) (hb : HasType (.snoc Γ x A) b B) :
      HasType Γ (.let₁ x a b) B
  | unit : HasType Γ .unit TypeFormers.unit
  | pair (ha : HasType Γ a A) (hb : HasType Γ b B) :
      HasType Γ (.pair a b) (TypeFormers.tensor A B)
  | let₂ (ha : HasType Γ a (TypeFormers.tensor A B))
      (hc : HasType (.snoc (.snoc Γ x A) y B) c C) :
      HasType Γ (.let₂ x y a c) C
  | inl (ha : HasType Γ a A) : HasType Γ (.inl a) (TypeFormers.coprod A B)
  | inr (hb : HasType Γ b B) : HasType Γ (.inr b) (TypeFormers.coprod A B)
  | case (he : HasType Γ e (TypeFormers.coprod A B))
      (ha : HasType (.snoc Γ x A) a C)
      (hb : HasType (.snoc Γ y B) b C) :
      HasType Γ (.case e x a y b) C
  | abort (ha : HasType Γ a TypeFormers.empty) : HasType Γ (.abort a) C
  | iter (ha : HasType Γ a A)
      (hb : HasType (.snoc Γ x A) b (TypeFormers.coprod B A)) :
      HasType Γ (.iter a x b) B
  /-- The explicit coercion boundary leaves every term-former rule
  syntax-directed while exposing the result-subtyping used by weakening. -/
  | sub (ha : HasType Γ a A) (hAB : Subty A B) : HasType Γ a B

end Isotope.LambdaIter.Subtyping.Named
