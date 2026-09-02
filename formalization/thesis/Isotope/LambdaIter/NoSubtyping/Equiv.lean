import Isotope.LambdaIter.NoSubtyping.Typing

/-!
# Typed equational closures without subtyping

The raw axiom relation is a parameter.  This separates the experiment's main
question—whether typing, weakening, alpha conversion, and quotient formation
need subtyping—from choices about which presentation of the lambda-iter laws
is most convenient.  Concrete lambda-iter axiom schemes can be plugged into
`RawTheory` without changing either typing judgment.
-/

namespace Isotope.LambdaIter.NoSubtyping

namespace LocallyNameless

variable {τ : Type u} [TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]

/-- A first syntax-only kernel of equations.  Endpoint typing in `Eqv.ax`
rules out ill-typed instances.  The remaining beta, commuting, and Elgot
schemes will extend this datatype rather than the congruence closure. -/
inductive CoreAxiom : {n : Nat} → Tm ν Φ n → Tm ν Φ n → Prop where
  | letEta (a : Tm ν Φ n) : CoreAxiom (.let₁ a (.bv 0)) a
  | unitEta (a : Tm ν Φ n) : CoreAxiom (.let₁ a .unit) a
  | pairEta (a : Tm ν Φ n) : CoreAxiom (.let₂ a (.pair (.bv 1) (.bv 0))) a
  | caseEta (a : Tm ν Φ n) :
      CoreAxiom (.case a (.inl (.bv 0)) (.inr (.bv 0))) a
  | iterBind (a : Tm ν Φ n) (b : Tm ν Φ (n + 1)) :
      CoreAxiom (.iter a b) (.let₁ a (.iter (.bv 0)
        (Isotope.LambdaIter.LocallyNameless.Tm.underBinder b)))

/-- Typed congruence closure of raw equations.  Notice the absence of both a
subtyping rule and proof-relevant endpoint typing evidence. -/
inductive Eqv (Γ : LambdaIter.Ctx ν τ) :
    {n : Nat} → BoundCtx τ n → Tm ν Φ n → Tm ν Φ n → τ → Prop where
  | refl (h : HasType Φ Γ β a A) : Eqv Γ β a a A
  | symm : Eqv Γ β a b A → Eqv Γ β b a A
  | trans : Eqv Γ β a b A → Eqv Γ β b c A → Eqv Γ β a c A
  | op : Eqv Γ β a a' (instrSrc f) → Eqv Γ β (.op f a) (.op f a') (instrTrg f)
  | let₁ (ha : Eqv Γ β a a' A) (hb : Eqv Γ (.snoc β A) b b' B) :
      Eqv Γ β (.let₁ a b) (.let₁ a' b') B
  | unit : Eqv Γ β .unit .unit LambdaIter.unit
  | pair (ha : Eqv Γ β a a' A) (hb : Eqv Γ β b b' B) :
      Eqv Γ β (.pair a b) (.pair a' b') (LambdaIter.tensor A B)
  | let₂ (he : Eqv Γ β e e' (LambdaIter.tensor A B))
      (hc : Eqv Γ (.snoc (.snoc β A) B) c c' C) :
      Eqv Γ β (.let₂ e c) (.let₂ e' c') C
  | inl (h : Eqv Γ β a a' A) : Eqv Γ β (.inl a) (.inl a') (LambdaIter.coprod A B)
  | inr (h : Eqv Γ β b b' B) : Eqv Γ β (.inr b) (.inr b') (LambdaIter.coprod A B)
  | case (he : Eqv Γ β e e' (LambdaIter.coprod A B))
      (hl : Eqv Γ (.snoc β A) l l' C) (hr : Eqv Γ (.snoc β B) r r' C) :
      Eqv Γ β (.case e l r) (.case e' l' r') C
  | abort (h : Eqv Γ β a a' LambdaIter.empty) : Eqv Γ β (.abort a) (.abort a') C
  | iter (ha : Eqv Γ β a a' A)
      (hb : Eqv Γ (.snoc β A) b b' (LambdaIter.coprod B A)) :
      Eqv Γ β (.iter a b) (.iter a' b') B
  | ax (hax : CoreAxiom a b) (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b A) :
      Eqv Γ β a b A

/-- The proposition used to form the one-variable syntactic quotient. -/
abbrev Related (Γ : LambdaIter.Ctx ν τ) (β : BoundCtx τ n)
    (A : τ) (a b : Tm ν Φ n) : Prop := Eqv Γ β a b A

end LocallyNameless

namespace Named

variable {τ : Type u} [TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]

inductive CoreAxiom : Tm ν Φ → Tm ν Φ → Prop where
  | letEta : CoreAxiom (.let₁ (some x) a (.var x)) a
  | unitEta : CoreAxiom (.let₁ x a .unit) a
  | pairEta (hxy : x ≠ y) : CoreAxiom (.let₂ (some x) (some y) a (.pair (.var x) (.var y))) a
  | caseEta : CoreAxiom (.case a (some x) (.inl (.var x)) (some y) (.inr (.var y))) a
  | iterBind : CoreAxiom (.iter a (some x) b)
      (.let₁ (some y) a (.iter (.var y) (some x) b))

/-- Typed congruence and alpha closure of a named raw theory. -/
inductive Eqv : Ctx ν τ → Tm ν Φ → Tm ν Φ → τ → Prop where
  | refl (h : HasType Φ Γ a A) : Eqv Γ a a A
  | symm : Eqv Γ a b A → Eqv Γ b a A
  | trans : Eqv Γ a b A → Eqv Γ b c A → Eqv Γ a c A
  | op : Eqv Γ a a' (instrSrc f) → Eqv Γ (.op f a) (.op f a') (instrTrg f)
  | let₁ (ha : Eqv Γ a a' A) (hb : Eqv (.snoc Γ x A) b b' B) :
      Eqv Γ (.let₁ x a b) (.let₁ x a' b') B
  | unit : Eqv Γ .unit .unit LambdaIter.unit
  | pair (ha : Eqv Γ a a' A) (hb : Eqv Γ b b' B) :
      Eqv Γ (.pair a b) (.pair a' b') (LambdaIter.tensor A B)
  | let₂ (he : Eqv Γ e e' (LambdaIter.tensor A B))
      (hc : Eqv (.snoc (.snoc Γ x A) y B) c c' C) :
      Eqv Γ (.let₂ x y e c) (.let₂ x y e' c') C
  | inl (h : Eqv Γ a a' A) : Eqv Γ (.inl a) (.inl a') (LambdaIter.coprod A B)
  | inr (h : Eqv Γ b b' B) : Eqv Γ (.inr b) (.inr b') (LambdaIter.coprod A B)
  | case (he : Eqv Γ e e' (LambdaIter.coprod A B))
      (hl : Eqv (.snoc Γ x A) l l' C) (hr : Eqv (.snoc Γ y B) r r' C) :
      Eqv Γ (.case e x l y r) (.case e' x l' y r') C
  | abort (h : Eqv Γ a a' LambdaIter.empty) : Eqv Γ (.abort a) (.abort a') C
  | iter (ha : Eqv Γ a a' A) (hb : Eqv (.snoc Γ x A) b b' (LambdaIter.coprod B A)) :
      Eqv Γ (.iter a x b) (.iter a' x b') B
  | ax (hax : CoreAxiom a b) (ha : HasType Φ Γ a A) (hb : HasType Φ Γ b A) : Eqv Γ a b A
  | alpha (h : Isotope.LambdaIter.Named.Alpha a b)
      (ha : HasType Φ Γ a A) (hb : HasType Φ Γ b A) :
      Eqv Γ a b A

end Named
end Isotope.LambdaIter.NoSubtyping
