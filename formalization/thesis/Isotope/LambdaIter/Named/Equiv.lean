import Isotope.LambdaIter.Named.Subst

/-! # Typed equational theory for named lambda-iter -/

namespace Isotope.LambdaIter.Named

open TypeFormers

variable [DecidableEq ι] [TypeFormers τ] [Subtyping τ] {S : Signature τ}

/-- Syntactic purity, used exactly where the thesis requires a pure expression. -/
inductive Pure : Tm ι S → Prop where
  | var : Pure (.var x)
  | op (hf : S.pure f) (ha : Pure a) : Pure (.op f a)
  | let₁ : Pure a → Pure b → Pure (.let₁ x a b)
  | unit : Pure .unit
  | pair : Pure a → Pure b → Pure (.pair a b)
  | let₂ : Pure a → Pure b → Pure (.let₂ x y a b)
  | inl : Pure a → Pure (.inl a)
  | inr : Pure a → Pure (.inr a)
  | case : Pure e → Pure a → Pure b → Pure (.case e x a y b)
  | abort : Pure a → Pure (.abort a)
  | iter : Pure a → Pure b → Pure (.iter a x b)

/-- Raw axiom schemes. `Eqv.ax` below additionally requires both sides to have
the displayed type, making every scheme a typed equation. -/
inductive Axiom : Tm ι S → Tm ι S → Prop where
  | letBeta (hp : Pure a) (hs : CaptureSafe a b) :
      Axiom (.let₁ (some x) a b) (Tm.substSafe x a b hs)
  | letEta : Axiom (.let₁ (some x) a (.var x)) a
  | unitEta : Axiom (.let₁ x a .unit) a
  | empty : Axiom (.let₁ x (.abort a) b) (.let₁ x (.abort a) b')
  | pairBeta :
      Axiom (.let₂ (some x) (some y) (.pair a b) c)
        (.let₁ (some x) a (.let₁ (some y) b c))
  | pairEta : Axiom (.let₂ (some x) (some y) a (.pair (.var x) (.var y))) a
  | caseBetaL :
      Axiom (.case (.inl e) (some x) a (some y) b) (.let₁ (some x) e a)
  | caseBetaR :
      Axiom (.case (.inr e) (some x) a (some y) b) (.let₁ (some y) e b)
  | caseEta :
      Axiom (.case e (some x) (.inl (.var x)) (some y) (.inr (.var y))) e
  | letOp :
      Axiom (.let₁ (some y) (.op f a) c)
        (.let₁ (some x) a (.let₁ (some y) (.op f (.var x)) c))
  | letLet :
      Axiom (.let₁ y (.let₁ x a b) c) (.let₁ x a (.let₁ y b c))
  | letLet₂ :
      Axiom (.let₁ z (.let₂ x y e c) d) (.let₂ x y e (.let₁ z c d))
  | letCase :
      Axiom (.let₁ z (.case e x a y b) d)
        (.case e x (.let₁ z a d) y (.let₁ z b d))
  | let₂Bind :
      Axiom (.let₂ x y a c) (.let₁ (some z) a (.let₂ x y (.var z) c))
  | caseBind :
      Axiom (.case e x a y b) (.let₁ (some z) e (.case (.var z) x a y b))
  | iterUnfold :
      Axiom (.iter a (some x) b)
        (.let₁ (some x) a
          (.case b (some y) (.var y) (some z) (.iter (.var z) (some x) b)))
  | iterNaturality :
      Axiom (.let₁ (some y) (.iter a (some x) b) c)
        (.iter a (some x)
          (.case b (some y) (.inl c) (some z) (.inr (.var z))))
  | iterCodiagonal :
      Axiom (.iter a (some x) (.iter (.var x) (some y) b))
        (.iter a (some y) (.case b (some x) (.var x) (some z) (.inr (.var z))))
  | iterBind :
      Axiom (.iter a (some x) b)
        (.let₁ (some y) a (.iter (.var y) (some x) b))
  /- Pure let-distribution. Together with `letEta`, these are the thesis's
  syntax-directed presentation of pure substitution. -/
  | pureLetVar (hp : Pure e) (hne : x ≠ y) :
      Axiom (.let₁ (some x) e (.var y)) (.var y)
  | pureLetOp (hp : Pure e) :
      Axiom (.let₁ (some x) e (.op f a))
        (.op f (.let₁ (some x) e a))
  | pureLetUnit (hp : Pure e) : Axiom (.let₁ (some x) e .unit) .unit
  | pureLetPair (hp : Pure e) :
      Axiom (.let₁ (some x) e (.pair a b))
        (.pair (.let₁ (some x) e a) (.let₁ (some x) e b))
  | pureLetInl (hp : Pure e) :
      Axiom (.let₁ (some x) e (.inl a)) (.inl (.let₁ (some x) e a))
  | pureLetInr (hp : Pure e) :
      Axiom (.let₁ (some x) e (.inr b)) (.inr (.let₁ (some x) e b))
  | pureLetLet (hp : Pure e) :
      Axiom (.let₁ (some x) e (.let₁ y a b))
        (.let₁ y (.let₁ (some x) e a) (.let₁ (some x) e b))
  | pureLetLet₂ (hp : Pure e) :
      Axiom (.let₁ (some x) e (.let₂ y z a b))
        (.let₂ y z (.let₁ (some x) e a) (.let₁ (some x) e b))
  | pureLetCase (hp : Pure e) :
      Axiom (.let₁ (some x) e (.case a y b z c))
        (.case (.let₁ (some x) e a) y (.let₁ (some x) e b)
          z (.let₁ (some x) e c))
  | pureLetAbort (hp : Pure e) :
      Axiom (.let₁ (some x) e (.abort a)) (.abort (.let₁ (some x) e a))
  | pureLetIter (hp : Pure e) :
      Axiom (.let₁ (some x) e (.iter a y b))
        (.iter (.let₁ (some x) e a) y (.let₁ (some x) e b))

inductive Eqv (S : Signature τ) : Ctx ι τ → Tm ι S → Tm ι S → τ → Prop where
  | refl (h : HasType S Γ a A) : Eqv S Γ a a A
  | symm (h : Eqv S Γ a b A) : Eqv S Γ b a A
  | trans (h₁ : Eqv S Γ a b A) (h₂ : Eqv S Γ b c A) : Eqv S Γ a c A
  | op (hf : InstTy S f A B) (h : Eqv S Γ a b A) :
      Eqv S Γ (.op f a) (.op f b) B
  | let₁ (ha : Eqv S Γ a a' A)
      (hb : Eqv S ((x, A) :: Γ) b b' B) :
      Eqv S Γ (.let₁ x a b) (.let₁ x a' b') B
  | pair (ha : Eqv S Γ a a' A) (hb : Eqv S Γ b b' B) :
      Eqv S Γ (.pair a b) (.pair a' b') (tensor A B)
  | let₂ (he : Eqv S Γ e e' (tensor A B))
      (hc : Eqv S ((y, B) :: (x, A) :: Γ) c c' C) :
      Eqv S Γ (.let₂ x y e c) (.let₂ x y e' c') C
  | inl (h : Eqv S Γ a a' A) : Eqv S Γ (.inl a) (.inl a') (coprod A B)
  | inr (h : Eqv S Γ b b' B) : Eqv S Γ (.inr b) (.inr b') (coprod A B)
  | case (he : Eqv S Γ e e' (coprod A B))
      (ha : Eqv S ((x, A) :: Γ) a a' C)
      (hb : Eqv S ((y, B) :: Γ) b b' C) :
      Eqv S Γ (.case e x a y b) (.case e' x a' y b') C
  | abort (h : Eqv S Γ a a' TypeFormers.empty) :
      Eqv S Γ (.abort a) (.abort a') C
  | iter (ha : Eqv S Γ a a' A)
      (hb : Eqv S ((x, A) :: Γ) b b' (coprod B A)) :
      Eqv S Γ (.iter a x b) (.iter a' x b') B
  | ax (hax : Axiom a b) (ha : HasType S Γ a A) (hb : HasType S Γ b A) :
      Eqv S Γ a b A
  /-- Uniformity includes the thesis's purity side condition on the comparison. -/
  | uniformity (hp : Pure h)
      (ha : HasType S Γ a A)
      (hh : HasType S ((some x, A) :: Γ) h A')
      (hsquare : Eqv S ((some x, A) :: Γ)
        (.case b (some y) (.inl (.var y)) (some z) (.inr h))
        (Tm.subst x' h b') (coprod B A')) :
      Eqv S Γ (.iter a (some x) b)
        (.iter (.let₁ (some x) a h) (some x') b') B
  | sub (h : Eqv S Γ a b A) (hAB : Subty A B) : Eqv S Γ a b B

end Isotope.LambdaIter.Named
