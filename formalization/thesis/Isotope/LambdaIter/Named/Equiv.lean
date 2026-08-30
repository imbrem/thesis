import Isotope.LambdaIter.Named.Alpha

/-! # Typed equational theory for named lambda-iter -/

namespace Isotope.LambdaIter.Named

open TypeFormers

variable [DecidableEq ν] [TypeFormers τ] [Subtyping τ] [HasTy Φ τ] [HasEff Φ ε]

/-- Syntactic purity, used exactly where the thesis requires a pure expression. -/
inductive Pure (pureEff : ε) : Tm ν Φ → Prop where
  | var : Pure pureEff (.var x)
  | op (hf : IsPure pureEff f) (ha : Pure pureEff a) : Pure pureEff (.op f a)
  | let₁ : Pure pureEff a → Pure pureEff b → Pure pureEff (.let₁ x a b)
  | unit : Pure pureEff .unit
  | pair : Pure pureEff a → Pure pureEff b → Pure pureEff (.pair a b)
  | let₂ : Pure pureEff a → Pure pureEff b → Pure pureEff (.let₂ x y a b)
  | inl : Pure pureEff a → Pure pureEff (.inl a)
  | inr : Pure pureEff a → Pure pureEff (.inr a)
  | case : Pure pureEff e → Pure pureEff a → Pure pureEff b → Pure pureEff (.case e x a y b)
  | abort : Pure pureEff a → Pure pureEff (.abort a)
  /- Iteration is deliberately absent. Even when its initializer and body use
  only pure instructions, Elgot iteration can diverge, so an abstract Elgot
  model cannot in general regard the resulting computation as a pure map. -/

/-- Raw axiom schemes. `Eqv.ax` below additionally requires both sides to have
the displayed type, making every scheme a typed equation. -/
inductive Axiom (pureEff : ε) : Tm ν Φ → Tm ν Φ → Prop where
  | letBeta (hp : Pure pureEff a) (hs : CaptureSafe a b) :
      Axiom pureEff (.let₁ (some x) a b) (Tm.substSafe x a b hs)
  | letEta : Axiom pureEff (.let₁ (some x) a (.var x)) a
  | unitEta : Axiom pureEff (.let₁ x a .unit) a
  | empty : Axiom pureEff (.let₁ x (.abort a) b) (.let₁ x (.abort a) b')
  | pairBeta (hfresh : ¬b.Free x) :
      Axiom pureEff (.let₂ (some x) (some y) (.pair a b) c)
        (.let₁ (some x) a (.let₁ (some y) b c))
  | pairEta (hne : x ≠ y) :
      Axiom pureEff (.let₂ (some x) (some y) a (.pair (.var x) (.var y))) a
  | caseBetaL :
      Axiom pureEff (.case (.inl e) (some x) a (some y) b) (.let₁ (some x) e a)
  | caseBetaR :
      Axiom pureEff (.case (.inr e) (some x) a (some y) b) (.let₁ (some y) e b)
  | caseEta :
      Axiom pureEff (.case e (some x) (.inl (.var x)) (some y) (.inr (.var y))) e
  | letOp (hfresh : ¬c.Free x) :
      Axiom pureEff (.let₁ (some y) (.op f a) c)
        (.let₁ (some x) a (.let₁ (some y) (.op f (.var x)) c))
  | letLet (hfresh : ∀ w, x = some w → ¬c.Free w) :
      Axiom pureEff (.let₁ y (.let₁ x a b) c) (.let₁ x a (.let₁ y b c))
  | letLet₂ (hfreshX : ∀ w, x = some w → ¬d.Free w)
      (hfreshY : ∀ w, y = some w → ¬d.Free w) :
      Axiom pureEff (.let₁ z (.let₂ x y e c) d) (.let₂ x y e (.let₁ z c d))
  | letCase (hfreshX : ∀ w, x = some w → ¬d.Free w)
      (hfreshY : ∀ w, y = some w → ¬d.Free w) :
      Axiom pureEff (.let₁ z (.case e x a y b) d)
        (.case e x (.let₁ z a d) y (.let₁ z b d))
  | let₂Bind (hfresh : ¬c.Free z) :
      Axiom pureEff (.let₂ x y a c) (.let₁ (some z) a (.let₂ x y (.var z) c))
  | caseBind (hfreshL : ¬a.Free z) (hfreshR : ¬b.Free z) :
      Axiom pureEff (.case e x a y b) (.let₁ (some z) e (.case (.var z) x a y b))
  | iterUnfold (hfresh : ¬b.Free z) :
      Axiom pureEff (.iter a (some x) b)
        (.let₁ (some x) a
          (.case b (some y) (.var y) (some z) (.iter (.var z) (some x) b)))
  | iterNaturality (hfresh : ¬c.Free x) :
      Axiom pureEff (.let₁ (some y) (.iter a (some x) b) c)
        (.iter a (some x)
          (.case b (some y) (.inl c) (some z) (.inr (.var z))))
  | iterCodiagonal (hfresh : ¬b.Free y) :
      Axiom pureEff (.iter a (some x) (.iter (.var x) (some y) b))
        (.iter a (some x) (.case b (some y) (.var y) (some z) (.inr (.var z))))
  | iterBind (hfresh : ¬b.Free y) :
      Axiom pureEff (.iter a (some x) b)
        (.let₁ (some y) a (.iter (.var y) (some x) b))
  /- Pure let-distribution. Together with `letEta`, these are the thesis's
  syntax-directed presentation of pure substitution. -/
  | pureLetVar (hp : Pure pureEff e) (hne : x ≠ y) :
      Axiom pureEff (.let₁ (some x) e (.var y)) (.var y)
  | pureLetOp (hp : Pure pureEff e) :
      Axiom pureEff (.let₁ (some x) e (.op f a))
        (.op f (.let₁ (some x) e a))
  | pureLetUnit (hp : Pure pureEff e) : Axiom pureEff (.let₁ (some x) e .unit) .unit
  | pureLetPair (hp : Pure pureEff e) :
      Axiom pureEff (.let₁ (some x) e (.pair a b))
        (.pair (.let₁ (some x) e a) (.let₁ (some x) e b))
  | pureLetInl (hp : Pure pureEff e) :
      Axiom pureEff (.let₁ (some x) e (.inl a)) (.inl (.let₁ (some x) e a))
  | pureLetInr (hp : Pure pureEff e) :
      Axiom pureEff (.let₁ (some x) e (.inr b)) (.inr (.let₁ (some x) e b))
  | pureLetLet (hp : Pure pureEff e)
      (hfresh : ∀ w, y = some w → ¬e.Free w) :
      Axiom pureEff (.let₁ (some x) e (.let₁ y a b))
        (.let₁ y (.let₁ (some x) e a) (.let₁ (some x) e b))
  | pureLetLet₂ (hp : Pure pureEff e)
      (hfreshY : ∀ w, y = some w → ¬e.Free w)
      (hfreshZ : ∀ w, z = some w → ¬e.Free w) :
      Axiom pureEff (.let₁ (some x) e (.let₂ y z a b))
        (.let₂ y z (.let₁ (some x) e a) (.let₁ (some x) e b))
  | pureLetCase (hp : Pure pureEff e)
      (hfreshY : ∀ w, y = some w → ¬e.Free w)
      (hfreshZ : ∀ w, z = some w → ¬e.Free w) :
      Axiom pureEff (.let₁ (some x) e (.case a y b z c))
        (.case (.let₁ (some x) e a) y (.let₁ (some x) e b)
          z (.let₁ (some x) e c))
  | pureLetAbort (hp : Pure pureEff e) :
      Axiom pureEff (.let₁ (some x) e (.abort a)) (.abort (.let₁ (some x) e a))
  | pureLetIter (hp : Pure pureEff e)
      (hfresh : ∀ w, y = some w → ¬e.Free w) :
      Axiom pureEff (.let₁ (some x) e (.iter a y b))
        (.iter (.let₁ (some x) e a) y (.let₁ (some x) e b))

inductive Eqv (pureEff : ε) : Ctx ν τ → Tm ν Φ → Tm ν Φ → τ → Prop where
  | refl (h : HasType Γ a A) : Eqv pureEff Γ a a A
  | symm (h : Eqv pureEff Γ a b A) : Eqv pureEff Γ b a A
  | trans (h₁ : Eqv pureEff Γ a b A) (h₂ : Eqv pureEff Γ b c A) : Eqv pureEff Γ a c A
  | op (hf : InstTy f A B) (h : Eqv pureEff Γ a b A) :
      Eqv pureEff Γ (.op f a) (.op f b) B
  | let₁ (ha : Eqv pureEff Γ a a' A)
      (hb : Eqv pureEff (.snoc Γ x A) b b' B) :
      Eqv pureEff Γ (.let₁ x a b) (.let₁ x a' b') B
  | pair (ha : Eqv pureEff Γ a a' A) (hb : Eqv pureEff Γ b b' B) :
      Eqv pureEff Γ (.pair a b) (.pair a' b') (tensor A B)
  | let₂ (he : Eqv pureEff Γ e e' (tensor A B))
      (hc : Eqv pureEff (.snoc (.snoc Γ x A) y B) c c' C) :
      Eqv pureEff Γ (.let₂ x y e c) (.let₂ x y e' c') C
  | inl (h : Eqv pureEff Γ a a' A) : Eqv pureEff Γ (.inl a) (.inl a') (coprod A B)
  | inr (h : Eqv pureEff Γ b b' B) : Eqv pureEff Γ (.inr b) (.inr b') (coprod A B)
  | case (he : Eqv pureEff Γ e e' (coprod A B))
      (ha : Eqv pureEff (.snoc Γ x A) a a' C)
      (hb : Eqv pureEff (.snoc Γ y B) b b' C) :
      Eqv pureEff Γ (.case e x a y b) (.case e' x a' y b') C
  | abort (h : Eqv pureEff Γ a a' TypeFormers.empty) :
      Eqv pureEff Γ (.abort a) (.abort a') C
  | iter (ha : Eqv pureEff Γ a a' A)
      (hb : Eqv pureEff (.snoc Γ x A) b b' (coprod B A)) :
      Eqv pureEff Γ (.iter a x b) (.iter a' x b') B
  | ax (hax : Axiom pureEff a b) (ha : HasType Γ a A) (hb : HasType Γ b A) :
      Eqv pureEff Γ a b A
  | alpha (hab : Alpha a b) (ha : HasType Γ a A) (hb : HasType Γ b A) :
      Eqv pureEff Γ a b A
  /-- Uniformity includes the thesis's purity side condition on the comparison.
  In the continuation branch the comparison is applied to the value named `z`;
  using `h` unchanged here would incorrectly denote `h x`. -/
  | uniformity (hp : Pure pureEff h)
      (ha : HasType Γ a A)
      (hh : HasType (.snoc Γ (some x) A) h A')
      (hcapture : CaptureSafe (.var z) h)
      (hcapture' : CaptureSafe h b')
      (hsquare : Eqv pureEff (.snoc Γ (some x) A)
        (.case b (some y) (.inl (.var y)) (some z)
          (.inr (Tm.substSafe x (.var z) h hcapture)))
        (Tm.substSafe x' h b' hcapture') (coprod B A')) :
      Eqv pureEff Γ (.iter a (some x) b)
        (.iter (.let₁ (some x) a h) (some x') b') B
  | sub (h : Eqv pureEff Γ a b A) (hAB : Subty A B) : Eqv pureEff Γ a b B

end Isotope.LambdaIter.Named
