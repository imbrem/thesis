import Isotope.LambdaIter.NoSubtyping.Typing

/-!
# Typed equational closures without subtyping

The axiom schemes are split into structural beta/eta laws, sequencing and
commuting conversions, and iteration/Elgot laws.  Endpoint typing remains in
the congruence closure, while the raw schemes contain their freshness and
purity side conditions.
-/

namespace Isotope.LambdaIter.NoSubtyping

namespace LocallyNameless

variable {τ : Type u} [TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε]

/-- Syntactic purity. Iteration is intentionally not pure, since even a loop
whose instructions are pure may diverge. -/
inductive Pure (pureEff : ε) : {n : Nat} → Tm ν Φ n → Prop where
  | fv : Pure pureEff (.fv x)
  | bv : Pure pureEff (.bv i)
  | op (hf : IsPure pureEff f) : Pure pureEff a → Pure pureEff (.op f a)
  | let₁ : Pure pureEff a → Pure pureEff b → Pure pureEff (.let₁ a b)
  | unit : Pure pureEff .unit
  | pair : Pure pureEff a → Pure pureEff b → Pure pureEff (.pair a b)
  | let₂ : Pure pureEff a → Pure pureEff b → Pure pureEff (.let₂ a b)
  | inl : Pure pureEff a → Pure pureEff (.inl a)
  | inr : Pure pureEff a → Pure pureEff (.inr a)
  | case : Pure pureEff e → Pure pureEff l → Pure pureEff r → Pure pureEff (.case e l r)
  | abort : Pure pureEff a → Pure pureEff (.abort a)

/-- Product, coproduct, unit, empty, and pure-let beta/eta laws. -/
inductive StructuralAxiom (pureEff : ε) :
    {n : Nat} → Tm ν Φ n → Tm ν Φ n → Prop where
  | letBeta (hp : Pure pureEff a) :
      StructuralAxiom pureEff (.let₁ a b)
        (Isotope.LambdaIter.LocallyNameless.Tm.instantiate b a)
  | letEta (a : Tm ν Φ n) : StructuralAxiom pureEff (.let₁ a (.bv 0)) a
  | unitEta (a : Tm ν Φ n) : StructuralAxiom pureEff (.let₁ a .unit) a
  | pairBeta (a b : Tm ν Φ n) (c : Tm ν Φ (n + 2)) :
      StructuralAxiom pureEff (.let₂ (.pair a b) c)
        (.let₁ a (.let₁ (Isotope.LambdaIter.LocallyNameless.Tm.lift b) c))
  | pairEta (a : Tm ν Φ n) :
      StructuralAxiom pureEff (.let₂ a (.pair (.bv 1) (.bv 0))) a
  | caseBetaL (e : Tm ν Φ n) (l r : Tm ν Φ (n + 1)) :
      StructuralAxiom pureEff (.case (.inl e) l r) (.let₁ e l)
  | caseBetaR (e : Tm ν Φ n) (l r : Tm ν Φ (n + 1)) :
      StructuralAxiom pureEff (.case (.inr e) l r) (.let₁ e r)
  | caseEta (e : Tm ν Φ n) :
      StructuralAxiom pureEff (.case e (.inl (.bv 0)) (.inr (.bv 0))) e
  | emptyInitial (a : Tm ν Φ n) (b c : Tm ν Φ (n + 1)) :
      StructuralAxiom pureEff (.let₁ (.abort a) b) (.let₁ (.abort a) c)

/-- Sequencing and commuting conversions. -/
inductive SequencingAxiom (pureEff : ε) :
    {n : Nat} → Tm ν Φ n → Tm ν Φ n → Prop where
  | bindOp (a : Tm ν Φ n) (c : Tm ν Φ (n + 1)) :
      SequencingAxiom pureEff (.let₁ (.op f a) c)
        (.let₁ a (.let₁ (.op f (.bv 0))
          (Isotope.LambdaIter.LocallyNameless.Tm.underBinder c)))
  | bindLet (a : Tm ν Φ n) (b c : Tm ν Φ (n + 1)) :
      SequencingAxiom pureEff (.let₁ (.let₁ a b) c)
        (.let₁ a (.let₁ b (Isotope.LambdaIter.LocallyNameless.Tm.underBinder c)))
  | bindLetPair (e : Tm ν Φ n) (c : Tm ν Φ (n + 2)) (d : Tm ν Φ (n + 1)) :
      SequencingAxiom pureEff (.let₁ (.let₂ e c) d)
        (.let₂ e (.let₁ c (Isotope.LambdaIter.LocallyNameless.Tm.underBinder
          (Isotope.LambdaIter.LocallyNameless.Tm.underBinder d))))
  | bindLetCase (e : Tm ν Φ n) (l r d : Tm ν Φ (n + 1)) :
      SequencingAxiom pureEff (.let₁ (.case e l r) d)
        (.case e
          (.let₁ l (Isotope.LambdaIter.LocallyNameless.Tm.underBinder d))
          (.let₁ r (Isotope.LambdaIter.LocallyNameless.Tm.underBinder d)))
  | bindPair (a : Tm ν Φ n) (c : Tm ν Φ (n + 2)) :
      SequencingAxiom pureEff (.let₂ a c)
        (.let₁ a (.let₂ (.bv 0)
          (Isotope.LambdaIter.LocallyNameless.Tm.underTwoBinders c)))
  | bindCase (e : Tm ν Φ n) (l r : Tm ν Φ (n + 1)) :
      SequencingAxiom pureEff (.case e l r)
        (.let₁ e (.case (.bv 0)
          (Isotope.LambdaIter.LocallyNameless.Tm.underBinder l)
          (Isotope.LambdaIter.LocallyNameless.Tm.underBinder r)))

/-- Fixpoint, naturality, codiagonal, and iteration-binding laws. Uniformity
is a constructor of `Eqv`, because its commuting square is itself an
equational derivation. -/
inductive IterationAxiom (pureEff : ε) :
    {n : Nat} → Tm ν Φ n → Tm ν Φ n → Prop where
  | fixpoint (a : Tm ν Φ n) (b : Tm ν Φ (n + 1)) :
      IterationAxiom pureEff (.iter a b)
        (.let₁ a (.case b (.bv 0)
          (.iter (.bv 0) (Isotope.LambdaIter.LocallyNameless.Tm.underBinder
            (Isotope.LambdaIter.LocallyNameless.Tm.underBinder b)))))
  | naturality (a : Tm ν Φ n) (b c : Tm ν Φ (n + 1)) :
      IterationAxiom pureEff (.let₁ (.iter a b) c)
        (.iter a (.case b
          (.inl (Isotope.LambdaIter.LocallyNameless.Tm.underBinder c))
          (.inr (.bv 0))))
  | codiagonal (a : Tm ν Φ n) (b : Tm ν Φ (n + 1)) :
      IterationAxiom pureEff
        (.iter a (.iter (.bv 0)
          (Isotope.LambdaIter.LocallyNameless.Tm.underBinder b)))
        (.iter a (.case b (.bv 0) (.inr (.bv 0))))
  | iterBind (a : Tm ν Φ n) (b : Tm ν Φ (n + 1)) :
      IterationAxiom pureEff (.iter a b)
        (.let₁ a (.iter (.bv 0)
          (Isotope.LambdaIter.LocallyNameless.Tm.underBinder b)))

inductive CoreAxiom (pureEff : ε) :
    {n : Nat} → Tm ν Φ n → Tm ν Φ n → Prop where
  | structural : StructuralAxiom pureEff a b → CoreAxiom pureEff a b
  | sequencing : SequencingAxiom pureEff a b → CoreAxiom pureEff a b
  | iteration : IterationAxiom pureEff a b → CoreAxiom pureEff a b

/-- Typed congruence closure of raw equations.  Notice the absence of both a
subtyping rule and proof-relevant endpoint typing evidence. -/
inductive Eqv (pureEff : ε) (Γ : LambdaIter.Ctx ν τ) :
    {n : Nat} → BoundCtx τ n → Tm ν Φ n → Tm ν Φ n → τ → Prop where
  | refl (h : HasType Φ Γ β a A) : Eqv pureEff Γ β a a A
  | symm : Eqv pureEff Γ β a b A → Eqv pureEff Γ β b a A
  | trans : Eqv pureEff Γ β a b A → Eqv pureEff Γ β b c A → Eqv pureEff Γ β a c A
  | op : Eqv pureEff Γ β a a' (instrSrc f) →
      Eqv pureEff Γ β (.op f a) (.op f a') (instrTrg f)
  | let₁ (ha : Eqv pureEff Γ β a a' A)
      (hb : Eqv pureEff Γ (.snoc β A) b b' B) :
      Eqv pureEff Γ β (.let₁ a b) (.let₁ a' b') B
  | unit : Eqv pureEff Γ β .unit .unit LambdaIter.unit
  | pair (ha : Eqv pureEff Γ β a a' A) (hb : Eqv pureEff Γ β b b' B) :
      Eqv pureEff Γ β (.pair a b) (.pair a' b') (LambdaIter.tensor A B)
  | let₂ (he : Eqv pureEff Γ β e e' (LambdaIter.tensor A B))
      (hc : Eqv pureEff Γ (.snoc (.snoc β A) B) c c' C) :
      Eqv pureEff Γ β (.let₂ e c) (.let₂ e' c') C
  | inl (h : Eqv pureEff Γ β a a' A) :
      Eqv pureEff Γ β (.inl a) (.inl a') (LambdaIter.coprod A B)
  | inr (h : Eqv pureEff Γ β b b' B) :
      Eqv pureEff Γ β (.inr b) (.inr b') (LambdaIter.coprod A B)
  | case (he : Eqv pureEff Γ β e e' (LambdaIter.coprod A B))
      (hl : Eqv pureEff Γ (.snoc β A) l l' C)
      (hr : Eqv pureEff Γ (.snoc β B) r r' C) :
      Eqv pureEff Γ β (.case e l r) (.case e' l' r') C
  | abort (h : Eqv pureEff Γ β a a' LambdaIter.empty) :
      Eqv pureEff Γ β (.abort a) (.abort a') C
  | iter (ha : Eqv pureEff Γ β a a' A)
      (hb : Eqv pureEff Γ (.snoc β A) b b' (LambdaIter.coprod B A)) :
      Eqv pureEff Γ β (.iter a b) (.iter a' b') B
  | ax (hax : CoreAxiom pureEff a b)
      (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b A) :
      Eqv pureEff Γ β a b A
  | uniformity {n : Nat} {β : BoundCtx τ n}
      {a : Tm ν Φ n} {h b b' : Tm ν Φ (n + 1)}
      (ha : HasType Φ Γ β a A)
      (hh : HasType Φ Γ (.snoc β A) h A') (hp : Pure pureEff h)
      (hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A))
      (hb' : HasType Φ Γ (.snoc β A') b' (LambdaIter.coprod B A'))
      (square : Eqv pureEff Γ (.snoc β A)
        (.case b (.inl (.bv (0 : Fin (n + 2))))
          (.inr (Isotope.LambdaIter.LocallyNameless.Tm.underBinder h)))
        (Isotope.LambdaIter.LocallyNameless.Tm.instantiate
          (Isotope.LambdaIter.LocallyNameless.Tm.underBinder b') h)
        (LambdaIter.coprod B A')) :
      Eqv pureEff Γ β (.iter a b) (.iter (.let₁ a h) b') B

/-- The proposition used to form the one-variable syntactic quotient. -/
abbrev Related (pureEff : ε) (Γ : LambdaIter.Ctx ν τ) (β : BoundCtx τ n)
    (A : τ) (a b : Tm ν Φ n) : Prop := Eqv pureEff Γ β a b A

end LocallyNameless

namespace Named

variable {τ : Type u} [TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε]

inductive Pure (pureEff : ε) : Tm ν Φ → Prop where
  | var : Pure pureEff (.var x)
  | op (hf : IsPure pureEff f) : Pure pureEff a → Pure pureEff (.op f a)
  | let₁ : Pure pureEff a → Pure pureEff b → Pure pureEff (.let₁ x a b)
  | unit : Pure pureEff .unit
  | pair : Pure pureEff a → Pure pureEff b → Pure pureEff (.pair a b)
  | let₂ : Pure pureEff a → Pure pureEff b → Pure pureEff (.let₂ x y a b)
  | inl : Pure pureEff a → Pure pureEff (.inl a)
  | inr : Pure pureEff a → Pure pureEff (.inr a)
  | case : Pure pureEff e → Pure pureEff a → Pure pureEff b →
      Pure pureEff (.case e x a y b)
  | abort : Pure pureEff a → Pure pureEff (.abort a)

/-- Named structural beta/eta schemes, including freshness and capture
conditions needed for safe named substitution. -/
inductive StructuralAxiom (pureEff : ε) : Tm ν Φ → Tm ν Φ → Prop where
  | letBeta (hp : Pure pureEff a)
      (hs : Isotope.LambdaIter.Named.CaptureSafe a b) :
      StructuralAxiom pureEff (.let₁ (some x) a b)
        (Isotope.LambdaIter.Named.Tm.substSafe x a b hs)
  | letEta : StructuralAxiom pureEff (.let₁ (some x) a (.var x)) a
  | unitEta : StructuralAxiom pureEff (.let₁ x a .unit) a
  | empty : StructuralAxiom pureEff (.let₁ x (.abort a) b) (.let₁ x (.abort a) b')
  | pairBeta (hfresh : ¬b.Free x) :
      StructuralAxiom pureEff (.let₂ (some x) (some y) (.pair a b) c)
        (.let₁ (some x) a (.let₁ (some y) b c))
  | pairEta (hne : x ≠ y) :
      StructuralAxiom pureEff
        (.let₂ (some x) (some y) a (.pair (.var x) (.var y))) a
  | caseBetaL : StructuralAxiom pureEff
      (.case (.inl e) (some x) a (some y) b) (.let₁ (some x) e a)
  | caseBetaR : StructuralAxiom pureEff
      (.case (.inr e) (some x) a (some y) b) (.let₁ (some y) e b)
  | caseEta : StructuralAxiom pureEff
      (.case e (some x) (.inl (.var x)) (some y) (.inr (.var y))) e

/-- Named sequencing, commuting, and pure-substitution schemes. -/
inductive SequencingAxiom (pureEff : ε) : Tm ν Φ → Tm ν Φ → Prop where
  | letOp (hfresh : ¬c.Free x) :
      SequencingAxiom pureEff (.let₁ (some y) (.op f a) c)
        (.let₁ (some x) a (.let₁ (some y) (.op f (.var x)) c))
  | letLet (hfresh : ∀ w, x = some w → ¬c.Free w) :
      SequencingAxiom pureEff (.let₁ y (.let₁ x a b) c)
        (.let₁ x a (.let₁ y b c))
  | letLet₂
      (hfreshX : ∀ w, x = some w → ¬d.Free w)
      (hfreshY : ∀ w, y = some w → ¬d.Free w) :
      SequencingAxiom pureEff (.let₁ z (.let₂ x y e c) d)
        (.let₂ x y e (.let₁ z c d))
  | letCase
      (hfreshX : ∀ w, x = some w → ¬d.Free w)
      (hfreshY : ∀ w, y = some w → ¬d.Free w) :
      SequencingAxiom pureEff (.let₁ z (.case e x a y b) d)
        (.case e x (.let₁ z a d) y (.let₁ z b d))
  | let₂Bind (hfresh : ¬c.Free z) :
      SequencingAxiom pureEff (.let₂ x y a c)
        (.let₁ (some z) a (.let₂ x y (.var z) c))
  | caseBind (hfreshL : ¬a.Free z)
      (hfreshR : ¬b.Free z) :
      SequencingAxiom pureEff (.case e x a y b)
        (.let₁ (some z) e (.case (.var z) x a y b))
  | pureLetVar (hp : Pure pureEff e) (hne : x ≠ y) :
      SequencingAxiom pureEff (.let₁ (some x) e (.var y)) (.var y)
  | pureLetOp (hp : Pure pureEff e) :
      SequencingAxiom pureEff (.let₁ (some x) e (.op f a))
        (.op f (.let₁ (some x) e a))
  | pureLetUnit (hp : Pure pureEff e) :
      SequencingAxiom pureEff (.let₁ (some x) e .unit) .unit
  | pureLetPair (hp : Pure pureEff e) :
      SequencingAxiom pureEff (.let₁ (some x) e (.pair a b))
        (.pair (.let₁ (some x) e a) (.let₁ (some x) e b))
  | pureLetInl (hp : Pure pureEff e) :
      SequencingAxiom pureEff (.let₁ (some x) e (.inl a))
        (.inl (.let₁ (some x) e a))
  | pureLetInr (hp : Pure pureEff e) :
      SequencingAxiom pureEff (.let₁ (some x) e (.inr b))
        (.inr (.let₁ (some x) e b))
  | pureLetLet (hp : Pure pureEff e)
      (hfresh : ∀ w, y = some w → ¬e.Free w) :
      SequencingAxiom pureEff (.let₁ (some x) e (.let₁ y a b))
        (.let₁ y (.let₁ (some x) e a) (.let₁ (some x) e b))
  | pureLetLet₂ (hp : Pure pureEff e)
      (hfreshY : ∀ w, y = some w → ¬e.Free w)
      (hfreshZ : ∀ w, z = some w → ¬e.Free w) :
      SequencingAxiom pureEff (.let₁ (some x) e (.let₂ y z a b))
        (.let₂ y z (.let₁ (some x) e a) (.let₁ (some x) e b))
  | pureLetCase (hp : Pure pureEff e)
      (hfreshY : ∀ w, y = some w → ¬e.Free w)
      (hfreshZ : ∀ w, z = some w → ¬e.Free w) :
      SequencingAxiom pureEff (.let₁ (some x) e (.case a y b z c))
        (.case (.let₁ (some x) e a) y (.let₁ (some x) e b)
          z (.let₁ (some x) e c))
  | pureLetAbort (hp : Pure pureEff e) :
      SequencingAxiom pureEff (.let₁ (some x) e (.abort a))
        (.abort (.let₁ (some x) e a))
  | pureLetIter (hp : Pure pureEff e)
      (hfresh : ∀ w, y = some w → ¬e.Free w) :
      SequencingAxiom pureEff (.let₁ (some x) e (.iter a y b))
        (.iter (.let₁ (some x) e a) y (.let₁ (some x) e b))

inductive IterationAxiom (pureEff : ε) : Tm ν Φ → Tm ν Φ → Prop where
  | fixpoint (hfresh : ¬b.Free z) :
      IterationAxiom pureEff (.iter a (some x) b)
        (.let₁ (some x) a
          (.case b (some y) (.var y) (some z) (.iter (.var z) (some x) b)))
  | naturality (hfresh : ¬c.Free x) :
      IterationAxiom pureEff (.let₁ (some y) (.iter a (some x) b) c)
        (.iter a (some x)
          (.case b (some y) (.inl c) (some z) (.inr (.var z))))
  | codiagonal (hfresh : ¬b.Free y) :
      IterationAxiom pureEff (.iter a (some x) (.iter (.var x) (some y) b))
        (.iter a (some x) (.case b (some y) (.var y) (some z) (.inr (.var z))))
  | iterBind (hfresh : ¬b.Free y) :
      IterationAxiom pureEff (.iter a (some x) b)
        (.let₁ (some y) a (.iter (.var y) (some x) b))

inductive CoreAxiom (pureEff : ε) : Tm ν Φ → Tm ν Φ → Prop where
  | structural : StructuralAxiom pureEff a b → CoreAxiom pureEff a b
  | sequencing : SequencingAxiom pureEff a b → CoreAxiom pureEff a b
  | iteration : IterationAxiom pureEff a b → CoreAxiom pureEff a b

/-- Typed congruence and alpha closure of a named raw theory. -/
inductive Eqv (pureEff : ε) : Ctx ν τ → Tm ν Φ → Tm ν Φ → τ → Prop where
  | refl (h : HasType Φ Γ a A) : Eqv pureEff Γ a a A
  | symm : Eqv pureEff Γ a b A → Eqv pureEff Γ b a A
  | trans : Eqv pureEff Γ a b A → Eqv pureEff Γ b c A → Eqv pureEff Γ a c A
  | op : Eqv pureEff Γ a a' (instrSrc f) →
      Eqv pureEff Γ (.op f a) (.op f a') (instrTrg f)
  | let₁ (ha : Eqv pureEff Γ a a' A)
      (hb : Eqv pureEff (.snoc Γ x A) b b' B) :
      Eqv pureEff Γ (.let₁ x a b) (.let₁ x a' b') B
  | unit : Eqv pureEff Γ .unit .unit LambdaIter.unit
  | pair (ha : Eqv pureEff Γ a a' A) (hb : Eqv pureEff Γ b b' B) :
      Eqv pureEff Γ (.pair a b) (.pair a' b') (LambdaIter.tensor A B)
  | let₂ (he : Eqv pureEff Γ e e' (LambdaIter.tensor A B))
      (hc : Eqv pureEff (.snoc (.snoc Γ x A) y B) c c' C) :
      Eqv pureEff Γ (.let₂ x y e c) (.let₂ x y e' c') C
  | inl (h : Eqv pureEff Γ a a' A) :
      Eqv pureEff Γ (.inl a) (.inl a') (LambdaIter.coprod A B)
  | inr (h : Eqv pureEff Γ b b' B) :
      Eqv pureEff Γ (.inr b) (.inr b') (LambdaIter.coprod A B)
  | case (he : Eqv pureEff Γ e e' (LambdaIter.coprod A B))
      (hl : Eqv pureEff (.snoc Γ x A) l l' C)
      (hr : Eqv pureEff (.snoc Γ y B) r r' C) :
      Eqv pureEff Γ (.case e x l y r) (.case e' x l' y r') C
  | abort (h : Eqv pureEff Γ a a' LambdaIter.empty) :
      Eqv pureEff Γ (.abort a) (.abort a') C
  | iter (ha : Eqv pureEff Γ a a' A)
      (hb : Eqv pureEff (.snoc Γ x A) b b' (LambdaIter.coprod B A)) :
      Eqv pureEff Γ (.iter a x b) (.iter a' x b') B
  | ax (hax : CoreAxiom pureEff a b)
      (ha : HasType Φ Γ a A) (hb : HasType Φ Γ b A) : Eqv pureEff Γ a b A
  | alpha (h : Isotope.LambdaIter.Named.Alpha a b)
      (ha : HasType Φ Γ a A) (hb : HasType Φ Γ b A) :
      Eqv pureEff Γ a b A
  | uniformity (hp : Pure pureEff h)
      (ha : HasType Φ Γ a A)
      (hh : HasType Φ (.snoc Γ (some x) A) h A')
      (hcapture : Isotope.LambdaIter.Named.CaptureSafe (.var z) h)
      (hcapture' : Isotope.LambdaIter.Named.CaptureSafe h b')
      (square : Eqv pureEff (.snoc Γ (some x) A)
        (.case b (some y) (.inl (.var y)) (some z)
          (.inr (Isotope.LambdaIter.Named.Tm.substSafe x (.var z) h hcapture)))
        (Isotope.LambdaIter.Named.Tm.substSafe x' h b' hcapture')
        (LambdaIter.coprod B A')) :
      Eqv pureEff Γ (.iter a (some x) b)
        (.iter (.let₁ (some x) a h) (some x') b') B

end Named
end Isotope.LambdaIter.NoSubtyping
