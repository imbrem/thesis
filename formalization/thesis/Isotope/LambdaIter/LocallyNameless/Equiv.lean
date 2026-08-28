import Isotope.LambdaIter.LocallyNameless.Typing

namespace Isotope.LambdaIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable {ν : Type w} [DecidableEq ν]
variable {S : Signature.{u, q} τ} {Γ : LambdaIter.Ctx ν τ}

/-- The typed equational theory.  Unlike refinement, this judgment is
symmetric.  Its pure-substitution axiom records purity explicitly. -/
inductive Equiv (S : Signature.{u, q} τ) (Γ : LambdaIter.Ctx ν τ) :
    {n : Nat} → BoundCtx τ n → Tm ν S.Instr n → Tm ν S.Instr n → τ → Prop where
  | var (h : Γ.lookup x = some A) : Equiv S Γ β (.fv x) (.fv x) A
  | bvar : Equiv S Γ β (.bv ι) (.bv ι) (β.get ι)
  | symm : Equiv S Γ β a b A → Equiv S Γ β b a A
  | trans : Equiv S Γ β a b A → Equiv S Γ β b c A → Equiv S Γ β a c A
  | sub : Equiv S Γ β a b A → Subty A B → Equiv S Γ β a b B
  | op (hf : InstTy S f A B) (h : Equiv S Γ β a a' A) :
      Equiv S Γ β (.op f a) (.op f a') B
  | let₁ (ha : Equiv S Γ β a a' A)
      (hb : Equiv S Γ (.snoc β A) b b' B) :
      Equiv S Γ β (.let₁ a b) (.let₁ a' b') B
  | unit : Equiv S Γ β .unit .unit TypeFormers.unit
  | pair (ha : Equiv S Γ β a a' A) (hb : Equiv S Γ β b b' B) :
      Equiv S Γ β (.pair a b) (.pair a' b') (TypeFormers.tensor A B)
  | let₂ (ha : Equiv S Γ β a a' (TypeFormers.tensor A B))
      (hc : Equiv S Γ (.snoc (.snoc β A) B) c c' C) :
      Equiv S Γ β (.let₂ a c) (.let₂ a' c') C
  | inl (ha : Equiv S Γ β a a' A) :
      Equiv S Γ β (.inl a) (.inl a') (TypeFormers.coprod A B)
  | inr (hb : Equiv S Γ β b b' B) :
      Equiv S Γ β (.inr b) (.inr b') (TypeFormers.coprod A B)
  | case (he : Equiv S Γ β e e' (TypeFormers.coprod A B))
      (hl : Equiv S Γ (.snoc β A) l l' C)
      (hr : Equiv S Γ (.snoc β B) r r' C) :
      Equiv S Γ β (.case e l r) (.case e' l' r') C
  | abort (ha : Equiv S Γ β a a' TypeFormers.empty) :
      Equiv S Γ β (.abort a) (.abort a') C
  | iter (ha : Equiv S Γ β a a' A)
      (hb : Equiv S Γ (.snoc β A) b b' (TypeFormers.coprod B A)) :
      Equiv S Γ β (.iter a b) (.iter a' b') B

  /-- Pure let beta.  The purity side-condition is essential. -/
  | letBeta (hp : Pure S a) (ha : HasType S Γ β a A)
      (hb : HasType S Γ (.snoc β A) b B) :
      Equiv S Γ β (.let₁ a b) (Tm.instantiate b a) B
  | letEta {n : Nat} {β : BoundCtx τ n} {a : Tm ν S.Instr n}
      (ha : HasType S Γ β a A) :
      Equiv S Γ β (.let₁ a (.bv (0 : Fin (n + 1)))) a A
  | unitEta (ha : HasType S Γ β a TypeFormers.unit) :
      Equiv S Γ β (.let₁ a .unit) a TypeFormers.unit
  | pairBeta (ha : HasType S Γ β a A) (hb : HasType S Γ β b B)
      (hc : HasType S Γ (.snoc (.snoc β A) B) c C) :
      Equiv S Γ β (.let₂ (.pair a b) c) (.let₁ a (.let₁ (Tm.lift b) c)) C
  | pairEta {n : Nat} {β : BoundCtx τ n} {a : Tm ν S.Instr n}
      (ha : HasType S Γ β a (TypeFormers.tensor A B)) :
      Equiv S Γ β (.let₂ a (.pair (.bv 1) (.bv 0))) a (TypeFormers.tensor A B)
  | caseBetaL (he : HasType S Γ β e A)
      (hl : HasType S Γ (.snoc β A) l C)
      (hr : HasType S Γ (.snoc β B) r C) :
      Equiv S Γ β (.case (.inl e) l r) (.let₁ e l) C
  | caseBetaR (he : HasType S Γ β e B)
      (hl : HasType S Γ (.snoc β A) l C)
      (hr : HasType S Γ (.snoc β B) r C) :
      Equiv S Γ β (.case (.inr e) l r) (.let₁ e r) C
  | caseEta {n : Nat} {β : BoundCtx τ n} {e : Tm ν S.Instr n}
      (he : HasType S Γ β e (TypeFormers.coprod A B)) :
      Equiv S Γ β (.case e (.inl (.bv 0)) (.inr (.bv 0))) e
        (TypeFormers.coprod A B)

  | bindOp {n : Nat} {β : BoundCtx τ n} {a : Tm ν S.Instr n}
      {c : Tm ν S.Instr (n + 1)} (hf : InstTy S f A B) (ha : HasType S Γ β a A)
      (hc : HasType S Γ (.snoc β B) c C) :
      Equiv S Γ β (.let₁ (.op f a) c)
        (.let₁ a (.let₁ (.op f (.bv 0)) (Tm.underBinder c))) C
  | bindLet (ha : HasType S Γ β a A)
      (hb : HasType S Γ (.snoc β A) b B)
      (hc : HasType S Γ (.snoc β B) c C) :
      Equiv S Γ β (.let₁ (.let₁ a b) c)
        (.let₁ a (.let₁ b (Tm.underBinder c))) C
  | bindLetPair (he : HasType S Γ β e (TypeFormers.tensor A B))
      (hc : HasType S Γ (.snoc (.snoc β A) B) c C)
      (hd : HasType S Γ (.snoc β C) d D) :
      Equiv S Γ β (.let₁ (.let₂ e c) d)
        (.let₂ e (.let₁ c (Tm.underBinder (Tm.underBinder d)))) D
  | bindLetCase (he : HasType S Γ β e (TypeFormers.coprod A B))
      (hl : HasType S Γ (.snoc β A) l C)
      (hr : HasType S Γ (.snoc β B) r C)
      (hd : HasType S Γ (.snoc β C) d D) :
      Equiv S Γ β (.let₁ (.case e l r) d)
        (.case e (.let₁ l (Tm.underBinder d)) (.let₁ r (Tm.underBinder d))) D
  | bindPair {n : Nat} {β : BoundCtx τ n} {a : Tm ν S.Instr n}
      {c : Tm ν S.Instr (n + 2)} (ha : HasType S Γ β a (TypeFormers.tensor A B))
      (hc : HasType S Γ (.snoc (.snoc β A) B) c C) :
      Equiv S Γ β (.let₂ a c)
        (.let₁ a (.let₂ (.bv 0) (Tm.underTwoBinders c))) C
  | bindCase {n : Nat} {β : BoundCtx τ n} {e : Tm ν S.Instr n}
      {l r : Tm ν S.Instr (n + 1)} (he : HasType S Γ β e (TypeFormers.coprod A B))
      (hl : HasType S Γ (.snoc β A) l C)
      (hr : HasType S Γ (.snoc β B) r C) :
      Equiv S Γ β (.case e l r)
        (.let₁ e (.case (.bv 0) (Tm.underBinder l) (Tm.underBinder r))) C
  | emptyInitial (ha : HasType S Γ β a TypeFormers.empty)
      (hb : HasType S Γ (.snoc β A) b B)
      (hc : HasType S Γ (.snoc β A) c B) :
      Equiv S Γ β (.let₁ (.abort a) b) (.let₁ (.abort a) c) B

  | iterFixpoint {n : Nat} {β : BoundCtx τ n} {a : Tm ν S.Instr n}
      {b : Tm ν S.Instr (n + 1)} (ha : HasType S Γ β a A)
      (hb : HasType S Γ (.snoc β A) b (TypeFormers.coprod B A)) :
      Equiv S Γ β (.iter a b)
        (.let₁ a (.case b (.bv 0)
          (.iter (.bv 0) (Tm.underBinder (Tm.underBinder b))))) B
  | iterNaturality {n : Nat} {β : BoundCtx τ n} {a : Tm ν S.Instr n}
      {b c : Tm ν S.Instr (n + 1)} (ha : HasType S Γ β a A)
      (hb : HasType S Γ (.snoc β A) b (TypeFormers.coprod B A))
      (hc : HasType S Γ (.snoc β B) c C) :
      Equiv S Γ β (.let₁ (.iter a b) c)
        (.iter a (.case b (.inl (Tm.underBinder c)) (.inr (.bv 0)))) C
  | iterCodiagonal {n : Nat} {β : BoundCtx τ n} {a : Tm ν S.Instr n}
      {b : Tm ν S.Instr (n + 1)} (ha : HasType S Γ β a A)
      (hb : HasType S Γ (.snoc β A) b
        (TypeFormers.coprod (TypeFormers.coprod B A) A)) :
      Equiv S Γ β (.iter a (.iter (.bv 0) (Tm.underBinder b)))
        (.iter a (.case b (.bv 0) (.inr (.bv 0)))) B
  | iterUniformity {n : Nat} {β : BoundCtx τ n} {a : Tm ν S.Instr n}
      {h b b' : Tm ν S.Instr (n + 1)} (ha : HasType S Γ β a A)
      (hh : HasType S Γ (.snoc β A) h A') (hp : Pure S h)
      (hb : HasType S Γ (.snoc β A) b (TypeFormers.coprod B A))
      (hb' : HasType S Γ (.snoc β A') b' (TypeFormers.coprod B A'))
      (square : Equiv S Γ (.snoc β A)
        (.case b (.inl (.bv 0)) (.inr (Tm.underBinder h)))
        (Tm.instantiate (Tm.underBinder b') h) (TypeFormers.coprod B A')) :
      Equiv S Γ β (.iter a b) (.iter (.let₁ a h) b') B

  /-- Float a loop's initial value into an explicit binding. -/
  | iterBind {n : Nat} {β : BoundCtx τ n} {a : Tm ν S.Instr n}
      {b : Tm ν S.Instr (n + 1)} (ha : HasType S Γ β a A)
      (hb : HasType S Γ (.snoc β A) b (TypeFormers.coprod B A)) :
      Equiv S Γ β (.iter a b) (.let₁ a (.iter (.bv 0) (Tm.underBinder b))) B

namespace Eqv

variable {Γ' : LambdaIter.Ctx ν τ} {β' : BoundCtx τ n}

private def weakenSame (wΓ : FreeWk Γ' Γ) :
    {n : Nat} → {β β' : BoundCtx τ n} → BoundCtx.Wk β' β →
    {a b : Tm ν S.Instr n} → {A : τ} →
      Isotope.LambdaIter.LocallyNameless.Equiv S Γ β a b A →
      Isotope.LambdaIter.LocallyNameless.Equiv S Γ' β' a b A
  | _, _, _, wβ, _, _, _, .var h =>
      let ⟨B, hB, hBA⟩ := wΓ.lookup _ _ h
      .sub (.var hB) hBA
  | _, _, _, wβ, _, _, _, .bvar => .sub .bvar (wβ.at _)
  | _, _, _, wβ, _, _, _, .symm h => .symm (weakenSame wΓ wβ h)
  | _, _, _, wβ, _, _, _, .trans h k => .trans (weakenSame wΓ wβ h) (weakenSame wΓ wβ k)
  | _, _, _, wβ, _, _, _, .sub h hAB => .sub (weakenSame wΓ wβ h) hAB
  | _, _, _, wβ, _, _, _, .op hf h => .op hf (weakenSame wΓ wβ h)
  | _, _, _, wβ, _, _, _, .let₁ ha hb => .let₁ (weakenSame wΓ wβ ha)
      (weakenSame wΓ (.snoc wβ (Subty.refl _)) hb)
  | _, _, _, _, _, _, _, .unit => .unit
  | _, _, _, wβ, _, _, _, .pair ha hb => .pair (weakenSame wΓ wβ ha) (weakenSame wΓ wβ hb)
  | _, _, _, wβ, _, _, _, .let₂ ha hc => .let₂ (weakenSame wΓ wβ ha)
      (weakenSame wΓ (.snoc (.snoc wβ (Subty.refl _)) (Subty.refl _)) hc)
  | _, _, _, wβ, _, _, _, .inl h => .inl (weakenSame wΓ wβ h)
  | _, _, _, wβ, _, _, _, .inr h => .inr (weakenSame wΓ wβ h)
  | _, _, _, wβ, _, _, _, .case he hl hr => .case (weakenSame wΓ wβ he)
      (weakenSame wΓ (.snoc wβ (Subty.refl _)) hl)
      (weakenSame wΓ (.snoc wβ (Subty.refl _)) hr)
  | _, _, _, wβ, _, _, _, .abort h => .abort (weakenSame wΓ wβ h)
  | _, _, _, wβ, _, _, _, .iter ha hb => .iter (weakenSame wΓ wβ ha)
      (weakenSame wΓ (.snoc wβ (Subty.refl _)) hb)
  | _, _, _, wβ, _, _, _, .letBeta hp ha hb => .letBeta hp
      (HasType.weaken wΓ wβ (Subty.refl _) ha)
      (HasType.weaken wΓ (.snoc wβ (Subty.refl _)) (Subty.refl _) hb)
  | _, _, _, wβ, _, _, _, .letEta ha => .letEta (HasType.weaken wΓ wβ (Subty.refl _) ha)
  | _, _, _, wβ, _, _, _, .unitEta ha => .unitEta (HasType.weaken wΓ wβ (Subty.refl _) ha)
  | _, _, _, wβ, _, _, _, .pairBeta ha hb hc => .pairBeta
      (HasType.weaken wΓ wβ (Subty.refl _) ha)
      (HasType.weaken wΓ wβ (Subty.refl _) hb)
      (HasType.weaken wΓ (.snoc (.snoc wβ (Subty.refl _)) (Subty.refl _)) (Subty.refl _) hc)
  | _, _, _, wβ, _, _, _, .pairEta ha => .pairEta (HasType.weaken wΓ wβ (Subty.refl _) ha)
  | _, _, _, wβ, _, _, _, .caseBetaL he hl hr => .caseBetaL
      (HasType.weaken wΓ wβ (Subty.refl _) he)
      (HasType.weaken wΓ (.snoc wβ (Subty.refl _)) (Subty.refl _) hl)
      (HasType.weaken wΓ (.snoc wβ (Subty.refl _)) (Subty.refl _) hr)
  | _, _, _, wβ, _, _, _, .caseBetaR he hl hr => .caseBetaR
      (HasType.weaken wΓ wβ (Subty.refl _) he)
      (HasType.weaken wΓ (.snoc wβ (Subty.refl _)) (Subty.refl _) hl)
      (HasType.weaken wΓ (.snoc wβ (Subty.refl _)) (Subty.refl _) hr)
  | _, _, _, wβ, _, _, _, .caseEta he => .caseEta (HasType.weaken wΓ wβ (Subty.refl _) he)
  | _, _, _, wβ, _, _, _, .bindOp hf ha hc => .bindOp hf
      (HasType.weaken wΓ wβ (Subty.refl _) ha)
      (HasType.weaken wΓ (.snoc wβ (Subty.refl _)) (Subty.refl _) hc)
  | _, _, _, wβ, _, _, _, .bindLet ha hb hc => .bindLet
      (HasType.weaken wΓ wβ (Subty.refl _) ha)
      (HasType.weaken wΓ (.snoc wβ (Subty.refl _)) (Subty.refl _) hb)
      (HasType.weaken wΓ (.snoc wβ (Subty.refl _)) (Subty.refl _) hc)
  | _, _, _, wβ, _, _, _, .bindLetPair he hc hd => .bindLetPair
      (HasType.weaken wΓ wβ (Subty.refl _) he)
      (HasType.weaken wΓ (.snoc (.snoc wβ (Subty.refl _)) (Subty.refl _)) (Subty.refl _) hc)
      (HasType.weaken wΓ (.snoc wβ (Subty.refl _)) (Subty.refl _) hd)
  | _, _, _, wβ, _, _, _, .bindLetCase he hl hr hd => .bindLetCase
      (HasType.weaken wΓ wβ (Subty.refl _) he)
      (HasType.weaken wΓ (.snoc wβ (Subty.refl _)) (Subty.refl _) hl)
      (HasType.weaken wΓ (.snoc wβ (Subty.refl _)) (Subty.refl _) hr)
      (HasType.weaken wΓ (.snoc wβ (Subty.refl _)) (Subty.refl _) hd)
  | _, _, _, wβ, _, _, _, .bindPair ha hc => .bindPair
      (HasType.weaken wΓ wβ (Subty.refl _) ha)
      (HasType.weaken wΓ (.snoc (.snoc wβ (Subty.refl _)) (Subty.refl _)) (Subty.refl _) hc)
  | _, _, _, wβ, _, _, _, .bindCase he hl hr => .bindCase
      (HasType.weaken wΓ wβ (Subty.refl _) he)
      (HasType.weaken wΓ (.snoc wβ (Subty.refl _)) (Subty.refl _) hl)
      (HasType.weaken wΓ (.snoc wβ (Subty.refl _)) (Subty.refl _) hr)
  | _, _, _, wβ, _, _, _, .emptyInitial ha hb hc => .emptyInitial
      (HasType.weaken wΓ wβ (Subty.refl _) ha)
      (HasType.weaken wΓ (.snoc wβ (Subty.refl _)) (Subty.refl _) hb)
      (HasType.weaken wΓ (.snoc wβ (Subty.refl _)) (Subty.refl _) hc)
  | _, _, _, wβ, _, _, _, .iterFixpoint ha hb => .iterFixpoint
      (HasType.weaken wΓ wβ (Subty.refl _) ha)
      (HasType.weaken wΓ (.snoc wβ (Subty.refl _)) (Subty.refl _) hb)
  | _, _, _, wβ, _, _, _, .iterNaturality ha hb hc => .iterNaturality
      (HasType.weaken wΓ wβ (Subty.refl _) ha)
      (HasType.weaken wΓ (.snoc wβ (Subty.refl _)) (Subty.refl _) hb)
      (HasType.weaken wΓ (.snoc wβ (Subty.refl _)) (Subty.refl _) hc)
  | _, _, _, wβ, _, _, _, .iterCodiagonal ha hb => .iterCodiagonal
      (HasType.weaken wΓ wβ (Subty.refl _) ha)
      (HasType.weaken wΓ (.snoc wβ (Subty.refl _)) (Subty.refl _) hb)
  | _, _, _, wβ, _, _, _, .iterUniformity ha hh hp hb hb' square => .iterUniformity
      (HasType.weaken wΓ wβ (Subty.refl _) ha)
      (HasType.weaken wΓ (.snoc wβ (Subty.refl _)) (Subty.refl _) hh) hp
      (HasType.weaken wΓ (.snoc wβ (Subty.refl _)) (Subty.refl _) hb)
      (HasType.weaken wΓ (.snoc wβ (Subty.refl _)) (Subty.refl _) hb')
      (weakenSame wΓ (.snoc wβ (Subty.refl _)) square)
  | _, _, _, wβ, _, _, _, .iterBind ha hb => .iterBind
      (HasType.weaken wΓ wβ (Subty.refl _) ha)
      (HasType.weaken wΓ (.snoc wβ (Subty.refl _)) (Subty.refl _) hb)

/-- Proof-relevant equational weakening. -/
def weaken (wΓ : FreeWk Γ' Γ) (wβ : BoundCtx.Wk β' β) (hAB : Subty A B) :
    Isotope.LambdaIter.LocallyNameless.Equiv S Γ β a b A →
    Isotope.LambdaIter.LocallyNameless.Equiv S Γ' β' a b B :=
  fun h => .sub (weakenSame wΓ wβ h) hAB

/-- Proposition-truncated equational weakening. -/
theorem weaken_nonempty (wΓ : FreeWkProp Γ' Γ) (wβ : BoundCtx.WkProp β' β)
    (hAB : Nonempty (Subty A B))
    (h : Nonempty (Isotope.LambdaIter.LocallyNameless.Equiv S Γ β a b A)) :
    Nonempty (Isotope.LambdaIter.LocallyNameless.Equiv S Γ' β' a b B) :=
  wΓ.elim fun fΓ => wβ.elim fun fβ => hAB.elim fun fAB => h.elim fun he =>
    ⟨weaken fΓ fβ fAB he⟩

end Eqv

end Isotope.LambdaIter.LocallyNameless
