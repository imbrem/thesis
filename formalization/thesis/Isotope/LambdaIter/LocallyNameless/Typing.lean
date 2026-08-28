import Isotope.LambdaIter.LocallyNameless.Context

namespace Isotope.LambdaIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable {ν : Type w} [DecidableEq ν]

/-- Contravariant source and covariant target instruction typing. -/
structure InstTy (S : Signature τ) (f : S.Instr) (A B : τ) : Type u where
  input : Subty A (S.src f)
  output : Subty (S.trg f) B

/-- Syntax-directed typing over a shared free context and an anonymous snoc
bound context. Derivations retain subtyping evidence in `Type`. -/
inductive HasType (S : Signature.{u, q} τ) (Γ : LambdaIter.Ctx ν τ) :
    {n : Nat} → BoundCtx τ n → Tm ν S.Instr n → τ → Type (max u q w) where
  | fv (h : Γ.lookup x = some A) : HasType S Γ β (.fv x) A
  | bv : HasType S Γ β (.bv ι) (β.get ι)
  | op (hf : InstTy S f A B) (ha : HasType S Γ β a A) : HasType S Γ β (.op f a) B
  | let₁ (ha : HasType S Γ β a A)
      (hb : HasType S Γ (.snoc β A) b B) : HasType S Γ β (.let₁ a b) B
  | unit : HasType S Γ β .unit LambdaIter.unit
  | pair (ha : HasType S Γ β a A) (hb : HasType S Γ β b B) :
      HasType S Γ β (.pair a b) (LambdaIter.tensor A B)
  | let₂ (ha : HasType S Γ β a (LambdaIter.tensor A B))
      (hc : HasType S Γ (.snoc (.snoc β A) B) c C) : HasType S Γ β (.let₂ a c) C
  | inl (ha : HasType S Γ β a A) : HasType S Γ β (.inl a) (LambdaIter.coprod A B)
  | inr (hb : HasType S Γ β b B) : HasType S Γ β (.inr b) (LambdaIter.coprod A B)
  | case (he : HasType S Γ β e (LambdaIter.coprod A B))
      (hl : HasType S Γ (.snoc β A) l C)
      (hr : HasType S Γ (.snoc β B) r C) : HasType S Γ β (.case e l r) C
  | abort (ha : HasType S Γ β a LambdaIter.empty) : HasType S Γ β (.abort a) C
  | iter (ha : HasType S Γ β a A)
      (hb : HasType S Γ (.snoc β A) b (LambdaIter.coprod B A)) :
      HasType S Γ β (.iter a b) B
  | sub (ha : HasType S Γ β a A) (hAB : Subty A B) : HasType S Γ β a B

namespace HasType

variable {S : Signature.{u, q} τ} {Γ Γ' : LambdaIter.Ctx ν τ} {β β' : BoundCtx τ n}
  {t : Tm ν S.Instr n} {A B : τ}

private def weakenSame [DecidableEq ν] (wΓ : FreeWk Γ' Γ) :
    {n : Nat} → {β β' : BoundCtx τ n} → BoundCtx.Wk β' β →
    {t : Tm ν S.Instr n} → {A : τ} → HasType S Γ β t A → HasType S Γ' β' t A
  | _, _, _, wβ, _, _, .fv h =>
      let ⟨B, hB, hBA⟩ := wΓ.lookup _ _ h
      .sub (.fv hB) hBA
  | _, _, _, wβ, _, _, .bv => .sub .bv (wβ.at _)
  | _, _, _, wβ, _, _, .op hf ha => .op hf (weakenSame wΓ wβ ha)
  | _, _, _, wβ, _, _, .let₁ ha hb => .let₁ (weakenSame wΓ wβ ha)
      (weakenSame wΓ (.snoc wβ (Subty.refl _)) hb)
  | _, _, _, _, _, _, .unit => .unit
  | _, _, _, wβ, _, _, .pair ha hb => .pair (weakenSame wΓ wβ ha) (weakenSame wΓ wβ hb)
  | _, _, _, wβ, _, _, .let₂ ha hc => .let₂ (weakenSame wΓ wβ ha)
      (weakenSame wΓ (.snoc (.snoc wβ (Subty.refl _)) (Subty.refl _)) hc)
  | _, _, _, wβ, _, _, .inl ha => .inl (weakenSame wΓ wβ ha)
  | _, _, _, wβ, _, _, .inr hb => .inr (weakenSame wΓ wβ hb)
  | _, _, _, wβ, _, _, .case he hl hr => .case (weakenSame wΓ wβ he)
      (weakenSame wΓ (.snoc wβ (Subty.refl _)) hl)
      (weakenSame wΓ (.snoc wβ (Subty.refl _)) hr)
  | _, _, _, wβ, _, _, .abort ha => .abort (weakenSame wΓ wβ ha)
  | _, _, _, wβ, _, _, .iter ha hb => .iter (weakenSame wΓ wβ ha)
      (weakenSame wΓ (.snoc wβ (Subty.refl _)) hb)
  | _, _, _, wβ, _, _, .sub ha hAB => .sub (weakenSame wΓ wβ ha) hAB

/-- Proof-relevant weakening, with a separately supplied result coercion. -/
def weaken [DecidableEq ν] (wΓ : FreeWk Γ' Γ) (wβ : BoundCtx.Wk β' β)
    (hAB : Subty A B) : HasType S Γ β t A → HasType S Γ' β' t B :=
  fun h => .sub (weakenSame wΓ wβ h) hAB

/-- Proposition-truncated existence of a weakened typing derivation. -/
theorem weaken_nonempty [DecidableEq ν] (wΓ : FreeWkProp Γ' Γ)
    (wβ : BoundCtx.WkProp β' β) (hAB : Nonempty (Subty A B))
    (h : Nonempty (HasType S Γ β t A)) : Nonempty (HasType S Γ' β' t B) :=
  wΓ.elim fun fΓ => wβ.elim fun fβ => hAB.elim fun fAB => h.elim fun ht =>
    ⟨weaken fΓ fβ fAB ht⟩

end HasType

inductive Pure (S : Signature τ) : {n : Nat} → Tm ν S.Instr n → Prop where
  | fv : Pure S (.fv x)
  | bv : Pure S (.bv ι)
  | op (hf : S.IsPure f) (ha : Pure S a) : Pure S (.op f a)
  | let₁ : Pure S a → Pure S b → Pure S (.let₁ a b)
  | unit : Pure S .unit
  | pair : Pure S a → Pure S b → Pure S (.pair a b)
  | let₂ : Pure S a → Pure S b → Pure S (.let₂ a b)
  | inl : Pure S a → Pure S (.inl a)
  | inr : Pure S a → Pure S (.inr a)
  | case : Pure S e → Pure S l → Pure S r → Pure S (.case e l r)
  | abort : Pure S a → Pure S (.abort a)
  | iter : Pure S a → Pure S b → Pure S (.iter a b)

end Isotope.LambdaIter.LocallyNameless
